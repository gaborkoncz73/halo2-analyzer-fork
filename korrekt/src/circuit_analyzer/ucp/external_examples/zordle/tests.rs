//! A hivatalos jatekmenetekre futtatja a visszaallitast, es szotarbejarassal veti ossze az eredmenyt.
//! A referencia csak a futas utan ellenorzes; a recovery sem a tanut, sem a referenciat nem kapja meg.

use super::{
    compat::{dev::MockProver, pasta::Fp, plonk::Assigned},
    wordle::{
        dict::get_dict,
        utils::{word_to_chars, word_to_polyhash, BASE, WORD_COUNT, WORD_LEN},
        WordleCircuit,
    },
};
use crate::{
    circuit_analyzer::{
        analyzable::Analyzable,
        halo2_proofs_libs::{Any, Value},
        ucp::{
            cell::CellId,
            extractor::extract_ucp_problem_with_targets,
            privacy::{
                analyze_private_recoverability_with_witness, PrivacyAnalysisProfile,
                PrivacyAnalysisReport, PrivateCellUniqueness,
            },
            value::{normalize_field_value, UcpValueDomain},
        },
    },
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
};
use num_bigint::BigInt;
use std::collections::{BTreeSet, HashMap};

const K: u32 = 14;
type Letters = [u64; WORD_LEN];

#[derive(Clone, Copy)]
struct Game {
    name: &'static str,
    guesses: [&'static str; WORD_COUNT],
    answer: &'static str,
}

// Az elso jatekmenet a Zordle sajat tesztjenek szavait hasznalja.
const UPSTREAM_GAME: Game = Game {
    name: "upstream",
    guesses: ["audio", "hunky", "funky", "fluff", "fluff", "fluff"],
    answer: "fluff",
};
const VARIED_GAME: Game = Game {
    name: "varied",
    guesses: ["crane", "moist", "night", "might", "light", "light"],
    answer: "light",
};

fn letters(word: &str) -> Letters {
    word_to_chars(word).try_into().unwrap()
}

// A szotar polinomhasit a kapu szerinti karakterekre bontja; a 0 az upstream ures sora.
fn decode(hash: u64) -> Letters {
    let mut value = hash;
    let mut out = [0; WORD_LEN];
    for index in (0..WORD_LEN).rev() {
        out[index] = value % BASE;
        value /= BASE;
    }
    assert_eq!(value, 0);
    out
}

fn pattern(guess: &Letters, answer: &Letters) -> ([u64; WORD_LEN], [u64; WORD_LEN]) {
    let mut green = [0; WORD_LEN];
    let mut yellow = [0; WORD_LEN];
    for index in 0..WORD_LEN {
        green[index] = u64::from(guess[index] == answer[index]);
        yellow[index] = u64::from(answer.contains(&guess[index]));
    }
    (green, yellow)
}

fn dictionary() -> Vec<Letters> {
    let mut hashes: Vec<u64> = get_dict().into_iter().map(u64::from).collect();
    hashes.push(0);
    hashes.into_iter().map(decode).collect()
}

fn circuit_for(guesses: &[Letters; WORD_COUNT], answer: &Letters) -> WordleCircuit<Fp> {
    let assigned = |value: Fp| -> Value<Assigned<Fp>> { Value::known(value.into()) };
    let poly_words: [Value<Assigned<Fp>>; WORD_COUNT] = std::array::from_fn(|idx| {
        let hash = guesses[idx]
            .iter()
            .fold(0, |hash, letter| hash * BASE + letter);
        assigned(Fp::from(hash))
    });
    let word_chars =
        std::array::from_fn(|idx| std::array::from_fn(|i| assigned(Fp::from(guesses[idx][i]))));
    let word_diffs_green = std::array::from_fn(|idx| {
        std::array::from_fn(|i| Value::known(Fp::from(guesses[idx][i]) - Fp::from(answer[i])))
    });
    let word_diffs_yellow = std::array::from_fn(|idx| {
        std::array::from_fn(|i| {
            Value::known(answer.iter().fold(Fp::from(1), |product, letter| {
                product * (Fp::from(guesses[idx][i]) - Fp::from(*letter))
            }))
        })
    });
    WordleCircuit {
        poly_words,
        word_chars,
        word_diffs_green,
        word_diffs_yellow,
    }
}

fn game_letters(game: &Game) -> ([Letters; WORD_COUNT], Letters) {
    (
        std::array::from_fn(|idx| letters(game.guesses[idx])),
        letters(game.answer),
    )
}

fn public_rows(guesses: &[Letters; WORD_COUNT], answer: &Letters) -> Vec<Vec<u64>> {
    let mut green = Vec::new();
    let mut yellow = Vec::new();
    for guess in guesses {
        let (g, y) = pattern(guess, answer);
        green.extend(g);
        yellow.extend(y);
    }
    vec![answer.to_vec(), green, yellow]
}

fn observations(rows: &[Vec<u64>]) -> AnalyzerInput {
    let mut cells = HashMap::new();
    for (column, values) in rows.iter().enumerate() {
        for (row, value) in values.iter().enumerate() {
            cells.insert(format!("I-{column}-{row}"), BigInt::from(*value));
        }
    }
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput {
            instance_cells: cells,
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

// A tippek betucellait a regioszerkezetbol valasztja ki, tanuertek olvasasa nelkul.
fn guess_targets(circuit: &WordleCircuit<Fp>) -> Vec<Vec<CellId>> {
    let analyzable = Analyzable::<Fp>::config_and_synthesize(circuit, K).unwrap();
    let mut words = Vec::new();
    for region in analyzable
        .regions
        .iter()
        .filter(|region| region.name.contains("one word checks"))
    {
        let first_row = region
            .cells
            .iter()
            .filter(|(column, _)| matches!(column.column_type(), Any::Advice))
            .map(|(_, row)| *row)
            .min()
            .unwrap();
        words.push(
            (1..=WORD_LEN)
                .map(|column| CellId::advice(column, i32::try_from(first_row).unwrap()))
                .collect::<Vec<_>>(),
        );
    }
    assert_eq!(words.len(), WORD_COUNT, "Upstream region layout changed");
    words
}

// A referencia: a szotar osszes szava, amelyre a publikus szinminta pontosan teljesul.
fn reference(rows: &[Vec<u64>]) -> Vec<Vec<Letters>> {
    let answer: Letters = rows[0].clone().try_into().unwrap();
    let dictionary = dictionary();
    (0..WORD_COUNT)
        .map(|idx| {
            let green = &rows[1][idx * WORD_LEN..(idx + 1) * WORD_LEN];
            let yellow = &rows[2][idx * WORD_LEN..(idx + 1) * WORD_LEN];
            dictionary
                .iter()
                .filter(|word| {
                    let (g, y) = pattern(word, &answer);
                    g.as_slice() == green && y.as_slice() == yellow
                })
                .copied()
                .collect()
        })
        .collect()
}

fn canonical(value: u64) -> BigInt {
    normalize_field_value(
        BigInt::from(value),
        &crate::circuit_analyzer::ucp::extractor::field_modulus::<Fp>(),
    )
    .unwrap()
}

fn domain_values(domain: &UcpValueDomain) -> BTreeSet<BigInt> {
    match domain {
        UcpValueDomain::Exact(value) => [value.clone()].into(),
        UcpValueDomain::FiniteSet(values) => values.clone(),
    }
}

fn word_text(word: &Letters) -> String {
    word.iter()
        .map(|letter| match letter {
            0 => '_',
            value => char::from(b'a' + u8::try_from(value - 1).unwrap()),
        })
        .collect()
}

fn print_reference(game: &Game, candidates: &[Vec<Letters>]) {
    println!("Zordle game {} (answer {}):", game.name, game.answer);
    for (idx, words) in candidates.iter().enumerate() {
        let preview: Vec<_> = words.iter().take(6).map(word_text).collect();
        println!(
            "  guess {} = {}: {} dictionary candidates {:?}",
            idx,
            game.guesses[idx],
            words.len(),
            preview
        );
    }
}

#[test]
fn zordle_upstream_word_helpers_match_the_dictionary_decoding() {
    let dict: BTreeSet<_> = get_dict().into_iter().map(u64::from).collect();
    for game in [UPSTREAM_GAME, VARIED_GAME] {
        for word in game.guesses {
            let hash = word_to_polyhash(word);
            assert!(
                dict.contains(&hash),
                "{word} missing from the upstream dictionary"
            );
            assert_eq!(decode(hash), letters(word));
        }
    }
}

#[test]
fn zordle_mock_prover_accepts_games_and_rejects_changed_colors() {
    for game in [UPSTREAM_GAME, VARIED_GAME] {
        let (guesses, answer) = game_letters(&game);
        let circuit = circuit_for(&guesses, &answer);
        let rows = public_rows(&guesses, &answer);
        let instance = |rows: &[Vec<u64>]| -> Vec<Vec<Fp>> {
            rows.iter()
                .map(|row| row.iter().copied().map(Fp::from).collect())
                .collect()
        };
        MockProver::run(K, &circuit, instance(&rows))
            .unwrap()
            .assert_satisfied();
        let mut changed = rows.clone();
        changed[1][0] = 1 - changed[1][0];
        assert!(MockProver::run(K, &circuit, instance(&changed))
            .unwrap()
            .verify()
            .is_err());
        print_reference(&game, &reference(&rows));
    }
}

// A kenyszerek kovetkezmenye SMT nelkul: csak a publikus adatot es a kapukat kapja meg.
#[test]
fn zordle_ucp_fixpoint_matches_the_reference_without_solver() {
    for game in [UPSTREAM_GAME, VARIED_GAME] {
        let (guesses, answer) = game_letters(&game);
        let circuit = circuit_for(&guesses, &answer);
        let rows = public_rows(&guesses, &answer);
        let input = observations(&rows);
        let targets = guess_targets(&circuit);
        let analyzable = Analyzable::<Fp>::config_and_synthesize(&circuit, K).unwrap();
        let problem = extract_ucp_problem_with_targets(&analyzable, targets.concat());
        println!(
            "Zordle extraction: {} expressions, {} lookups",
            problem.expressions.len(),
            problem.lookups.len()
        );
        let mut values = problem.initial_value_facts.clone();
        for (name, value) in &input.verification_input.instance_cells {
            let cell = crate::circuit_analyzer::ucp::value::parse_cell_id(name).unwrap();
            values.mark_known(
                cell,
                normalize_field_value(value.clone(), &problem.field_modulus).unwrap(),
            );
        }
        let started = std::time::Instant::now();
        let result = problem.analyze_with_values(problem.initial_facts.clone(), values);
        println!(
            "Zordle UCP fixpoint ({}): {:?}",
            game.name,
            started.elapsed()
        );
        let candidates = reference(&rows);
        print_reference(&game, &candidates);
        for (idx, word) in targets.iter().enumerate() {
            let mut line = Vec::new();
            for (position, cell) in word.iter().enumerate() {
                let feasible: BTreeSet<_> = candidates[idx]
                    .iter()
                    .map(|candidate| canonical(candidate[position]))
                    .collect();
                let domain = result.value_facts.domain(cell);
                if let Some(domain) = domain {
                    let values = domain_values(domain);
                    assert!(
                        feasible.is_subset(&values),
                        "UCP domain excludes a dictionary word at guess {idx} position {position}"
                    );
                    // A kapuk es a szotar egyuttes kovetkezmenye SMT nelkul pontosan a referencia.
                    assert_eq!(
                        values, feasible,
                        "UCP domain differs from the reference at guess {idx} position {position}"
                    );
                    line.push(values.len().to_string());
                } else {
                    line.push("-".into());
                }
            }
            println!("  UCP domain sizes guess {idx}: {line:?}");
        }
    }
}

fn check_against_reference(
    report: &PrivacyAnalysisReport,
    targets: &[Vec<CellId>],
    candidates: &[Vec<Letters>],
) -> (usize, usize, usize) {
    let mut exact_match = 0;
    let mut narrower_than_reference = 0;
    let mut complete_equal = 0;
    for (idx, word) in targets.iter().enumerate() {
        for (position, cell) in word.iter().enumerate() {
            let feasible: BTreeSet<_> = candidates[idx]
                .iter()
                .map(|candidate| canonical(candidate[position]))
                .collect();
            let entry = report
                .cells
                .iter()
                .find(|entry| &entry.cell == cell)
                .unwrap();
            if let Some(domain) = &entry.domain {
                let values = domain_values(domain);
                assert!(
                    feasible.is_subset(&values),
                    "Reported domain excludes a feasible letter at guess {idx} position {position}"
                );
                if entry.domain_is_complete {
                    assert_eq!(values, feasible, "Complete domain differs from reference");
                    complete_equal += 1;
                }
                if matches!(domain, UcpValueDomain::Exact(_)) {
                    assert_eq!(feasible.len(), 1);
                    exact_match += 1;
                }
                narrower_than_reference += usize::from(values == feasible);
            }
            match entry.uniqueness {
                PrivateCellUniqueness::Unique => assert_eq!(feasible.len(), 1),
                PrivateCellUniqueness::NonUnique => assert!(feasible.len() >= 2),
                PrivateCellUniqueness::Unknown => {}
            }
        }
    }
    (exact_match, narrower_than_reference, complete_equal)
}

fn run_recovery(game: Game) {
    let (guesses, answer) = game_letters(&game);
    let circuit = circuit_for(&guesses, &answer);
    let rows = public_rows(&guesses, &answer);
    let input = observations(&rows);
    let targets = guess_targets(&circuit);
    let candidates = reference(&rows);
    print_reference(&game, &candidates);
    let options = crate::circuit_analyzer::ucp::thesis_examples::recovery_options()
        .with_profile(PrivacyAnalysisProfile::Standard);
    let started = std::time::Instant::now();
    let report = analyze_private_recoverability_with_witness::<Fp, _, _>(
        &circuit,
        K,
        &input,
        targets.concat(),
        options,
    )
    .unwrap();
    println!(
        "Zordle recovery {} finished in {:?}",
        game.name,
        started.elapsed()
    );
    let names: HashMap<CellId, String> = targets
        .iter()
        .enumerate()
        .flat_map(|(idx, word)| {
            word.iter()
                .enumerate()
                .map(move |(position, cell)| (cell.clone(), format!("g{idx}[{position}]")))
        })
        .collect();
    println!(
        "{}",
        report.phase_report_with_names(|cell| names.get(cell).cloned())
    );
    let (exact, equal, complete) = check_against_reference(&report, &targets, &candidates);
    println!(
        "Zordle {}: exact={exact}, domain equals reference={equal}, complete={complete}, of {} letters",
        game.name,
        WORD_COUNT * WORD_LEN
    );
}

#[test]
#[ignore = "Teljes UCP-SMT visszaallitas; futtatas: cargo test --release --lib zordle_recovery -- --ignored --nocapture --test-threads=1"]
fn zordle_recovery_upstream_game() {
    run_recovery(UPSTREAM_GAME);
}

#[test]
#[ignore = "Teljes UCP-SMT visszaallitas; futtatas: cargo test --release --lib zordle_recovery -- --ignored --nocapture --test-threads=1"]
fn zordle_recovery_varied_game() {
    run_recovery(VARIED_GAME);
}

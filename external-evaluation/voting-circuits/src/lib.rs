//! A valtozatlanul importalt kulso szavazasi circuitet ellenorzi es elemzi.

#[cfg(test)]
mod tests {
    use group::{Curve, Group};
    use halo2_poseidon::{ConstantLength, Hash, P128Pow5T3};
    use korrekt::{
        circuit_analyzer::{
            analyzable::Analyzable,
            halo2_proofs_libs::{Any, Circuit, Fr, MockProver, PrimeField, Region},
            ucp::{
                cell::CellId,
                extractor::extract_ucp_problem,
                privacy::{
                    analyze_private_recoverability_with_witness, PrivacyAnalysisOptions,
                    PrivacyAnalysisStatus, SatisfiabilityEvidence,
                },
                value::UcpValueDomain,
            },
        },
        io::analyzer_io_type::{
            AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod,
        },
    };
    use num_bigint::{BigInt, Sign};
    use pasta_curves::{arithmetic::CurveAffine, pallas};
    use std::{collections::BTreeSet, time::Instant};
    use voting_circuits::{
        share_reveal::{build_share_reveal, Circuit as ShareRevealCircuit, ShareRevealBundle, K},
        VOTE_COMM_TREE_DEPTH,
    };

    struct Fixture {
        bundle: ShareRevealBundle,
        private_values: Vec<(String, Fr)>,
    }

    // A Pasta test little-endian kanonikus reprezentaciojat egesz szamma alakitja.
    fn field_to_bigint(value: &Fr) -> BigInt {
        BigInt::from_bytes_le(Sign::Plus, value.to_repr().as_ref())
    }

    // A nativ gorbe- es hash-muveletekkel csak ervenyes tesztadatot keszit, nem circuitet ir ujra.
    // Az adatok egy onallo ShareReveal allitast adnak, nem a teljes szavazasi protokoll futasat.
    fn fixture(seed: u64) -> Fixture {
        let generator = pallas::Point::generator();
        let recipient = generator * pallas::Scalar::from(42);
        let blinds: [Fr; 16] = std::array::from_fn(|i| Fr::from(1001 + seed * 100 + i as u64));
        let coordinates: [[Fr; 4]; 16] = std::array::from_fn(|i| {
            let randomness = pallas::Scalar::from((i as u64 + 1) * 101 + seed * 2000);
            let c1 = (generator * randomness).to_affine();
            let c2 =
                (generator * pallas::Scalar::from(625 + seed) + recipient * randomness).to_affine();
            let a = c1.coordinates().unwrap();
            let b = c2.coordinates().unwrap();
            [*a.x(), *b.x(), *a.y(), *b.y()]
        });
        let commitments: [Fr; 16] = std::array::from_fn(|i| {
            Hash::<Fr, P128Pow5T3, ConstantLength<5>, 3, 2>::init().hash([
                blinds[i],
                coordinates[i][0],
                coordinates[i][1],
                coordinates[i][2],
                coordinates[i][3],
            ])
        });
        let index = (seed as usize + 2) % 16;
        let c = coordinates[index];
        let bundle = build_share_reveal(
            [Fr::from(0); VOTE_COMM_TREE_DEPTH],
            0,
            commitments,
            blinds[index],
            c[0],
            c[1],
            c[2],
            c[3],
            index as u32,
            Fr::from(3),
            Fr::from(1),
            Fr::from(999),
        );
        let mut private_values = vec![
            ("share_index".into(), Fr::from(index as u64)),
            ("primary_blind".into(), blinds[index]),
        ];
        private_values.extend(
            commitments
                .into_iter()
                .enumerate()
                .map(|(i, value)| (format!("share_comm[{i}]"), value)),
        );
        Fixture {
            bundle,
            private_values,
        }
    }

    fn single_advice(region: &Region) -> CellId {
        assert_eq!(region.cells.len(), 1, "Upstream single-cell layout changed");
        let (column, row) = region.cells[0];
        assert_eq!(column.column_type(), &Any::Advice);
        assert_eq!(column.index(), 0);
        CellId::advice(column.index(), i32::try_from(row).unwrap())
    }

    // A rogzitett kiadas szintezissorrendje alapjan azonosit, privat erteket nem olvas.
    // A V1 floor planner altal valasztott sorszamokat nem rogziti elore.
    fn private_targets(analyzable: &Analyzable<Fr>) -> Vec<CellId> {
        let regions = &analyzable.regions;
        assert!(regions.len() >= 22);
        for region in &regions[..3] {
            assert_eq!(region.name, "load private");
        }
        assert_eq!(regions[3].name, "copy proposal_id from instance");
        assert_eq!(regions[4].name, "copy vote_decision from instance");
        assert_eq!(regions[5].name, "copy voting_round_id from instance");
        for region in &regions[6..22] {
            assert_eq!(region.name, "load private");
        }
        let targets: Vec<_> = [1, 2]
            .into_iter()
            .chain(6..22)
            .map(|i| single_advice(&regions[i]))
            .collect();
        assert_eq!(targets.iter().collect::<BTreeSet<_>>().len(), 18);
        targets
    }

    fn observations(bundle: &ShareRevealBundle) -> AnalyzerInput {
        AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new(
                bundle
                    .instance
                    .to_halo2_instance()
                    .iter()
                    .enumerate()
                    .map(|(row, value)| (format!("I-0-{row}"), field_to_bigint(value))),
                1,
            ),
            lookup_method: LookupMethod::InlineConstraints,
        }
    }

    #[test]
    fn imported_share_reveal_is_valid_and_extractable() {
        fn accepts_analyzer_circuit<C: Circuit<Fr>>() {}
        accepts_analyzer_circuit::<ShareRevealCircuit>();
        for seed in [0, 1] {
            let data = fixture(seed);
            MockProver::run(
                K,
                &data.bundle.circuit,
                vec![data.bundle.instance.to_halo2_instance()],
            )
            .unwrap()
            .assert_satisfied();
            let analyzable =
                Analyzable::<Fr>::config_and_synthesize(&data.bundle.circuit, K).unwrap();
            let targets = private_targets(&analyzable);
            let problem = extract_ucp_problem(&analyzable);
            assert!(targets
                .iter()
                .all(|cell| problem.witness_cells.contains(cell)));
            println!(
                "voting-circuits 0.9.0 ShareReveal: k={K}; {} gate polynomials; {} extracted equations; {} advice cells; {} private targets; MockProver valid (seed={seed})",
                analyzable.cs.gates.iter().map(|gate| gate.polys.len()).sum::<usize>(),
                problem.expressions.len(), problem.witness_cells.len(), targets.len(),
            );
        }
    }

    #[test]
    fn imported_share_reveal_rejects_changed_public_input() {
        let data = fixture(0);
        let original = data.bundle.instance.to_halo2_instance();
        assert_eq!(original.len(), 9);
        for row in 0..original.len() {
            let mut public = original.clone();
            public[row] += Fr::from(1);
            assert!(
                MockProver::run(K, &data.bundle.circuit, vec![public])
                    .unwrap()
                    .verify()
                    .is_err(),
                "Changed public input {row} was accepted"
            );
        }
    }

    fn positive_env(name: &str, fallback: usize) -> usize {
        let value = std::env::var(name)
            .map(|value| value.parse().unwrap_or_else(|_| panic!("Invalid {name}")))
            .unwrap_or(fallback);
        assert!(value > 0, "{name} must be positive");
        value
    }

    #[test]
    #[ignore = "bounded external recovery measurement; run explicitly in release mode"]
    fn imported_share_reveal_standard_recovery() {
        let data = fixture(0);
        let analyzable = Analyzable::<Fr>::config_and_synthesize(&data.bundle.circuit, K).unwrap();
        let targets = private_targets(&analyzable);
        let mut options = PrivacyAnalysisOptions::default();
        // A pilotmeres mindharom keresest engedelyezi, kicsi es nyiltan kozolt osszesitett keretekkel.
        options.solver_timeout_ms = Some(positive_env("UCP_VOTING_TIMEOUT_MS", 1000) as u64);
        options.max_semantic_queries = positive_env("UCP_VOTING_SEMANTIC_QUERIES", 4);
        options.domain_refinement.max_solver_checks =
            positive_env("UCP_VOTING_REFINEMENT_CHECKS", 4);
        options.domain_discovery.max_solver_checks = positive_env("UCP_VOTING_DISCOVERY_CHECKS", 4);
        options.search.max_bridge_queries = 2;
        options.search.max_queries_without_progress = 4;
        options.search.max_retries_per_target = 0;
        options.search.retry_solver_timeout_ms = None;
        println!("voting-circuits 0.9.0 ShareReveal; Standard; options={options:?}");
        let started = Instant::now();
        let report = analyze_private_recoverability_with_witness(
            &data.bundle.circuit,
            K,
            &observations(&data.bundle),
            targets.clone(),
            options,
        )
        .unwrap();
        println!(
            "{}",
            report.phase_report_with_names(|cell| {
                targets
                    .iter()
                    .position(|target| target == cell)
                    .map(|i| data.private_values[i].0.clone())
            })
        );
        println!(
            "Recovery wall time: {:.2}s",
            started.elapsed().as_secs_f64()
        );
        assert_ne!(report.status, PrivacyAnalysisStatus::Inconsistent);
        assert_eq!(
            report.satisfiability_evidence,
            Some(SatisfiabilityEvidence::VerifiedWitness)
        );
        assert_eq!(report.satisfiability_checks, 0);
        assert_eq!(report.cells.len(), 18);
        // A privat referenciaertekeket kizarolag az eredmeny ellenorzesere hasznalja.
        for cell in &report.cells {
            let i = targets
                .iter()
                .position(|target| target == &cell.cell)
                .unwrap();
            if let Some(domain) = &cell.domain {
                let expected = field_to_bigint(&data.private_values[i].1);
                let contains = match domain {
                    UcpValueDomain::Exact(value) => value == &expected,
                    UcpValueDomain::FiniteSet(values) => values.contains(&expected),
                };
                assert!(
                    contains,
                    "True witness excluded for {}",
                    data.private_values[i].0
                );
            }
        }
        let ucp = report
            .ucp_result
            .as_ref()
            .expect("Recovery state is missing");
        // A publikus szavazat advice masolatat kontrollkent vizsgalja, nem privat szivargaskent szamolja.
        assert_eq!(
            ucp.value_facts
                .known_value(&single_advice(&analyzable.regions[4])),
            Some(&BigInt::from(1))
        );
    }
}

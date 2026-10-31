//! A kézi felárat a számla egészéhez kapcsolja, és a tényleges UCP--SMT visszacsatolást méri.

use super::{
    invoice_circuit::*,
    invoice_reference::{cart_vectors, supplier_pairs},
};
use crate::circuit_analyzer::{
    analyzable::Analyzable,
    halo2_proofs_libs::*,
    ucp::{
        cell::CellId,
        engine::UcpResult,
        extractor::extract_ucp_problem,
        privacy::{
            analyze_private_recoverability_with_witness, PrivacyAnalysisProfile,
            PrivacyAnalysisReport, PrivacyAnalysisStatus, PrivateCellUniqueness, RecoveryPhase,
        },
        value::UcpValueDomain,
    },
};
use num_bigint::BigInt;
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Instant,
};

type ApprovalInvoice = InvoiceAudit<ALL, true>;
type CatalogInvoice = InvoiceAudit<ALL, true, true>;

fn cell(column: usize) -> CellId {
    CellId::advice(column, APPROVAL_ROW as i32)
}

fn entries(domain: &UcpValueDomain) -> BTreeSet<BigInt> {
    match domain {
        UcpValueDomain::Exact(value) => [value.clone()].into(),
        UcpValueDomain::FiniteSet(values) => values.clone(),
    }
}

// Az egészszámos referencia a három régi összesítőnek megfelelő kosarakon jár végig.
// A végösszegből számolja a felárat; a mintákat és a gyököket nem adja át az elemzőnek.
fn reference(h: u64) -> Vec<(CartWitness, ApprovalWitness)> {
    reference_with_catalog(h, None)
}

fn reference_with_catalog(h: u64, catalog: Option<&[u64]>) -> Vec<(CartWitness, ApprovalWitness)> {
    let mut result = Vec::new();
    for quantities in cart_vectors(7) {
        for coupon in 0..COUPONS.len() {
            let witness = CartWitness {
                quantities,
                coupon,
                supplier_u: 0,
            };
            let subtotal: u64 = quantities.into_iter().zip(PRICES).map(|(q, p)| q * p).sum();
            let base = subtotal - subtotal * COUPONS[coupon] / 100 + 17;
            let shipping = SHIPPING
                .iter()
                .find(|s| s[1] <= OBSERVED[1] && OBSERVED[1] <= s[2])
                .unwrap()[3];
            let Some(surcharge) = OBSERVED[3].checked_sub(base + base * 20 / 100 + shipping) else {
                continue;
            };
            if surcharge >= 1 << 16 || catalog.is_some_and(|allowed| !allowed.contains(&surcharge))
            {
                continue;
            }
            for mode in 0..10 {
                if mode * (10 - mode) != h || (surcharge != 0 && mode != 5) {
                    continue;
                }
                for (supplier_u, _) in supplier_pairs(quantities[0]) {
                    result.push((
                        CartWitness {
                            supplier_u,
                            ..witness.clone()
                        },
                        ApprovalWitness { mode, surcharge },
                    ));
                }
            }
        }
    }
    result
}

fn projections(h: u64) -> BTreeMap<CellId, BTreeSet<BigInt>> {
    projections_with_catalog(h, None)
}

fn projections_with_catalog(h: u64, catalog: Option<&[u64]>) -> BTreeMap<CellId, BTreeSet<BigInt>> {
    let mut result = BTreeMap::<CellId, BTreeSet<BigInt>>::new();
    for (witness, approval) in reference_with_catalog(h, catalog) {
        let quantities = witness.quantities;
        let subtotal: u64 = quantities.into_iter().zip(PRICES).map(|(q, p)| q * p).sum();
        let rate = COUPONS[witness.coupon];
        let discount = subtotal * rate / 100;
        let base = subtotal - discount + 17;
        let shipping = SHIPPING
            .iter()
            .find(|s| s[1] <= OBSERVED[1] && OBSERVED[1] <= s[2])
            .unwrap();
        for (row, quantity) in quantities.into_iter().enumerate() {
            result
                .entry(CellId::advice(0, row as i32))
                .or_default()
                .insert(quantity.into());
        }
        for (column, value) in [
            (SUBTOTAL, subtotal),
            (COUPON, witness.coupon as u64),
            (RATE, rate),
            (DISCOUNT, discount),
            (DISCOUNT_REMAINDER, subtotal * rate % 100),
            (TAX_BASE, base),
            (TAX, base * 20 / 100),
            (TAX_REMAINDER, base * 20 % 100),
            (SHIPPING_FEE, shipping[3]),
            (SHIPPING_CLASS, shipping[0]),
        ] {
            result
                .entry(invoice_cell(column))
                .or_default()
                .insert(value.into());
        }
        for (column, value) in [
            (1, witness.supplier_u),
            (2, quantities[0] - witness.supplier_u),
        ] {
            result
                .entry(CellId::advice(column, SUPPLIER_ROW as i32))
                .or_default()
                .insert(value.into());
        }
        for column in 0..3 {
            let value = if column as u64 == shipping[0] {
                shipping[3]
            } else {
                0
            };
            result
                .entry(CellId::advice(column, LEDGER_ROW as i32))
                .or_default()
                .insert(value.into());
        }
        result
            .entry(cell(APPROVAL_MODE))
            .or_default()
            .insert(approval.mode.into());
        result
            .entry(cell(SURCHARGE))
            .or_default()
            .insert(approval.surcharge.into());
    }
    result
}

#[test]
fn thesis_invoice_approval_reference_and_mock_prover() {
    let leaking = reference(21);
    assert_eq!(leaking.len(), 24);
    for (witness, approval) in leaking {
        assert_eq!(witness.quantities, CartWitness::default().quantities);
        assert_eq!(approval.surcharge, 0);
        let circuit = ApprovalInvoice::with_approval(witness, approval.mode, approval.surcharge);
        zcash_halo2_proofs::dev::MockProver::run(K, &circuit, circuit.instances())
            .unwrap()
            .assert_satisfied();
    }
    // Ugyanazokat a publikus értékeket két eltérő kosárral is teljesíti a kivételes mód.
    let first = ApprovalInvoice::with_approval(CartWitness::default(), 5, 0);
    let second = ApprovalInvoice::with_approval(
        CartWitness {
            quantities: [38, 28, 26, 32],
            coupon: 2,
            supplier_u: 8,
        },
        5,
        432,
    );
    assert_eq!(first.instances(), second.instances());
    for circuit in [first, second] {
        zcash_halo2_proofs::dev::MockProver::run(K, &circuit, circuit.instances())
            .unwrap()
            .assert_satisfied();
    }
    assert!(reference(25)
        .iter()
        .any(
            |(witness, approval)| witness.quantities != CartWitness::default().quantities
                && approval.surcharge > 0
        ));

    let valid = ApprovalInvoice::with_approval(CartWitness::default(), 3, 0);
    // A rögzített publikus megfigyelés mellett a felár, a mód és a számjegykorlát sem írható át.
    for (column, value) in [(SURCHARGE, 1), (APPROVAL_MODE, 5), (3, 16)] {
        let mut broken = valid.clone();
        broken.tamper = Some((APPROVAL_ROW, column, value));
        assert!(
            zcash_halo2_proofs::dev::MockProver::run(K, &broken, valid.instances())
                .unwrap()
                .verify()
                .is_err()
        );
    }
    let too_large = ApprovalInvoice::with_approval(CartWitness::default(), 5, 1 << 16);
    assert!(
        zcash_halo2_proofs::dev::MockProver::run(K, &too_large, too_large.instances())
            .unwrap()
            .verify()
            .is_err()
    );
    // A módhoz kötést helyes végösszeg és érvényes számjegyek mellett is kikényszeríti.
    let unauthorized = ApprovalInvoice::with_approval(CartWitness::default(), 3, 1);
    assert!(
        zcash_halo2_proofs::dev::MockProver::run(K, &unauthorized, unauthorized.instances())
            .unwrap()
            .verify()
            .is_err()
    );
    // H=0 polinomját a 10 is kielégíti; itt kizárólag a kategórialookup zárja ki.
    let mode_zero = ApprovalInvoice::with_approval(CartWitness::default(), 0, 0);
    let mut mode_ten = mode_zero.clone();
    mode_ten.tamper = Some((APPROVAL_ROW, APPROVAL_MODE, 10));
    assert!(
        zcash_halo2_proofs::dev::MockProver::run(K, &mode_ten, mode_zero.instances())
            .unwrap()
            .verify()
            .is_err()
    );
    let empty = valid.without_witnesses();
    assert!(empty.witness.is_none() && empty.approval.is_none());
}

fn ucp_fixpoint(mode: u64) -> UcpResult {
    let circuit = ApprovalInvoice::with_approval(CartWitness::default(), mode, 0);
    let h = mode * (10 - mode);
    let before = crate::smt_solver::process::invocation_count();
    let analyzable = Analyzable::config_and_synthesize(&circuit, K).unwrap();
    let problem = extract_ucp_problem(&analyzable);
    let mut values = problem.initial_value_facts.clone();
    for (row, value) in [OBSERVED.as_slice(), &[h]].concat().into_iter().enumerate() {
        values.mark_known(CellId::instance(0, row as i32), value.into());
    }
    let started = Instant::now();
    let result = problem.analyze_with_values(problem.initial_facts.clone(), values);
    assert_eq!(crate::smt_solver::process::invocation_count(), before);
    let expected = projections(h);
    let mut exact = 0;
    for target in approval_targets() {
        if let Some(domain) = result.value_facts.domain(&target) {
            assert!(expected[&target].is_subset(&entries(domain)), "{target}");
            if result.value_facts.domain_is_complete(&target) {
                assert_eq!(entries(domain), expected[&target], "{target}");
            }
        }
        if result.facts.is_unique(&target) {
            assert_eq!(expected[&target].len(), 1, "{target}");
        }
        exact += usize::from(result.value_facts.known_value(&target).is_some());
        if std::env::var("UCP_DEMO_VERBOSE").is_ok_and(|v| v == "1") {
            println!(
                "APPROVAL_UCP {}: {:?}",
                target_name(&target),
                result.value_facts.domain(&target)
            );
        }
    }
    println!(
        "Approval invoice UCP (H={h}): {exact} exact targets, {:.2} s, 0 solver calls",
        started.elapsed().as_secs_f64()
    );
    result
}

#[test]
fn thesis_invoice_approval_ucp_fixpoint() {
    let result = ucp_fixpoint(3);
    let exact = approval_targets()
        .iter()
        .filter(|c| result.value_facts.known_value(c).is_some())
        .count();
    assert_eq!(exact, 5);
    assert!(result.value_facts.known_value(&cell(SURCHARGE)).is_none());
    assert!(entries(result.value_facts.domain(&cell(APPROVAL_MODE)).unwrap()).contains(&5.into()));
    assert!(result
        .value_facts
        .known_value(&CellId::advice(0, 0))
        .is_none());
}

#[test]
fn thesis_invoice_approval_ucp_control_keeps_real_ambiguity() {
    let result = ucp_fixpoint(5);
    // A teljes referencia több kosarat enged; az UCP nem állíthatja vissza őket egyetlenként.
    assert!(!result.facts.is_unique(&CellId::advice(0, 0)));
    assert!(!result.facts.is_unique(&cell(SURCHARGE)));
    assert!(result.value_facts.known_value(&cell(SURCHARGE)).is_none());
}

fn run_recovery<const CATALOG: bool>(mode: u64) -> PrivacyAnalysisReport {
    let circuit =
        InvoiceAudit::<ALL, true, CATALOG>::with_approval(CartWitness::default(), mode, 0);
    let h = mode * (10 - mode);
    // A profil csak a szokásos erőforráskereteket állítja; cellát vagy gyököt nem választ előre.
    let profile =
        std::env::var("UCP_INVOICE_APPROVAL_PROFILE").unwrap_or_else(|_| "standard".into());
    let (profile, label) = match profile.as_str() {
        "standard" | "combined" => (PrivacyAnalysisProfile::Standard, "standard (combined)"),
        "refinement" | "ablation-refinement" => (
            PrivacyAnalysisProfile::RefinementOnly,
            "ablation:refinement",
        ),
        _ => panic!("Unknown invoice recovery profile: {profile}"),
    };
    let options = super::recovery_options().with_profile(profile);
    println!("Approval invoice (H={h}, surcharge_catalog={CATALOG}): {label}; timeout={:?} ms/call; semantic_attempts={}; refinement_checks={}; discovery_checks={}",
        options.solver_timeout_ms, options.max_semantic_queries,
        options.domain_refinement.max_solver_checks, options.domain_discovery.max_solver_checks);
    let before = crate::smt_solver::process::invocation_count();
    let report = analyze_private_recoverability_with_witness::<Fr, _, _>(
        &circuit,
        K,
        &circuit.input(),
        approval_targets(),
        options,
    )
    .unwrap();
    assert_eq!(
        crate::smt_solver::process::invocation_count() - before,
        report.solver_invocations
    );
    println!(
        "{}",
        report.phase_report_with_names(|target| approval_targets()
            .contains(target)
            .then(|| target_name(target).to_string()))
    );
    assert_ne!(report.status, PrivacyAnalysisStatus::Inconsistent);
    assert_eq!(report.satisfiability_checks, 0);
    assert!(matches!(
        report.satisfiability_evidence,
        Some(crate::circuit_analyzer::ucp::privacy::SatisfiabilityEvidence::VerifiedWitness)
    ));
    // A teljes referenciát csak a visszaadott állítások ellenőrzéséhez használja, nem keresési premisszaként.
    let expected = projections_with_catalog(h, CATALOG.then_some(SURCHARGE_CATALOG.as_slice()));
    assert_eq!(report.cells.len(), approval_targets().len());
    for target in &report.cells {
        if let Some(domain) = &target.domain {
            assert!(
                expected[&target.cell].is_subset(&entries(domain)),
                "{}",
                target.cell
            );
            if target.domain_is_complete {
                assert_eq!(entries(domain), expected[&target.cell], "{}", target.cell);
            }
        }
        match target.uniqueness {
            PrivateCellUniqueness::Unique => assert_eq!(expected[&target.cell].len(), 1),
            PrivateCellUniqueness::NonUnique => assert!(expected[&target.cell].len() > 1),
            PrivateCellUniqueness::Unknown => (),
        }
    }
    report
}

#[test]
#[ignore = "Teljes számlavisszaállítás; sorosan, --ignored --nocapture --test-threads=1 kapcsolókkal futtatandó"]
fn thesis_invoice_approval_recovery_feedback() {
    let report = run_recovery::<false>(3);
    let expected = projections(21);
    assert_eq!(report.summary.exact_values, 17);
    for target in &report.cells {
        assert_eq!(
            entries(target.domain.as_ref().unwrap()),
            expected[&target.cell],
            "{}",
            target.cell
        );
    }
    let [RecoveryPhase::Ucp { counts: first, .. }, RecoveryPhase::Smt { steps, .. }, RecoveryPhase::Ucp {
        counts: second,
        updates,
        ..
    }, ..] = report.phases.as_slice()
    else {
        panic!("A példa valódi UCP--SMT--UCP átadást igényel");
    };
    assert_eq!(first.exact_values, 5);
    assert_eq!(second.exact_values, 17);
    assert!(steps.iter().any(|step| step.propagation_requested
        && step
            .updates
            .iter()
            .any(|update| update.cell == cell(APPROVAL_MODE)
                && update
                    .domain
                    .as_ref()
                    .is_some_and(|d| !entries(d).contains(&5.into())))));
    assert!(updates.iter().any(|update| update.cell == cell(SURCHARGE)
        && update.domain == Some(UcpValueDomain::exact(0.into()))));
    for row in 0..4 {
        assert!(updates
            .iter()
            .any(|update| update.cell == CellId::advice(0, row)
                && matches!(update.domain, Some(UcpValueDomain::Exact(_)))));
    }
}

#[test]
#[ignore = "Többértelmű számla teljes recovery-kontrollja; sorosan, --ignored --nocapture --test-threads=1 kapcsolókkal futtatandó"]
fn thesis_invoice_approval_control_recovery() {
    let report = run_recovery::<false>(5);
    assert!(report.domain_refinement_statistics.solver_checks > 0);
    let expected = projections(25);
    assert_ambiguous_cart_and_surcharge(&report, &expected);
}

fn assert_ambiguous_cart_and_surcharge(
    report: &PrivacyAnalysisReport,
    expected: &BTreeMap<CellId, BTreeSet<BigInt>>,
) {
    let ambiguous = (0..4)
        .map(|row| CellId::advice(0, row))
        .chain([cell(SURCHARGE)]);
    for target in ambiguous {
        assert!(expected[&target].len() > 1, "{target}");
        let recovered = report
            .cells
            .iter()
            .find(|entry| entry.cell == target)
            .unwrap();
        // A kontroll valódi többértelműségét sem solverkorlát, sem részleges vizsgálat nem írhatja felül.
        assert_ne!(
            recovered.uniqueness,
            PrivateCellUniqueness::Unique,
            "{target}"
        );
        assert!(
            !matches!(recovered.domain, Some(UcpValueDomain::Exact(_))),
            "{target}"
        );
    }
    assert_eq!(expected[&cell(APPROVAL_MODE)], [BigInt::from(5)].into());
    assert!(expected[&cell(SURCHARGE)].contains(&BigInt::from(0)));
    assert!(expected[&cell(SURCHARGE)].contains(&BigInt::from(432)));
}

#[test]
fn thesis_invoice_surcharge_catalog_reference_and_mock_prover() {
    let expected = reference_with_catalog(25, Some(&SURCHARGE_CATALOG));
    assert_eq!(expected.len(), 26);
    let first = CatalogInvoice::with_approval(CartWitness::default(), 5, 0);
    let public = first.instances();
    let mut carts = BTreeMap::<u64, BTreeSet<[u64; 4]>>::new();
    for (witness, approval) in expected {
        assert_eq!(approval.mode, 5);
        carts
            .entry(approval.surcharge)
            .or_default()
            .insert(witness.quantities);
        let circuit = CatalogInvoice::with_approval(witness, approval.mode, approval.surcharge);
        assert_eq!(circuit.instances(), public);
        zcash_halo2_proofs::dev::MockProver::run(K, &circuit, public.clone())
            .unwrap()
            .assert_satisfied();
    }
    assert_eq!(
        carts,
        BTreeMap::from([
            (0, BTreeSet::from([[37, 29, 25, 33]])),
            (432, BTreeSet::from([[38, 28, 26, 32]])),
        ])
    );
    // A többi szabályt teljesítő, de a katalógusban nem szereplő felárat kizárólag az új lookup utasítja el.
    let (witness, approval) = reference(25)
        .into_iter()
        .find(|(_, approval)| !SURCHARGE_CATALOG.contains(&approval.surcharge))
        .unwrap();
    let broad = ApprovalInvoice::with_approval(witness.clone(), approval.mode, approval.surcharge);
    let restricted = CatalogInvoice::with_approval(witness, approval.mode, approval.surcharge);
    assert_eq!(broad.instances(), public);
    assert_eq!(restricted.instances(), public);
    zcash_halo2_proofs::dev::MockProver::run(K, &broad, public.clone())
        .unwrap()
        .assert_satisfied();
    assert!(
        zcash_halo2_proofs::dev::MockProver::run(K, &restricted, public)
            .unwrap()
            .verify()
            .is_err()
    );
    let empty = first.without_witnesses();
    assert!(empty.witness.is_none() && empty.approval.is_none());
}

#[test]
#[ignore = "Díjkatalógusos számla teljes recovery-kontrollja; sorosan, --ignored --nocapture --test-threads=1 kapcsolókkal futtatandó"]
fn thesis_invoice_surcharge_catalog_recovery() {
    let report = run_recovery::<true>(5);
    let expected = projections_with_catalog(25, Some(&SURCHARGE_CATALOG));
    assert_ambiguous_cart_and_surcharge(&report, &expected);
    assert!(report.domain_refinement_statistics.solver_checks > 0);
    // Nem elég a kezdeti tág domaint megtartania: a kosár vetületeit a két valódi lehetőségre kell szűkítenie.
    for target in (0..4)
        .map(|row| CellId::advice(0, row))
        .chain([cell(SURCHARGE)])
    {
        let recovered = report
            .cells
            .iter()
            .find(|entry| entry.cell == target)
            .unwrap();
        assert_eq!(
            entries(recovered.domain.as_ref().unwrap()),
            expected[&target],
            "{target}"
        );
    }
}

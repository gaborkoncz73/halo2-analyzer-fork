//! A számla állításait tanúellenőrzéssel, külön referenciával és a tényleges elemzővel vizsgálja.

use super::{invoice_circuit::*, invoice_reference::*};
use crate::{
    circuit_analyzer::{
        analyzable::Analyzable,
        halo2_proofs_libs::*,
        ucp::{
            cell::CellId,
            extractor::extract_ucp_problem,
            privacy::{
                analyze_private_recoverability_with_witness, PrivacyAnalysisOptions,
                PrivacyAnalysisProfile, PrivacyAnalysisReport, PrivacyAnalysisStatus,
                PrivateCellUniqueness,
            },
            value::UcpValueDomain,
        },
    },
    smt_solver::process::invocation_count,
};
use num_bigint::BigInt;
use std::{collections::BTreeSet, time::Instant};

fn entries(domain: &UcpValueDomain) -> BTreeSet<BigInt> {
    match domain {
        UcpValueDomain::Exact(value) => [value.clone()].into(),
        UcpValueDomain::FiniteSet(values) => values.clone(),
    }
}

#[test]
fn thesis_invoice_reference_and_disclosure_ablations() {
    for (mask, count) in [
        (1, 325_618),
        (3, 772),
        (7, 55),
        (15, 1),
        (14, 10),
        (13, 28),
        (11, 14),
    ] {
        let carts = cart_vectors(mask);
        assert_eq!(carts.len(), count, "observation_mask={mask}");
        if mask == ALL {
            assert_eq!(carts, [[37, 29, 25, 33]]);
        }
        println!("INVOICE_REFERENCE mask={mask} distinct_carts={count}");
    }
    assert_eq!(full_witnesses().len(), 12);
    assert_eq!(
        supplier_pairs(37),
        [(4, 33), (10, 27), (16, 21), (22, 15), (28, 9), (34, 3)]
    );
    let values = projections();
    for (column, expected) in [
        (SUBTOTAL, 191_600),
        (RATE, 10),
        (DISCOUNT, 19_160),
        (DISCOUNT_REMAINDER, 0),
        (TAX_BASE, 172_457),
        (TAX, 34_491),
        (TAX_REMAINDER, 40),
        (SHIPPING_FEE, 1200),
        (SHIPPING_CLASS, 1),
    ] {
        assert_eq!(
            values[&invoice_cell(column)],
            [BigInt::from(expected)].into()
        );
    }
    assert_eq!(values[&invoice_cell(COUPON)], [2.into(), 3.into()].into());
}

#[test]
fn thesis_invoice_mock_prover_accepts_all_twelve_private_choices() {
    for witness in full_witnesses() {
        let circuit = InvoiceAudit::<ALL>::new(witness);
        zcash_halo2_proofs::dev::MockProver::run(K, &circuit, circuit.instances())
            .unwrap()
            .assert_satisfied();
    }
    // Egy-egy belső érték módosítása megsérti a megfelelő kaput, lookupot vagy másolási kényszert.
    for (row, column, value) in [
        (0, 1, 2),
        (INVOICE_ROW, COUPON, 0),
        (INVOICE_ROW, TAX, 34_492),
        (INVOICE_ROW, TAX_REMAINDER, 140),
        (INVOICE_ROW, SHIPPING_CLASS, 0),
        (SUPPLIER_ROW, 1, 5),
        (8, 1, 256),
    ] {
        let mut circuit = InvoiceAudit::<ALL>::new(CartWitness::default());
        circuit.tamper = Some((row, column, value));
        assert!(
            zcash_halo2_proofs::dev::MockProver::run(K, &circuit, circuit.instances())
                .unwrap()
                .verify()
                .is_err(),
            "row={row} column={column}"
        );
    }
    assert!(InvoiceAudit::<ALL>::new(CartWitness::default())
        .without_witnesses()
        .witness
        .is_none());
}

#[test]
fn thesis_invoice_missing_observations_allow_different_carts() {
    fn check<const MASK: u8>() {
        let carts = cart_vectors(MASK);
        assert!(carts.len() > 1);
        let instances = InvoiceAudit::<ALL>::new(CartWitness::default()).instances();
        for quantities in carts.into_iter().take(2) {
            let witness = (0..COUPONS.len())
                .find_map(|coupon| {
                    let witness = CartWitness {
                        quantities,
                        coupon,
                        supplier_u: supplier_pairs(quantities[0])[0].0,
                    };
                    witness
                        .observations()
                        .into_iter()
                        .zip(OBSERVED)
                        .enumerate()
                        .all(|(i, (actual, expected))| MASK & (1 << i) == 0 || actual == expected)
                        .then_some(witness)
                })
                .unwrap();
            let circuit = InvoiceAudit::<MASK>::new(witness);
            zcash_halo2_proofs::dev::MockProver::run(K, &circuit, instances.clone())
                .unwrap()
                .assert_satisfied();
            assert_eq!(
                circuit.input().verification_input.instance_cells.len(),
                MASK.count_ones() as usize
            );
        }
    }
    check::<1>();
    check::<3>();
    check::<7>();
    check::<14>();
    check::<13>();
    check::<11>();
}

#[test]
fn thesis_invoice_ucp_fixpoint_is_sound_without_solver() {
    let verbose = std::env::var("UCP_DEMO_VERBOSE").is_ok_and(|v| v == "1");
    let profiling = verbose.then(crate::circuit_analyzer::ucp::profiling::ProfilingSession::start);
    let circuit = InvoiceAudit::<ALL>::new(CartWitness::default());
    let before = invocation_count();
    let analyzable = Analyzable::config_and_synthesize(&circuit, K).unwrap();
    let problem = extract_ucp_problem(&analyzable);
    let mut values = problem.initial_value_facts.clone();
    for (row, value) in OBSERVED.into_iter().enumerate() {
        values.mark_known(CellId::instance(0, row as i32), value.into());
    }
    let started = Instant::now();
    let result = problem.analyze_with_values(problem.initial_facts.clone(), values);
    let elapsed = started.elapsed();
    assert_eq!(invocation_count(), before);
    let reference = projections();
    let mut exact = 0;
    for target in targets() {
        if let Some(domain) = result.value_facts.domain(&target) {
            assert!(reference[&target].is_subset(&entries(domain)), "{target}");
            if result.value_facts.domain_is_complete(&target) {
                assert_eq!(entries(domain), reference[&target], "{target}");
            }
        }
        if result.facts.is_unique(&target) {
            assert_eq!(reference[&target].len(), 1, "{target}");
        }
        exact += usize::from(result.value_facts.known_value(&target).is_some());
        if verbose {
            println!(
                "INVOICE_UCP_CELL name={} cell={target} domain={:?} unique={}",
                target_name(&target),
                result.value_facts.domain(&target),
                result.facts.is_unique(&target)
            );
        }
    }
    // A referencia csak utólag ellenőriz: minden célvetületet az eredeti kényszerekből állít elő.
    for target in targets() {
        assert_eq!(
            entries(result.value_facts.domain(&target).unwrap()),
            reference[&target],
            "{target}"
        );
    }
    assert_eq!(exact, 16);
    if verbose {
        println!(
            "INVOICE_UCP targets={} exact={exact} expressions={} lookups={} elapsed_ms={:.3}",
            targets().len(),
            problem.expressions.len(),
            problem.lookups.len(),
            elapsed.as_secs_f64() * 1000.0
        );
        if let Some(profile) = profiling {
            print!("{}", profile.snapshot());
        }
    } else {
        let domains = targets()
            .iter()
            .filter(|c| {
                matches!(
                    result.value_facts.domain(c),
                    Some(UcpValueDomain::FiniteSet(_))
                )
            })
            .count();
        println!("1. UCP ({:.2} s)\n  Targets: {exact} exact values, {domains} domains.\n  SMT: 0 solver calls.",elapsed.as_secs_f64());
    }
}

#[derive(Clone, Copy, Debug)]
enum Profile {
    Propagation,
    Fast,
    Refinement,
    Discovery,
    Combined,
}

fn options(profile: Profile) -> PrivacyAnalysisOptions {
    super::recovery_options().with_profile(match profile {
        Profile::Combined => PrivacyAnalysisProfile::Standard,
        Profile::Propagation => PrivacyAnalysisProfile::PropagationOnly,
        Profile::Fast => PrivacyAnalysisProfile::FastProbeOnly,
        Profile::Refinement => PrivacyAnalysisProfile::RefinementOnly,
        Profile::Discovery => PrivacyAnalysisProfile::DiscoveryOnly,
    })
}

fn check_claims(report: &PrivacyAnalysisReport) {
    assert_ne!(report.status, PrivacyAnalysisStatus::Inconsistent);
    let expected = projections();
    for cell in &report.cells {
        if let Some(domain) = &cell.domain {
            assert!(
                expected[&cell.cell].is_subset(&entries(domain)),
                "{}",
                cell.cell
            );
            if cell.domain_is_complete {
                assert_eq!(entries(domain), expected[&cell.cell], "{}", cell.cell);
            }
        } else {
            assert!(!cell.domain_is_complete);
        }
        match cell.uniqueness {
            PrivateCellUniqueness::Unique => {
                assert_eq!(expected[&cell.cell].len(), 1, "{}", cell.cell)
            }
            PrivateCellUniqueness::NonUnique => {
                assert!(expected[&cell.cell].len() > 1, "{}", cell.cell)
            }
            PrivateCellUniqueness::Unknown => (),
        }
    }
}

fn run(profile: Profile, witness: CartWitness) -> PrivacyAnalysisReport {
    let verbose = std::env::var("UCP_DEMO_VERBOSE").is_ok_and(|v| v == "1");
    let profiling = verbose.then(crate::circuit_analyzer::ucp::profiling::ProfilingSession::start);
    let circuit = InvoiceAudit::<ALL>::new(witness);
    let before = invocation_count();
    let started = Instant::now();
    if verbose {
        println!(
            "INVOICE_BEGIN profile={profile:?} timeout_ms={:?} initial_sat_timeout_ms={:?}",
            options(profile).solver_timeout_ms,
            options(profile).initial_sat_timeout_ms
        );
    } else {
        if matches!(profile, Profile::Combined) {
            println!("Invoice audit: Standard (combined)");
        } else {
            println!("Invoice audit: Ablation/{profile:?}");
        }
    }
    let report = analyze_private_recoverability_with_witness::<Fr, _, _>(
        &circuit,
        K,
        &circuit.input(),
        targets(),
        options(profile),
    )
    .unwrap();
    let elapsed = started.elapsed();
    let solver_calls = invocation_count() - before;
    check_claims(&report);
    assert_eq!(solver_calls, report.solver_invocations);
    assert!(matches!(
        report.satisfiability_evidence,
        Some(crate::circuit_analyzer::ucp::privacy::SatisfiabilityEvidence::VerifiedWitness)
    ));
    assert_eq!(report.satisfiability_checks, 0);
    assert!(!report.structural_baseline_computed);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.baseline_domain.is_none() && !cell.domain_refined_from_baseline));
    println!(
        "{}",
        report.phase_report_with_names(|cell| report
            .cells
            .iter()
            .any(|c| &c.cell == cell)
            .then(|| target_name(cell).to_string()))
    );
    if verbose {
        if let Some(profile) = profiling {
            print!("{}", profile.snapshot());
        }
        println!("INVOICE_SAT evidence={:?}", report.satisfiability_evidence);
        println!(
            "INVOICE_BASELINE computed={}",
            report.structural_baseline_computed
        );
        println!("INVOICE_RESULT profile={profile:?} status={:?} exact={} domains={} complete={} smt_invocations={} sat_checks={} semantic_attempts={} refinement_checks={} discovery_checks={} propagation_runs={} elapsed_ms={:.3}",
        report.status, report.summary.exact_values, report.summary.finite_domains,
        report.cells.iter().filter(|c| c.domain_is_complete).count(), solver_calls,
        report.satisfiability_checks, report.semantic_queries, report.domain_refinement_statistics.solver_checks,
        report.domain_discovery_statistics.solver_checks, report.search_statistics.propagation_runs,
        elapsed.as_secs_f64() * 1000.0);
        for cell in &report.cells {
            println!(
            "INVOICE_CELL name={} cell={} domain={:?} complete={} uniqueness={:?} limitation={:?}",
            target_name(&cell.cell),
            cell.cell,
            cell.domain,
            cell.domain_is_complete,
            cell.uniqueness,
            cell.recovery_limitation
        );
        }
    }
    report
}

#[test]
fn thesis_invoice_initial_sat_has_a_separate_larger_allowance() {
    let configured = options(Profile::Combined);
    let expected_initial = std::env::var("UCP_INVOICE_INITIAL_SAT_TIMEOUT_MS")
        .map(|v| v.parse::<u64>().unwrap())
        .unwrap_or(60_000);
    let expected_search = std::env::var("UCP_INVOICE_TIMEOUT_MS")
        .map(|v| v.parse::<u64>().unwrap())
        .unwrap_or(3_000);
    assert_eq!(configured.initial_sat_timeout_ms, Some(expected_initial));
    assert_eq!(configured.solver_timeout_ms, Some(expected_search));
}

#[test]
#[ignore = "Egy teljes korlátos visszaállítás; sorosan, --ignored --nocapture --test-threads=1 kapcsolókkal futtatandó"]
fn thesis_invoice_recovery_smoke() {
    let report = run(Profile::Combined, CartWitness::default());
    assert_eq!(report.summary.exact_values, 16);
    let reference = projections();
    for cell in &report.cells {
        assert_eq!(
            entries(cell.domain.as_ref().unwrap()),
            reference[&cell.cell],
            "{}",
            cell.cell
        );
    }
}

#[test]
#[ignore = "Külön SMT-mérés; sorosan, --ignored --nocapture --test-threads=1 kapcsolókkal futtatandó"]
fn thesis_invoice_measurement_matrix() {
    let profiles = std::env::var("UCP_INVOICE_PROFILES").unwrap_or_else(|_| "combined".into());
    let repeats = std::env::var("UCP_INVOICE_REPEATS")
        .map(|v| v.parse::<usize>().unwrap())
        .unwrap_or(3);
    assert!((1..=20).contains(&repeats));
    assert!(
        profiles == "all"
            || profiles.split(',').all(|p| [
                "propagation",
                "fast",
                "refinement",
                "discovery",
                "combined"
            ]
            .contains(&p))
    );
    for (name, profile) in [
        ("propagation", Profile::Propagation),
        ("fast", Profile::Fast),
        ("refinement", Profile::Refinement),
        ("discovery", Profile::Discovery),
        ("combined", Profile::Combined),
    ] {
        if profiles != "all" && !profiles.split(',').any(|p| p == name) {
            continue;
        }
        for trial in 0..=repeats {
            println!("INVOICE_TRIAL trial={trial} warmup={}", trial == 0);
            run(profile, CartWitness::default());
        }
    }
}

#[test]
#[ignore = "Két teljes visszaállítást hasonlít össze; soros, korlátos SMT-vizsgálat"]
fn thesis_invoice_alternate_witness_reports_remain_sound() {
    let first = run(Profile::Combined, CartWitness::default());
    let second = run(
        Profile::Combined,
        CartWitness {
            coupon: 3,
            supplier_u: 34,
            ..Default::default()
        },
    );
    // Az időkorlát miatt eltérő erősségű riport is helyes lehet; a bizonyított pontos értékeknek egyezniük kell.
    for (a, b) in first.cells.iter().zip(&second.cells) {
        assert_eq!(a.cell, b.cell);
        if let (Some(UcpValueDomain::Exact(x)), Some(UcpValueDomain::Exact(y))) =
            (&a.domain, &b.domain)
        {
            assert_eq!(x, y, "{}", a.cell);
        }
    }
}

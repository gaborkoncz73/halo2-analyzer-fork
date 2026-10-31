//! Original-context controls; serial execution is required for the shared SMT output paths.

use super::{
    cell::CellId,
    demo_tests::{
        linear_masking_input, linear_masking_targets, LinearMaskingCircuit, LinearMaskingMode,
    },
    external_circuit_tests::observations,
    external_range_tests::{range_private_inputs, RangeAggregateCircuit, RANGE_K},
    privacy::{
        analyze_private_recoverability, prepare_privacy_analysis, PrivacyAnalysisOptions,
        PrivacyAnalysisReport, RecoveryLimitation,
    },
    privacy_discovery::{PrivacyDomainDiscoveryOptions, PrivateDomainDiscoveryStatus},
    privacy_discovery_tests::{
        discovery_demo_input, discovery_demo_targets, LocalizedRecoveryCircuit,
        UnboundedProjectionCircuit, COPIED_CONSTANT, INCONSISTENT, UNIQUE,
    },
    privacy_observation::{
        analyze_public_observation_effect, PrivateDomainObservationEffect,
        PublicObservationEffectOptions, PublicObservationEffectStatus,
    },
    value::{normalize_field_value, UcpValueDomain, UcpValueFacts},
};
use crate::{
    circuit_analyzer::halo2_proofs_libs::*,
    io::analyzer_io_type::{AnalyzerInput, VerificationMethod},
    smt_solver::smt_parser::Satisfiability,
};
use num_bigint::BigInt;
use std::collections::BTreeSet;

fn recovery_options() -> PrivacyAnalysisOptions {
    PrivacyAnalysisOptions {
        solver_timeout_ms: Some(2_000),
        ..PrivacyAnalysisOptions::fast_probe_only()
    }
}

pub(super) fn intrinsic_control_demo() -> (
    UnboundedProjectionCircuit<UNIQUE>,
    AnalyzerInput,
    PrivacyAnalysisReport,
) {
    let circuit = UnboundedProjectionCircuit::<UNIQUE>::new(Fr::from(1), Fr::from(3));
    let input = discovery_demo_input();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        discovery_demo_targets(),
        PrivacyAnalysisOptions {
            compute_structural_baseline: true,
            ..recovery_options()
        },
    )
    .unwrap();
    (circuit, input, report)
}

#[test]
fn smt_only_intrinsic_values_are_not_misattributed_to_public_observations() {
    let (circuit, input, recovery) = intrinsic_control_demo();
    assert!(recovery.cells[0].baseline_domain.is_none());
    assert!(recovery.cells[0].domain_refined_from_baseline); // UCP baseline missed a constant root.
    assert_eq!(
        recovery.cells[0].domain,
        Some(UcpValueDomain::exact(1.into()))
    );
    let before = recovery.cells.clone();
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert_eq!(
        control.status,
        PublicObservationEffectStatus::Analyzed,
        "{control}"
    );
    assert_eq!(control.solver_checks, 5);
    assert_eq!(
        control.options.solver_timeout_ms,
        recovery.options.solver_timeout_ms
    );
    assert!(control.cells.iter().all(|cell| cell.effect
        == PrivateDomainObservationEffect::AlreadyImplied
        && cell.observed_domain_verified
        && cell.unobserved_counterexample.is_none()));
    assert_eq!(recovery.cells, before); // No relabeling of K, Delta, or the coarse-baseline metric.
}

#[test]
fn public_dependent_expanded_root_and_ucp_handoff_are_both_verified() {
    let circuit = LocalizedRecoveryCircuit::<4> { amount: 21 };
    let input = discovery_demo_input();
    MockProver::run(4, &circuit, vec![vec![Fr::from(21)]])
        .unwrap()
        .assert_satisfied();
    let recovery = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        discovery_demo_targets(),
        recovery_options(),
    )
    .unwrap();
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert_eq!(
        control.status,
        PublicObservationEffectStatus::Analyzed,
        "{control}"
    );
    assert_eq!(control.solver_checks, 5);
    for cell in &control.cells {
        assert_eq!(
            cell.effect,
            PrivateDomainObservationEffect::ObservationDependent
        );
        assert!(cell.observed_domain_verified);
        let alternate = cell.unobserved_counterexample.as_ref().unwrap();
        assert_ne!(cell.domain, Some(UcpValueDomain::exact(alternate.clone())));
    }
}

#[test]
fn reused_mask_composition_requires_observations_not_just_structural_equations() {
    let circuit = LinearMaskingCircuit::<{ LinearMaskingMode::ReusedMask as u8 }>::new(42, 58, 99);
    let input = linear_masking_input(LinearMaskingMode::ReusedMask);
    MockProver::run(4, &circuit, vec![vec![Fr::from(100)], vec![Fr::from(142)]])
        .unwrap()
        .assert_satisfied();
    let recovery = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        linear_masking_targets(LinearMaskingMode::ReusedMask),
        recovery_options(),
    )
    .unwrap();
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert_eq!(recovery.summary.exact_values, 2);
    assert!(control
        .cells
        .iter()
        .all(|cell| cell.effect == PrivateDomainObservationEffect::ObservationDependent));
}

fn range_control<const LOOKUP: bool>(
    left: u64,
    right: u64,
    expected: PrivateDomainObservationEffect,
) {
    let circuit = RangeAggregateCircuit::<LOOKUP>::new(left, right);
    let input = observations(&[(left + right) as i64]);
    MockProver::run(RANGE_K, &circuit, vec![vec![Fr::from(left + right)]])
        .unwrap()
        .assert_satisfied();
    let recovery = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        RANGE_K,
        &input,
        range_private_inputs(&circuit),
        recovery_options(),
    )
    .unwrap();
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        RANGE_K,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert_eq!(
        control.status,
        PublicObservationEffectStatus::Analyzed,
        "{control}"
    );
    assert!(control.cells.iter().all(|cell| cell.effect == expected));
    assert_eq!(control.solver_checks, 5);
}

#[test]
fn finite_domain_narrowing_is_observation_dependent_with_real_range_gates_and_lookups() {
    range_control::<false>(1, 15, PrivateDomainObservationEffect::ObservationDependent);
    range_control::<true>(1, 15, PrivateDomainObservationEffect::ObservationDependent);
}

#[test]
fn original_ranges_are_already_implied_but_boundary_exact_values_need_public_totals() {
    range_control::<false>(7, 8, PrivateDomainObservationEffect::AlreadyImplied);
    range_control::<true>(7, 8, PrivateDomainObservationEffect::AlreadyImplied);
    range_control::<false>(15, 15, PrivateDomainObservationEffect::ObservationDependent);
    range_control::<true>(15, 15, PrivateDomainObservationEffect::ObservationDependent);
}

#[test]
fn a_coarse_covering_domain_does_not_certify_absence_of_more_precise_disclosure() {
    let circuit = RangeAggregateCircuit::<false>::new(15, 15);
    let input = observations(&[30.into()]);
    let mut recovery = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        RANGE_K,
        &input,
        range_private_inputs(&circuit),
        recovery_options(),
    )
    .unwrap();
    assert_eq!(recovery.summary.exact_values, 2);
    for cell in &mut recovery.cells {
        cell.domain = UcpValueDomain::finite_set((0..16).map(BigInt::from));
    }
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        RANGE_K,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    // C already entails {0,...,15}, even though P actually makes each input exactly 15.
    assert!(control
        .cells
        .iter()
        .all(|cell| cell.effect == PrivateDomainObservationEffect::AlreadyImplied));
}

#[test]
fn fabricated_exact_or_empty_claims_are_refuted_without_assuming_recovery_facts() {
    let (circuit, input, mut recovery) = intrinsic_control_demo();
    for false_domain in [
        UcpValueDomain::exact(2.into()),
        UcpValueDomain::FiniteSet(BTreeSet::new()),
    ] {
        recovery.cells[0].domain = Some(false_domain);
        let control = analyze_public_observation_effect::<Fr, _>(
            &circuit,
            4,
            &input,
            &recovery,
            Default::default(),
        )
        .unwrap();
        assert_eq!(control.status, PublicObservationEffectStatus::Refuted);
        assert_eq!(
            control.cells[0].effect,
            PrivateDomainObservationEffect::Refuted
        );
        assert_eq!(control.cells[0].observed_counterexample, Some(1.into()));
        assert_eq!(
            control.cells[1].effect,
            PrivateDomainObservationEffect::AlreadyImplied
        );
        assert_eq!(control.solver_checks, 4);
        assert!(!control.cells[0].observed_domain_verified);
    }
}

#[test]
fn zero_and_partial_budgets_do_not_fabricate_control_verdicts_or_reset_counts() {
    let (circuit, input, recovery) = intrinsic_control_demo();
    for checks in [0, 1, 2, 3] {
        let control = analyze_public_observation_effect::<Fr, _>(
            &circuit,
            4,
            &input,
            &recovery,
            PublicObservationEffectOptions {
                max_solver_checks: checks,
                solver_timeout_ms: Some(1_000),
            },
        )
        .unwrap();
        assert_eq!(
            control.status,
            PublicObservationEffectStatus::QueryLimitReached
        );
        assert_eq!(control.solver_checks, checks);
        assert_eq!(control.options.solver_timeout_ms, Some(1_000));
        assert_eq!(control.cells[0].observed_domain_verified, checks >= 2);
        assert_eq!(
            control.cells[0].effect,
            if checks == 3 {
                PrivateDomainObservationEffect::AlreadyImplied
            } else {
                PrivateDomainObservationEffect::Unresolved
            }
        );
        assert_eq!(
            control.cells[1].effect,
            PrivateDomainObservationEffect::Unresolved
        );
        assert_eq!(
            control.cells[1].limitation,
            Some(RecoveryLimitation::QueryLimit)
        );
    }
}

#[test]
fn initial_inconsistent_context_cannot_produce_vacuous_observation_effects() {
    let circuit = UnboundedProjectionCircuit::<INCONSISTENT>::new(Fr::from(0), Fr::from(0));
    let input = discovery_demo_input();
    let mut recovery = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        discovery_demo_targets(),
        recovery_options(),
    )
    .unwrap();
    recovery.cells[0].domain = Some(UcpValueDomain::exact(0.into()));
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert_eq!(control.status, PublicObservationEffectStatus::Inconsistent);
    assert_eq!(control.solver_checks, 1);
    assert_eq!(
        control.cells[0].effect,
        PrivateDomainObservationEffect::Inconsistent
    );
    assert!(!control.cells[0].observed_domain_verified);
}

#[test]
fn unknown_recovery_or_partial_discovery_without_a_domain_remains_no_claim() {
    let circuit = LocalizedRecoveryCircuit::<0> { amount: 21 };
    let input = discovery_demo_input();
    let recovery = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        [CellId::advice(0, 0)],
        PrivacyAnalysisOptions {
            max_semantic_queries: 0,
            domain_discovery: PrivacyDomainDiscoveryOptions {
                max_solver_checks: 1,
                ..Default::default()
            },
            ..recovery_options()
        },
    )
    .unwrap();
    assert!(recovery.cells[0].domain.is_none());
    assert_eq!(
        recovery.cells[0].domain_discovery.as_ref().unwrap().status,
        PrivateDomainDiscoveryStatus::Partial
    );
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert_eq!(
        control.status,
        PublicObservationEffectStatus::NoDomainClaims
    );
    assert_eq!(control.solver_checks, 1);
    assert_eq!(
        control.cells[0].effect,
        PrivateDomainObservationEffect::NoDomainClaim
    );
}

#[test]
fn duplicate_cells_changed_observations_and_zero_timeout_are_rejected() {
    let (circuit, input, mut recovery) = intrinsic_control_demo();
    let changed = observations(&[22.into()]);
    assert!(analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &changed,
        &recovery,
        Default::default()
    )
    .unwrap_err()
    .to_string()
    .contains("same public observations"));
    assert!(analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        PublicObservationEffectOptions {
            solver_timeout_ms: Some(0),
            ..Default::default()
        }
    )
    .is_err());
    recovery.cells.push(recovery.cells[0].clone());
    assert!(analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        Default::default()
    )
    .unwrap_err()
    .to_string()
    .contains("Duplicate cells"));
}

#[test]
fn unobserved_snapshot_must_be_taken_before_binding_public_values() {
    let circuit = LocalizedRecoveryCircuit::<0> { amount: 21 };
    let input = discovery_demo_input();
    let mut context =
        prepare_privacy_analysis::<Fr, _, _>(&circuit, 4, &input, discovery_demo_targets())
            .unwrap();
    assert_eq!(
        context.analyzer.check_ucp_satisfiability(&input).unwrap(),
        Satisfiability::Satisfiable
    );
    context.analyzer.instance_cells.clear();
    let mut cleared = input.clone();
    cleared.verification_method = VerificationMethod::None;
    cleared.verification_input.instance_cells.clear();
    assert!(context
        .analyzer
        .original_private_query_context_without_observations(&cleared, &context.private_cells)
        .is_err());
}

#[test]
fn paired_snapshots_remain_independent_of_later_strengthening_and_query_exclusions() {
    let circuit = LocalizedRecoveryCircuit::<0> { amount: 21 };
    let input = discovery_demo_input();
    let mut context =
        prepare_privacy_analysis::<Fr, _, _>(&circuit, 4, &input, discovery_demo_targets())
            .unwrap();
    let unobserved = context
        .analyzer
        .original_private_query_context_without_observations(&input, &context.private_cells)
        .unwrap();
    let observed = context
        .analyzer
        .original_private_query_context(&input, &context.private_cells)
        .unwrap();
    let cell = &context.private_cells[0];
    let blocked = BTreeSet::from([21.into()]);
    assert_eq!(
        observed.check_satisfiability::<Fr>(Some(2_000)).unwrap(),
        Satisfiability::Satisfiable
    );
    assert!(unobserved
        .query_unseen_value::<Fr>(cell, &blocked, Some(2_000))
        .unwrap()
        .is_some());
    assert!(observed
        .query_unseen_value::<Fr>(cell, &blocked, Some(2_000))
        .unwrap()
        .is_none());
    let mut wrong = UcpValueFacts::new();
    wrong.mark_known(cell.clone(), 22.into());
    context.analyzer.set_ucp_value_facts(&wrong);
    assert_eq!(
        context.analyzer.check_ucp_satisfiability(&input).unwrap(),
        Satisfiability::Unsatisfiable
    );
    let counterexample = unobserved
        .query_unseen_value::<Fr>(cell, &blocked, Some(2_000))
        .unwrap()
        .unwrap();
    assert_ne!(
        normalize_field_value(counterexample, &context.problem.field_modulus),
        Some(21.into())
    );
    assert!(observed
        .query_unseen_value::<Fr>(cell, &blocked, Some(2_000))
        .unwrap()
        .is_none());
    assert_eq!(
        observed
            .query_unseen_value::<Fr>(cell, &BTreeSet::new(), Some(2_000))
            .unwrap(),
        Some(21.into())
    );
}

#[test]
fn field_equivalent_report_values_do_not_create_a_false_public_effect() {
    let (circuit, input, mut recovery) = intrinsic_control_demo();
    let modulus = super::extractor::field_modulus::<Fr>();
    recovery.cells[0].domain = Some(UcpValueDomain::exact(modulus + BigInt::from(1)));
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert_eq!(control.status, PublicObservationEffectStatus::Analyzed);
    assert!(control
        .cells
        .iter()
        .all(|cell| cell.effect == PrivateDomainObservationEffect::AlreadyImplied));
}

#[test]
fn a_private_cell_copied_to_an_instance_is_not_frozen_in_the_unobserved_snapshot() {
    use crate::sample_circuits::zcash::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit;
    let circuit = TwoBitDecompCircuit::<Fr>::default();
    let input = observations(&[3]);
    MockProver::run(4, &circuit, vec![vec![Fr::from(3)]])
        .unwrap()
        .assert_satisfied();
    let recovery = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        [CellId::advice(2, 0)],
        recovery_options(),
    )
    .unwrap();
    assert_eq!(
        recovery.cells[0].domain,
        Some(UcpValueDomain::exact(3.into()))
    );
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert_eq!(control.status, PublicObservationEffectStatus::Analyzed);
    assert_eq!(
        control.cells[0].effect,
        PrivateDomainObservationEffect::ObservationDependent
    );
    assert!(control.cells[0].unobserved_counterexample.is_some());
    assert_eq!(control.solver_checks, 3);
}

#[test]
fn copied_fixed_constants_are_intrinsic_not_a_publication_effect() {
    let circuit = UnboundedProjectionCircuit::<COPIED_CONSTANT>::new(Fr::from(7), Fr::from(7));
    let input = discovery_demo_input();
    let recovery = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        discovery_demo_targets(),
        recovery_options(),
    )
    .unwrap();
    let control = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert!(control
        .cells
        .iter()
        .all(|cell| cell.domain == Some(UcpValueDomain::exact(7.into()))
            && cell.effect == PrivateDomainObservationEffect::AlreadyImplied));
    assert_eq!(control.solver_checks, 5);
}

#[test]
fn actual_supplied_advice_assignments_do_not_supply_observation_evidence() {
    let circuit = LocalizedRecoveryCircuit::<0> { amount: 21 };
    let input = discovery_demo_input();
    let recovery = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        discovery_demo_targets(),
        recovery_options(),
    )
    .unwrap();
    let wrong_witness = LocalizedRecoveryCircuit::<0> { amount: 99 };
    assert!(MockProver::run(4, &wrong_witness, vec![vec![Fr::from(21)]])
        .unwrap()
        .verify()
        .is_err());
    let control = analyze_public_observation_effect::<Fr, _>(
        &wrong_witness,
        4,
        &input,
        &recovery,
        Default::default(),
    )
    .unwrap();
    assert_eq!(control.status, PublicObservationEffectStatus::Analyzed);
    assert_eq!(
        control.cells[0].domain,
        Some(UcpValueDomain::exact(21.into()))
    );
    assert!(control
        .cells
        .iter()
        .all(|cell| cell.effect == PrivateDomainObservationEffect::ObservationDependent));
}

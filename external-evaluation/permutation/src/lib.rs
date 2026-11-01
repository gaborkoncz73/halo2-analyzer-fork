//! A kozvetlenul importalt permutacios circuit privat sorrendjet vizsgalja.

#[cfg(test)]
mod tests {
    use korrekt::{
        circuit_analyzer::{
            analyzable::Analyzable,
            halo2_proofs_libs::{Any, Fr, MockProver, Value},
            ucp::{
                cell::CellId,
                extractor::extract_ucp_problem,
                privacy::{
                    analyze_private_recoverability_with_witness, PrivacyAnalysisOptions,
                    PrivacyAnalysisReport, PrivacyAnalysisStatus, PrivateCellUniqueness,
                    SatisfiabilityEvidence,
                },
                value::UcpValueDomain,
            },
        },
        io::analyzer_io_type::{
            AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod,
        },
    };
    use num_bigint::BigInt;
    use std::collections::{BTreeMap, BTreeSet};
    use zk_halo2_playground::{utilities::PermutationsIter, PermutationCircuit};

    const N: usize = 5;
    const K: u32 = 4;
    const SWAPS: usize = N * (N - 1) / 2;
    type ExternalCircuit = PermutationCircuit<Fr, N>;

    fn circuit(permutation: [usize; N]) -> ExternalCircuit {
        // Az eredeti API a permutacio indexeit rendezi; az azonos bemeneti sorbol 0..N lesz.
        ExternalCircuit::new_unchecked(
            permutation.map(|value| Value::known(Fr::from(value as u64))),
            permutation,
        )
    }

    fn public_values() -> Vec<Fr> {
        (0..N).map(|value| Fr::from(value as u64)).collect()
    }

    fn observations() -> AnalyzerInput {
        AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new(
                (0..N).map(|i| (format!("I-0-{i}"), BigInt::from(i))),
                1,
            ),
            lookup_method: LookupMethod::InlineConstraints,
        }
    }

    // Kizarolag az eredeti inputregio cellait jeloli ki, masolatokat es kapcsolokat nem.
    fn targets(layout: &Analyzable<Fr>) -> BTreeMap<CellId, String> {
        let regions: Vec<_> = layout
            .regions
            .iter()
            .filter(|r| r.name == "input values")
            .collect();
        assert_eq!(regions.len(), 1);
        let region = regions[0];
        assert_eq!(region.cells.len(), N);
        let mut cells: Vec<_> = region
            .cells
            .iter()
            .map(|(column, row)| {
                assert_eq!(column.column_type(), &Any::Advice);
                (column.index(), *row)
            })
            .collect();
        cells.sort_unstable();
        assert_eq!(
            cells.iter().map(|(col, _)| *col).collect::<Vec<_>>(),
            (0..N).collect::<Vec<_>>()
        );
        cells
            .into_iter()
            .enumerate()
            .map(|(i, (col, row))| {
                (
                    CellId::advice(col, i32::try_from(row).unwrap()),
                    format!("input_{i}"),
                )
            })
            .collect()
    }

    fn options() -> PrivacyAnalysisOptions {
        let timeout = std::env::var("UCP_PERMUTATION_TIMEOUT_MS")
            .map(|value| value.parse().expect("Invalid UCP_PERMUTATION_TIMEOUT_MS"))
            .unwrap_or(3_000);
        assert!(timeout > 0);
        let mut options = PrivacyAnalysisOptions::default();
        options.solver_timeout_ms = Some(timeout);
        options.initial_sat_timeout_ms = Some(60_000);
        options.search.retry_solver_timeout_ms = None;
        options
    }

    fn recover(circuit: &ExternalCircuit) -> PrivacyAnalysisReport {
        let layout = Analyzable::<Fr>::config_and_synthesize(circuit, K).unwrap();
        analyze_private_recoverability_with_witness::<Fr, _, _>(
            circuit,
            K,
            &observations(),
            targets(&layout).into_keys(),
            options(),
        )
        .unwrap()
    }

    // A referenciaertekek csak az elemzes utan ellenorzik a riportot, solverpremisszak nem lesznek.
    fn check_report(report: &PrivacyAnalysisReport) {
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(
            report.satisfiability_evidence,
            Some(SatisfiabilityEvidence::VerifiedWitness)
        );
        assert_eq!(report.satisfiability_checks, 0);
        assert_eq!(report.summary.private_cells, N);
        assert_eq!(report.summary.exact_values, 0);
        assert_eq!(report.summary.non_unique_cells, N);
        assert_eq!(report.summary.unresolved_uniqueness, 0);
        let expected: BTreeSet<_> = (0..N).map(BigInt::from).collect();
        for cell in &report.cells {
            assert_eq!(cell.uniqueness, PrivateCellUniqueness::NonUnique);
            match &cell.domain {
                Some(UcpValueDomain::FiniteSet(values)) => {
                    assert!(expected.is_subset(values));
                    if cell.domain_is_complete {
                        assert_eq!(values, &expected);
                    }
                }
                None => assert!(!cell.domain_is_complete),
                Some(UcpValueDomain::Exact(_)) => panic!("Permutation input is not unique"),
            }
        }
    }

    #[test]
    fn imported_permutation_accepts_all_120_private_orders() {
        let mut projections: [BTreeSet<usize>; N] = std::array::from_fn(|_| BTreeSet::new());
        let mut count = 0;
        let mut expected_targets = None;
        for permutation in PermutationsIter::<N> {
            let circuit = circuit(permutation);
            MockProver::run(K, &circuit, vec![public_values()])
                .unwrap()
                .assert_satisfied();
            let layout = Analyzable::<Fr>::config_and_synthesize(&circuit, K).unwrap();
            let actual_targets = targets(&layout);
            if let Some(expected) = &expected_targets {
                assert_eq!(&actual_targets, expected);
            } else {
                expected_targets = Some(actual_targets);
            }
            for (i, value) in permutation.into_iter().enumerate() {
                projections[i].insert(value);
            }
            count += 1;
        }
        assert_eq!(count, 120);
        assert!(projections.iter().all(|values| *values == (0..N).collect()));

        let circuit = circuit([0, 1, 2, 3, 4]);
        for index in 0..N {
            let mut wrong = public_values();
            wrong[index] = Fr::from(99);
            assert!(MockProver::run(K, &circuit, vec![wrong])
                .unwrap()
                .verify()
                .is_err());
        }
    }

    #[test]
    fn imported_permutation_ucp_infers_boolean_switch_domains() {
        let circuit = circuit([0, 1, 2, 3, 4]);
        let layout = Analyzable::<Fr>::config_and_synthesize(&circuit, K).unwrap();
        let problem = extract_ucp_problem(&layout);
        let mut values = problem.initial_value_facts.clone();
        for i in 0..N {
            values.mark_known(CellId::instance(0, i as i32), BigInt::from(i));
        }
        let result = problem.analyze_with_values(problem.initial_facts.clone(), values);
        let boolean_domain = UcpValueDomain::finite_set([0.into(), 1.into()]);
        let switches: Vec<_> = problem
            .witness_cells
            .iter()
            .filter(|cell| cell.column >= N)
            .collect();
        assert_eq!(switches.len(), SWAPS);
        for cell in switches {
            assert_eq!(result.value_facts.domain(cell), boolean_domain.as_ref());
        }
        println!("UCP: {SWAPS} auxiliary swap-switch domains {{0, 1}}; no SMT calls.");
    }

    #[test]
    fn imported_permutation_standard_recovery() {
        let circuit = circuit([0, 1, 2, 3, 4]);
        let layout = Analyzable::<Fr>::config_and_synthesize(&circuit, K).unwrap();
        let names = targets(&layout);
        let problem = extract_ucp_problem(&layout);
        println!("Unmodified imported permutation: Standard (combined)");
        println!("{N} private inputs; {SWAPS} swaps; {} equations; {} advice cells; public output=[0, 1, 2, 3, 4]", problem.expressions.len(), problem.witness_cells.len());
        let report = recover(&circuit);
        println!(
            "{}",
            report.phase_report_with_names(|cell| names.get(cell).cloned())
        );
        check_report(&report);
    }

    #[test]
    #[ignore = "stronger full-domain measurement; may require a longer UCP_PERMUTATION_TIMEOUT_MS"]
    fn imported_permutation_complete_domain_recovery() {
        let circuit = circuit([0, 1, 2, 3, 4]);
        let layout = Analyzable::<Fr>::config_and_synthesize(&circuit, K).unwrap();
        let names = targets(&layout);
        let report = recover(&circuit);
        println!(
            "{}",
            report.phase_report_with_names(|cell| names.get(cell).cloned())
        );
        check_report(&report);
        let expected = UcpValueDomain::finite_set((0..N).map(BigInt::from));
        for cell in &report.cells {
            assert_eq!(cell.domain, expected);
            assert!(cell.domain_is_complete);
        }
    }
}

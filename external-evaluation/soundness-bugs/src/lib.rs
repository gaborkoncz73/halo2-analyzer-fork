//! Kulso circuiteken ellenorzi a privat ertekek visszaallitasat.

#[cfg(test)]
mod compat {
    // Az eltero API-verzio hibanevet illeszti; a circuit forrasat es eredeti testet megtartja.
    pub use backend::{arithmetic, circuit, halo2curves, poly};
    pub mod plonk {
        pub use backend::plonk::*;
        pub type ErrorFront = backend::plonk::Error;
    }
}

#[cfg(test)]
mod casino_tests;

#[cfg(test)]
mod merkle_tests;

#[cfg(test)]
mod tests {
    mod unbounded {
        use crate::compat as halo2_proofs;
        include!(concat!(env!("CARGO_MANIFEST_DIR"), "/target/halo2-soundness-bugs-4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4/src/square_root/sroot0.rs"));
    }

    mod bounded {
        use crate::compat as halo2_proofs;
        include!(concat!(env!("CARGO_MANIFEST_DIR"), "/target/halo2-soundness-bugs-4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4/src/square_root/sroot1.rs"));
    }

    use korrekt::{
        circuit_analyzer::{
            analyzable::Analyzable,
            analyzer::Analyzer,
            halo2_proofs_libs::{Any, Circuit, Fr, MockProver, Value},
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
            AnalyzerInput, AnalyzerType, LookupMethod, VerificationInput, VerificationMethod,
        },
    };
    use num_bigint::BigInt;
    use std::{collections::BTreeSet, time::Instant};

    const K: u32 = 5;

    fn observations(square: u64) -> AnalyzerInput {
        AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new([("I-0-0".into(), BigInt::from(square))], 1),
            lookup_method: LookupMethod::InlineConstraints,
        }
    }

    // A kapu altal hasznalt fo regio legelso advice cellajat valasztja, tanuertek olvasasa nelkul.
    fn root_target<C: Circuit<Fr>>(circuit: &C) -> CellId {
        let analyzable = Analyzable::<Fr>::config_and_synthesize(circuit, K).unwrap();
        let regions: Vec<_> = analyzable
            .regions
            .iter()
            .filter(|region| region.name == "main region")
            .collect();
        assert_eq!(regions.len(), 1);
        let mut cells: Vec<_> = regions[0]
            .cells
            .keys()
            .filter(|(column, _)| matches!(column.column_type(), Any::Advice(_)))
            .map(|(column, row)| (column.index(), *row))
            .collect();
        cells.sort_unstable();
        assert_eq!(cells.len(), 2, "Upstream witness layout changed");
        assert_eq!(cells[0].0, 0);
        CellId::advice(cells[0].0, i32::try_from(cells[0].1).unwrap())
    }

    fn options() -> PrivacyAnalysisOptions {
        let timeout = std::env::var("UCP_SROOT_TIMEOUT_MS")
            .map(|value| value.parse::<u64>().expect("Invalid UCP_SROOT_TIMEOUT_MS"))
            .unwrap_or(3000);
        assert!(timeout > 0);
        let mut options = PrivacyAnalysisOptions::default();
        options.solver_timeout_ms = Some(timeout);
        options.search.retry_solver_timeout_ms = None;
        options
    }

    fn recover<C: Circuit<Fr>>(label: &str, circuit: &C, square: u64) -> PrivacyAnalysisReport {
        let target = root_target(circuit);
        let analyzable = Analyzable::<Fr>::config_and_synthesize(circuit, K).unwrap();
        let problem = extract_ucp_problem(&analyzable);
        let options = options();
        println!(
            "\n{label}; Standard; {} equations; {} advice cells; {} Halo2 lookup arguments; timeout={}ms",
            problem.expressions.len(),
            problem.witness_cells.len(),
            analyzable.cs.lookups.len(),
            options.solver_timeout_ms.unwrap()
        );
        let started = Instant::now();
        let report = analyze_private_recoverability_with_witness::<Fr, _, _>(
            circuit,
            K,
            &observations(square),
            [target],
            options,
        )
        .unwrap();
        println!(
            "{}",
            report.phase_report_with_names(|_| Some("private_root".into()))
        );
        println!(
            "Recovery wall time: {:.3}s",
            started.elapsed().as_secs_f64()
        );
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(
            report.satisfiability_evidence,
            Some(SatisfiabilityEvidence::VerifiedWitness)
        );
        assert_eq!(report.satisfiability_checks, 0);
        assert_eq!(report.cells.len(), 1);
        report
    }

    #[test]
    fn external_square_root_two_roots_complete_domain() {
        let circuit = unbounded::SquareRootCircuit {
            root: Value::known(Fr::from(3)),
        };
        let alternate = unbounded::SquareRootCircuit {
            root: Value::known(-Fr::from(3)),
        };
        for witness in [&circuit, &alternate] {
            MockProver::run(K, witness, vec![vec![Fr::from(9)]])
                .unwrap()
                .assert_satisfied();
        }
        let report = recover("Unrestricted square root; public square=9", &circuit, 9);
        // A teljes referenciahalmaz csak az eredmeny ellenorzeseben szerepel, nem keresesi premissza.
        // A rendszer a p-3 testelemet az azzal egyenerteku -3 reprezentanssal tarolja.
        let expected = UcpValueDomain::finite_set([BigInt::from(3), BigInt::from(-3)]);
        assert_eq!(report.cells[0].domain, expected);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
        assert!(report.cells[0].domain_is_complete);
        let alternate_report = recover(
            "Same public square; different supplied witness",
            &alternate,
            9,
        );
        assert_eq!(report.cells[0].domain, alternate_report.cells[0].domain);
        assert_eq!(
            report.cells[0].uniqueness,
            alternate_report.cells[0].uniqueness
        );
        assert_eq!(
            report.cells[0].domain_is_complete,
            alternate_report.cells[0].domain_is_complete
        );
    }

    #[test]
    fn external_square_root_zero_exact() {
        let circuit = unbounded::SquareRootCircuit {
            root: Value::known(Fr::from(0)),
        };
        let report = recover("Unrestricted square root; public square=0", &circuit, 0);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(0.into()))
        );
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert!(report.cells[0].domain_is_complete);
    }

    #[test]
    fn external_square_root_lookup_exact() {
        let circuit = bounded::SquareRootCircuit {
            root: Value::known(Fr::from(3)),
        };
        let analyzable = Analyzable::<Fr>::config_and_synthesize(&circuit, K).unwrap();
        let problem = extract_ucp_problem(&analyzable);
        let expected: BTreeSet<_> = (0..=10).map(BigInt::from).collect();
        assert_eq!(
            problem.initial_value_facts.domain(&root_target(&circuit)),
            Some(&UcpValueDomain::FiniteSet(expected))
        );
        let report = recover(
            "Lookup-bounded square root (0..=10); public square=9",
            &circuit,
            9,
        );
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(3.into()))
        );
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert!(report.cells[0].domain_is_complete);
    }

    #[test]
    fn external_square_root_controls_reject_invalid_witnesses() {
        let valid = unbounded::SquareRootCircuit {
            root: Value::known(Fr::from(3)),
        };
        assert!(MockProver::run(K, &valid, vec![vec![Fr::from(10)]])
            .unwrap()
            .verify()
            .is_err());
        let outside_range = bounded::SquareRootCircuit {
            root: Value::known(-Fr::from(3)),
        };
        assert!(MockProver::run(K, &outside_range, vec![vec![Fr::from(9)]])
            .unwrap()
            .verify()
            .is_err());
    }

    #[test]
    fn pse_unconstrained_scan_respects_copy_constraints() {
        let circuit = unbounded::SquareRootCircuit {
            root: Value::known(Fr::from(3)),
        };
        let input = observations(9);
        let mut analyzer =
            Analyzer::<Fr>::new(&circuit, K, AnalyzerType::UnconstrainedCells, Some(&input))
                .unwrap();
        let output = analyzer.analyze_unconstrained_cells().unwrap();
        assert_eq!(
            output.output_status,
            korrekt::io::analyzer_io_type::AnalyzerOutputStatus::NoUnconstrainedCells
        );
    }

    #[test]
    fn pse_unconstrained_scan_uses_row_keys_not_assignment_counts() {
        use backend::{
            circuit::{Layouter, SimpleFloorPlanner},
            plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
            poly::Rotation,
        };

        // Helyi backend-kontroll: a sorindex es a hozzarendelesek szama elter.
        struct ScanControl;
        impl Circuit<Fr> for ScanControl {
            type Config = (Column<Advice>, Selector);
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self
            }

            fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
                let column = meta.advice_column();
                let selector = meta.selector();
                meta.create_gate("selected row equals one", |meta| {
                    let q = meta.query_selector(selector);
                    let value = meta.query_advice(column, Rotation::cur());
                    vec![q * (value - Expression::Constant(Fr::from(1)))]
                });
                (column, selector)
            }

            fn synthesize(
                &self,
                (column, selector): Self::Config,
                mut layouter: impl Layouter<Fr>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "row-key regression control",
                    |mut region| {
                        selector.enable(&mut region, 1)?;
                        region.assign_advice(
                            || "constrained",
                            column,
                            1,
                            || Value::known(Fr::from(1)),
                        )?;
                        region.assign_advice(
                            || "unconstrained",
                            column,
                            3,
                            || Value::known(Fr::from(2)),
                        )?;
                        Ok(())
                    },
                )
            }
        }
        MockProver::run(K, &ScanControl, vec![])
            .unwrap()
            .assert_satisfied();
        let mut analyzer =
            Analyzer::<Fr>::new(&ScanControl, K, AnalyzerType::UnconstrainedCells, None).unwrap();
        assert_eq!(
            analyzer
                .analyze_unconstrained_cells()
                .unwrap()
                .output_status,
            korrekt::io::analyzer_io_type::AnalyzerOutputStatus::UnconstrainedCells
        );
    }
}

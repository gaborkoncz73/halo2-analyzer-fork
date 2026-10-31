#![cfg(feature = "use_zcash_halo2_proofs")]

//! End-to-end UCP demos.
//!
//! Ezek nem mikroszkopikus unit tesztek, hanem előadásra is használható
//! demonstrációk:
//!   - ugyanarra a circuitre lefuttatjuk a sima Analyzer/SMT útvonalat,
//!   - majd lefuttatjuk az UCP + SMT pipeline-t,
//!   - és kiírjuk az időket, a státuszt, valamint hogy kellett-e SMT query.
//!
//! A cél nem az, hogy flaky időbeli assertet írjunk, hanem hogy `--nocapture`
//! mellett jól látszódjon: amikor az UCP szabályok elég erősek, a drága SMT
//! részt teljesen vagy majdnem teljesen el tudjuk kerülni.
//!
//! Alapbol rovid osszefoglalot irunk; a teljes riport: `UCP_DEMO_VERBOSE=1`.

use super::{
    cell::CellId,
    pipeline::{analyze_underconstrained_with_ucp, UcpAnalyzerPipelineStatus},
    privacy::{
        analyze_private_recoverability, PrivacyAnalysisOptions, PrivacyAnalysisReport,
        PrivacyAnalysisStatus, PrivateCellUniqueness,
    },
    privacy_discovery::PrivateDomainDiscoveryStatus,
    privacy_domain::PrivateDomainRefinementStatus,
    privacy_observation::PublicObservationEffectReport,
    privacy_validation::{
        validate_private_recovery_report, validate_private_recovery_report_with_timeout,
        PrivateRecoveryValidationReport, RecoveryValidationStatus,
    },
    value::UcpValueDomain,
};
use crate::{
    circuit_analyzer::{analyzer::Analyzer, halo2_proofs_libs::*},
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerOutputStatus, AnalyzerType, LookupMethod, VerificationInput,
        VerificationMethod,
    },
};
use std::{array, collections::HashMap, fmt, marker::PhantomData, time::Duration, time::Instant};

#[path = "risk_audit_demo_tests.rs"]
mod risk_audit;

fn demo_verbose() -> bool {
    std::env::var("UCP_DEMO_VERBOSE").is_ok_and(|value| value == "1")
}

fn demo_report_text(
    report: &impl fmt::Display,
    compact: impl FnOnce() -> String,
    verbose: bool,
) -> String {
    if verbose {
        report.to_string()
    } else {
        compact()
    }
}

fn print_demo_report(title: &str, report: &impl fmt::Display, compact: impl FnOnce() -> String) {
    println!(
        "{title}\n{}",
        demo_report_text(report, compact, demo_verbose())
    );
}

fn short_demo_domain(domain: Option<&UcpValueDomain>) -> String {
    match domain {
        Some(UcpValueDomain::Exact(value)) => format!("Exact({value})"),
        Some(UcpValueDomain::FiniteSet(values)) => {
            let preview: Vec<_> = values.iter().take(8).map(ToString::to_string).collect();
            let suffix = if values.len() > preview.len() {
                ", ..."
            } else {
                ""
            };
            format!(
                "Candidates({{{}{suffix}}}; size={})",
                preview.join(", "),
                values.len()
            )
        }
        None => "No recovered domain".into(),
    }
}

fn short_privacy_report(report: &PrivacyAnalysisReport) -> String {
    if !report.phases.is_empty() {
        return report.phase_report();
    }
    let summary = &report.summary;
    let mut lines = vec![format!(
        "Privacy: {:?}; cells: {}; exact: {}; finite domains: {}; unique: {}; non-unique: {}; unresolved: {}",
        report.status, summary.private_cells, summary.exact_values, summary.finite_domains,
        summary.unique_cells, summary.non_unique_cells, summary.unresolved_uniqueness,
    )];
    for cell in &report.cells {
        let mut line = format!(
            "{}: {:?}; {}",
            cell.cell,
            cell.uniqueness,
            short_demo_domain(cell.domain.as_ref())
        );
        if cell.domain_is_complete && matches!(cell.domain, Some(UcpValueDomain::FiniteSet(_))) {
            line.push_str("; complete domain");
        }
        if let Some(limitation) = &cell.recovery_limitation {
            line.push_str(&format!("; limitation: {limitation:?}"));
        }
        // Analyzed can coexist with unfinished optional searches; do not hide that evidence.
        if let Some(evidence) = &cell.domain_refinement {
            if evidence.status != PrivateDomainRefinementStatus::Complete {
                line.push_str(&format!(
                    "; refinement: {:?} ({:?})",
                    evidence.status, evidence.limitation
                ));
            }
        }
        if let Some(evidence) = &cell.domain_discovery {
            if evidence.status != PrivateDomainDiscoveryStatus::Complete {
                line.push_str(&format!(
                    "; discovery: {:?} ({:?})",
                    evidence.status, evidence.limitation
                ));
            }
        }
        lines.push(line);
    }
    let mut checks = format!(
        "Initial SAT checks: {}; SMT uniqueness queries: {}",
        report.satisfiability_checks, report.semantic_queries
    );
    if report.domain_refinement_statistics.solver_checks > 0 {
        checks.push_str(&format!(
            "; refinement checks: {}",
            report.domain_refinement_statistics.solver_checks
        ));
    }
    if report.domain_discovery_statistics.solver_checks > 0 {
        checks.push_str(&format!(
            "; discovery checks: {}",
            report.domain_discovery_statistics.solver_checks
        ));
    }
    checks.push_str(&format!("; elapsed: {:.2?}", report.elapsed));
    lines.push(checks);
    if report.search_statistics.stop_reason.is_some()
        || report.domain_refinement_statistics.budget_exhausted
        || report.domain_discovery_statistics.budget_exhausted
    {
        lines.push(format!(
            "Search stop: {:?}; refinement budget exhausted: {}; discovery budget exhausted: {}",
            report.search_statistics.stop_reason,
            report.domain_refinement_statistics.budget_exhausted,
            report.domain_discovery_statistics.budget_exhausted
        ));
    }
    lines.join("\n")
}

fn print_privacy_demo(title: &str, report: &PrivacyAnalysisReport) {
    print_demo_report(title, report, || short_privacy_report(report));
}

fn short_validation_report(report: &PrivateRecoveryValidationReport) -> String {
    let mut lines = vec![format!(
        "Domain validation: {:?}; checked claims: {}; SMT checks: {}; elapsed: {:.2?}",
        report.status, report.domain_queries, report.solver_checks, report.elapsed
    )];
    for cell in &report.cells {
        if let Some(value) = &cell.counterexample {
            lines.push(format!(
                "{}: {:?}; counterexample: {value}",
                cell.cell, cell.status
            ));
        }
    }
    lines.join("\n")
}

fn print_validation_demo(title: &str, report: &PrivateRecoveryValidationReport) {
    print_demo_report(title, report, || short_validation_report(report));
}

fn short_observation_report(report: &PublicObservationEffectReport) -> String {
    let mut lines = vec![format!(
        "Observation control: {:?}; SMT checks: {}; elapsed: {:.2?}",
        report.status, report.solver_checks, report.elapsed
    )];
    for cell in &report.cells {
        let mut line = format!(
            "{}: {:?}; observed domain verified: {}",
            cell.cell, cell.effect, cell.observed_domain_verified
        );
        if let Some(value) = &cell.observed_counterexample {
            line.push_str(&format!("; counterexample under observations: {value}"));
        }
        if let Some(limitation) = &cell.limitation {
            line.push_str(&format!("; limitation: {limitation:?}"));
        }
        lines.push(line);
    }
    lines.join("\n")
}

fn print_observation_demo(title: &str, report: &PublicObservationEffectReport) {
    print_demo_report(title, report, || short_observation_report(report));
}

//N darab privát bit advice oszlop és egy selector, ami az egyetlen aktív sort kapcsolja.
#[derive(Clone, Debug)]
pub(super) struct PrivateAmountBitsConfig<const N: usize> {
    //A privát amount bitjei: bit_i = 0 vagy 1
    bits: [Column<Advice>; N],
    //A boolean és packing constraint-ek bekapcsolója
    selector: Selector,
}

//Privát amountot bont bitekre, majd bizonyítja, hogy a bitek public amounttá pakolódnak.
#[derive(Clone, Debug)]
pub(super) struct PrivateAmountBitsCircuit<const N: usize> {
    //A witnessként betöltött privát érték
    amount: u64,
    _marker: PhantomData<Fr>,
}

impl<const N: usize> PrivateAmountBitsCircuit<N> {
    pub(super) fn new(amount: u64) -> Self {
        Self {
            amount,
            _marker: PhantomData,
        }
    }
}

impl<const N: usize> Circuit<Fr> for PrivateAmountBitsCircuit<N> {
    type Config = PrivateAmountBitsConfig<N>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(0)
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        //Public input: az az amount, amire a privát biteknek vissza kell állniuk
        let public_amount = meta.instance_column();
        //Advice oszlopok: az amount bitjei
        let bits = array::from_fn(|_| meta.advice_column());
        //Selector: csak azon a soron aktívak a constraint-ek, ahol witness-t adunk
        let selector = meta.selector();

        meta.create_gate(
            "private amount bits are boolean and pack to public amount",
            |meta| {
                let selector_expr = meta.query_selector(selector);
                let public_amount = meta.query_instance(public_amount, Rotation::cur());
                let mut constraints = Vec::with_capacity(N + 1);
                let mut packed = Expression::Constant(Fr::from(0));

                for (index, bit_column) in bits.iter().enumerate() {
                    let bit = meta.query_advice(*bit_column, Rotation::cur());
                    let weight = Expression::Constant(Fr::from(1_u64 << index));

                    //Root rule demó: bit * (bit - 1) = 0 miatt Delta(bit) = {0, 1}.
                    constraints.push(
                        selector_expr.clone()
                            * bit.clone()
                            * (bit.clone() - Expression::Constant(Fr::from(1))),
                    );
                    packed = packed + weight * bit;
                }

                //Base-Conv demó: sum 2^i * bit_i - public_amount = 0.
                constraints.push(selector_expr * (packed - public_amount));
                constraints
            },
        );

        PrivateAmountBitsConfig { bits, selector }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> std::result::Result<(), Error> {
        layouter.assign_region(
            || "private amount bit decomposition",
            |mut region| {
                //Az egyetlen region sort aktívvá tesszük
                config.selector.enable(&mut region, 0)?;

                for (index, bit_column) in config.bits.iter().enumerate() {
                    //A witness amount megfelelő bitjét írjuk az advice oszlopba
                    let bit = (self.amount >> index) & 1;
                    region.assign_advice(
                        || format!("bit_{index}"),
                        *bit_column,
                        0,
                        || Value::known(Fr::from(bit)),
                    )?;
                }

                Ok(())
            },
        )
    }
}

//Demo circuit 2 config:
//Egy SMT-vel bizonyítandó anchor cella és sok output, amelyeket UCP lánc zár le.
#[derive(Clone, Debug)]
pub(super) struct SmtAnchorChainConfig<const N: usize> {
    //Anchor: expandált (x - 1)^2 = 0 constraintből lesz unique, SMT segítséggel
    anchor: Column<Advice>,
    //Output lánc: output_i = previous + 1, UCP Assign szabállyal terjed
    outputs: [Column<Advice>; N],
    //A teljes sort aktiváló selector
    selector: Selector,
}

//Demo circuit 2:
//Hibrid példa, ahol egyetlen SMT query után az UCP sok outputot bizonyít unique-nak.
#[derive(Clone, Debug, Default)]
pub(super) struct SmtAnchorChainCircuit<const N: usize> {
    _marker: PhantomData<Fr>,
}

//Demo circuit 3 config:
//Két privát witness egy public commitment/output összegébe van bekötve.
#[derive(Clone, Debug)]
pub(super) struct SecretCommitmentConfig {
    //Valódi titok: nem akarjuk, hogy public inputból exacten kikövetkezzen
    secret: Column<Advice>,
    //Blinding/nonce: ettől a secret önmagában nem lesz meghatározott
    nonce: Column<Advice>,
    //Public-facing output/commitment advice cella, amit constrainednek akarunk látni
    commitment: Column<Advice>,
    //Az egyetlen aktív sort kapcsoló selector
    selector: Selector,
}

//Demo circuit 3:
//A commitment constrained, de a secret és nonce szándékosan több megoldást enged.
#[derive(Clone, Debug)]
pub(super) struct SecretCommitmentCircuit {
    secret: u64,
    nonce: u64,
    _marker: PhantomData<Fr>,
}

impl SecretCommitmentCircuit {
    pub(super) fn new(secret: u64, nonce: u64) -> Self {
        Self {
            secret,
            nonce,
            _marker: PhantomData,
        }
    }

    fn commitment(&self) -> u64 {
        self.secret + self.nonce
    }
}

impl<const N: usize> Circuit<Fr> for SmtAnchorChainCircuit<N> {
    type Config = SmtAnchorChainConfig<N>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        //Az egyetlen nehezebb cella, amit UCP önmagában nem faktorizál
        let anchor = meta.advice_column();
        //A target outputok, amelyek lineárisan függnek az anchortól
        let outputs = array::from_fn(|_| meta.advice_column());
        //Selector: az egy aktív sort kapcsolja
        let selector = meta.selector();

        meta.create_gate(
            "one semantic anchor unlocks a linear derivation chain",
            |meta| {
                let selector_expr = meta.query_selector(selector);
                let anchor_expr = meta.query_advice(anchor, Rotation::cur());
                let mut constraints = Vec::with_capacity(N + 1);

                //Ez szándékosan expandált (anchor - 1)^2 = 0 alak.
                //A lightweight UCP root szabály ezt nem faktorizálja vissza, az SMT viszont
                //be tudja bizonyítani, hogy anchor unique. Ezután az UCP láncban továbbterjed.
                constraints.push(
                    selector_expr.clone()
                        * (anchor_expr.clone() * anchor_expr.clone()
                            - Expression::Constant(Fr::from(2)) * anchor_expr.clone()
                            + Expression::Constant(Fr::from(1))),
                );

                let mut previous = anchor_expr;
                for output_column in outputs.iter() {
                    let output = meta.query_advice(*output_column, Rotation::cur());

                    //Assign rule demó: ha previous unique, akkor output is unique,
                    //és fordítva is tud propagálni a lineáris null-egyenlet miatt.
                    //output0 = anchor + 1
                    //output1 = output0 + 1
                    //output2 = output1 + 1

                    constraints.push(
                        selector_expr.clone()
                            * (output.clone() - previous - Expression::Constant(Fr::from(1))),
                    );
                    previous = output;
                }

                constraints
            },
        );

        SmtAnchorChainConfig {
            anchor,
            outputs,
            selector,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> std::result::Result<(), Error> {
        layouter.assign_region(
            || "smt anchor plus ucp derivation chain",
            |mut region| {
                //Bekapcsoljuk az anchor és lánc constraintjeit
                config.selector.enable(&mut region, 0)?;
                //Anchor witness: a polynomial gyöke, x = 1
                region.assign_advice(
                    || "anchor",
                    config.anchor,
                    0,
                    || Value::known(Fr::from(1)),
                )?;

                for (index, output_column) in config.outputs.iter().enumerate() {
                    //Output witness: 2,3,4,...; mindegyik az előzőből következik
                    region.assign_advice(
                        || format!("output_{index}"),
                        *output_column,
                        0,
                        || Value::known(Fr::from(index as u64 + 2)),
                    )?;
                }

                Ok(())
            },
        )
    }
}

impl Circuit<Fr> for SecretCommitmentCircuit {
    type Config = SecretCommitmentConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(0, 0)
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        //Public input: a commitment értéke, nem maga a secret
        let public_commitment = meta.instance_column();
        //Privát witness cellák
        let secret = meta.advice_column();
        let nonce = meta.advice_column();
        //Output/commitment cella, amelyet targetként ellenőrzünk
        let commitment = meta.advice_column();
        let selector = meta.selector();

        meta.create_gate("secret plus nonce equals public commitment", |meta| {
            let selector_expr = meta.query_selector(selector);
            let public_commitment = meta.query_instance(public_commitment, Rotation::cur());
            let secret = meta.query_advice(secret, Rotation::cur());
            let nonce = meta.query_advice(nonce, Rotation::cur());
            let commitment = meta.query_advice(commitment, Rotation::cur());

            vec![
                //Az output/commitment constrained: commitment = public_commitment.
                selector_expr.clone() * (commitment.clone() - public_commitment),
                //A privát tanúk csak összegként kötöttek: secret + nonce = commitment.
                selector_expr * (secret + nonce - commitment),
            ]
        });

        SecretCommitmentConfig {
            secret,
            nonce,
            commitment,
            selector,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> std::result::Result<(), Error> {
        layouter.assign_region(
            || "secret commitment row",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                region.assign_advice(
                    || "secret",
                    config.secret,
                    0,
                    || Value::known(Fr::from(self.secret)),
                )?;
                region.assign_advice(
                    || "nonce",
                    config.nonce,
                    0,
                    || Value::known(Fr::from(self.nonce)),
                )?;
                region.assign_advice(
                    || "commitment",
                    config.commitment,
                    0,
                    || Value::known(Fr::from(self.commitment())),
                )?;
                Ok(())
            },
        )
    }
}

fn analyzer_input_with_public_amount(amount: i64) -> AnalyzerInput {
    let mut instance_cells = HashMap::new();
    instance_cells.insert("I-0-0".to_string(), amount.into());

    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput {
            instance_cells,
            iterations: 5,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

//A ket publikus osszeg kulon-kulon nem hatarozza meg a titkot.
//Ugyanazon maszk ujrahasznalata viszont a ket egyenletbol visszaallithatova teszi.
//Ez linearis algebrai illusztracio, nem kriptografiai commitment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LinearMaskingMode {
    FirstOnly = 0,
    SecondOnly = 1,
    ReusedMask = 2,
    IndependentMasks = 3,
}

#[derive(Clone, Debug)]
pub(super) struct LinearMaskingCircuit<const MODE: u8> {
    secret: u64,
    first_mask: u64,
    second_mask: u64,
}

#[derive(Clone, Debug)]
pub(super) struct LinearMaskingConfig {
    secret: Column<Advice>,
    first_mask: Column<Advice>,
    second_mask: Column<Advice>,
    first: Selector,
    reused: Selector,
    independent: Selector,
}

impl<const MODE: u8> LinearMaskingCircuit<MODE> {
    pub(super) fn new(secret: u64, first_mask: u64, second_mask: u64) -> Self {
        Self {
            secret,
            first_mask,
            second_mask,
        }
    }

    fn mode() -> LinearMaskingMode {
        match MODE {
            0 => LinearMaskingMode::FirstOnly,
            1 => LinearMaskingMode::SecondOnly,
            2 => LinearMaskingMode::ReusedMask,
            3 => LinearMaskingMode::IndependentMasks,
            _ => panic!("Invalid linear masking mode"),
        }
    }
}

impl<const MODE: u8> Circuit<Fr> for LinearMaskingCircuit<MODE> {
    type Config = LinearMaskingConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(0, 0, 0)
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let secret = meta.advice_column();
        let first_mask = meta.advice_column();
        let second_mask = meta.advice_column();
        let public_a = meta.instance_column();
        let public_b = meta.instance_column();
        let first = meta.selector();
        let reused = meta.selector();
        let independent = meta.selector();

        //A nem publikalt egyenlet kapuja sem kerul be a constraint-rendszerbe.
        if Self::mode() != LinearMaskingMode::SecondOnly {
            meta.create_gate("first masked publication: a = s + r1", |meta| {
                let q = meta.query_selector(first);
                let s = meta.query_advice(secret, Rotation::cur());
                let r1 = meta.query_advice(first_mask, Rotation::cur());
                let a = meta.query_instance(public_a, Rotation::cur());
                vec![q * (s + r1 - a)]
            });
        }
        if matches!(
            Self::mode(),
            LinearMaskingMode::SecondOnly | LinearMaskingMode::ReusedMask
        ) {
            meta.create_gate("reused mask publication: b = 2s + r1", |meta| {
                let q = meta.query_selector(reused);
                let s = meta.query_advice(secret, Rotation::cur());
                let r1 = meta.query_advice(first_mask, Rotation::cur());
                let b = meta.query_instance(public_b, Rotation::cur());
                //Ugyanaz az r1: kivonassal s = b - a, majd r1 = 2a - b.
                vec![q * (Expression::Constant(Fr::from(2)) * s + r1 - b)]
            });
        }
        if Self::mode() == LinearMaskingMode::IndependentMasks {
            meta.create_gate("independent mask publication: b = 2s + r2", |meta| {
                let q = meta.query_selector(independent);
                let s = meta.query_advice(secret, Rotation::cur());
                let r2 = meta.query_advice(second_mask, Rotation::cur());
                let b = meta.query_instance(public_b, Rotation::cur());
                //r2 kulon valtozo, nincs r1 = r2 copy/egyenlosegi kenyszer.
                vec![q * (Expression::Constant(Fr::from(2)) * s + r2 - b)]
            });
        }
        LinearMaskingConfig {
            secret,
            first_mask,
            second_mask,
            first,
            reused,
            independent,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "masked publications",
            |mut region| {
                if Self::mode() != LinearMaskingMode::SecondOnly {
                    config.first.enable(&mut region, 0)?;
                }
                match Self::mode() {
                    LinearMaskingMode::FirstOnly => {}
                    LinearMaskingMode::SecondOnly | LinearMaskingMode::ReusedMask => {
                        config.reused.enable(&mut region, 0)?
                    }
                    LinearMaskingMode::IndependentMasks => {
                        config.independent.enable(&mut region, 0)?
                    }
                }
                region.assign_advice(
                    || "secret",
                    config.secret,
                    0,
                    || Value::known(Fr::from(self.secret)),
                )?;
                region.assign_advice(
                    || "first mask",
                    config.first_mask,
                    0,
                    || Value::known(Fr::from(self.first_mask)),
                )?;
                if Self::mode() == LinearMaskingMode::IndependentMasks {
                    region.assign_advice(
                        || "second mask",
                        config.second_mask,
                        0,
                        || Value::known(Fr::from(self.second_mask)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

//A megfigyeleseket explicit adjuk meg; nem a synthesis privat ertekeibol olvassuk ki.
pub(super) fn linear_masking_input(mode: LinearMaskingMode) -> AnalyzerInput {
    let mut input = analyzer_input_without_public_inputs();
    input.verification_method = VerificationMethod::Specific;
    if mode != LinearMaskingMode::SecondOnly {
        input
            .verification_input
            .instance_cells
            .insert("I-0-0".into(), 100.into());
    }
    if mode != LinearMaskingMode::FirstOnly {
        input
            .verification_input
            .instance_cells
            .insert("I-1-0".into(), 142.into());
    }
    input
}

pub(super) fn linear_masking_targets(mode: LinearMaskingMode) -> Vec<CellId> {
    let count = if mode == LinearMaskingMode::IndependentMasks {
        3
    } else {
        2
    };
    (0..count).map(|column| CellId::advice(column, 0)).collect()
}

fn assert_linear_masking_witness_satisfied<const MODE: u8>(
    circuit: &LinearMaskingCircuit<MODE>,
    input: &AnalyzerInput,
) {
    let instances = (0..2)
        .map(|column| {
            let value = input
                .verification_input
                .instance_cells
                .get(&format!("I-{column}-0"))
                .cloned()
                .unwrap_or_default();
            // This fixture uses small nonnegative public values, checked rather than cast.
            let value = u64::try_from(value).expect("masking fixture public value fits u64");
            vec![Fr::from(value)]
        })
        .collect();
    zcash_halo2_proofs::dev::MockProver::run(4, circuit, instances)
        .unwrap()
        .assert_satisfied();
}

// Algebraic core of the paper's merchant example; monetary range bounds are omitted.
#[derive(Clone, Debug)]
struct PackagePriceCircuit {
    x: u64,
    y: u64,
    z: u64,
}

#[derive(Clone, Debug)]
struct PackagePriceConfig {
    unit_prices: [Column<Advice>; 3],
    first_package: Selector,
    second_package: Selector,
}

impl Circuit<Fr> for PackagePriceCircuit {
    type Config = PackagePriceConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: 0, y: 0, z: 0 }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let unit_prices = array::from_fn(|_| meta.advice_column());
        let public_prices = meta.instance_column();
        let first_package = meta.selector();
        let second_package = meta.selector();

        meta.create_gate("first package: A = 2x + y + z", |meta| {
            let q = meta.query_selector(first_package);
            let [x, y, z] = unit_prices.map(|column| meta.query_advice(column, Rotation::cur()));
            let a = meta.query_instance(public_prices, Rotation::cur());
            vec![q * (Expression::Constant(Fr::from(2)) * x + y + z - a)]
        });
        meta.create_gate("second package: B = 3x + 2y + 2z", |meta| {
            let q = meta.query_selector(second_package);
            let [x, y, z] = unit_prices.map(|column| meta.query_advice(column, Rotation::prev()));
            let b = meta.query_instance(public_prices, Rotation::cur());
            vec![
                q * (Expression::Constant(Fr::from(3)) * x
                    + Expression::Constant(Fr::from(2)) * y
                    + Expression::Constant(Fr::from(2)) * z
                    - b),
            ]
        });
        PackagePriceConfig {
            unit_prices,
            first_package,
            second_package,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "private unit prices and public package prices",
            |mut region| {
                config.first_package.enable(&mut region, 0)?;
                config.second_package.enable(&mut region, 1)?;
                for (column, price) in config.unit_prices.into_iter().zip([self.x, self.y, self.z])
                {
                    region.assign_advice(
                        || "private unit price",
                        column,
                        0,
                        || Value::known(Fr::from(price)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

#[derive(Clone, Debug)]
struct CatalogPackagePriceCircuit {
    prices: PackagePriceCircuit,
}

#[derive(Clone, Debug)]
struct CatalogPackagePriceConfig {
    core: PackagePriceConfig,
    catalog_selector: Selector,
    catalogs: [TableColumn; 2],
}

impl Circuit<Fr> for CatalogPackagePriceCircuit {
    type Config = CatalogPackagePriceConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            prices: self.prices.without_witnesses(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let core = PackagePriceCircuit::configure(meta);
        let catalog_selector = meta.complex_selector();
        let catalogs = array::from_fn(|_| meta.lookup_table_column());
        // Separate lookups impose independent price lists, not a paired table relation.
        for (column, table, default) in [
            (core.unit_prices[1], catalogs[0], 10),
            (core.unit_prices[2], catalogs[1], 20),
        ] {
            meta.lookup(|meta| {
                let q = meta.query_selector(catalog_selector);
                let price = meta.query_advice(column, Rotation::cur());
                let default = Expression::Constant(Fr::from(default));
                vec![(q * (price - default.clone()) + default, table)]
            });
        }
        CatalogPackagePriceConfig {
            core,
            catalog_selector,
            catalogs,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "public unit-price catalogs",
            |mut table| {
                for (row, price) in (10..=90).step_by(10).enumerate() {
                    table.assign_cell(
                        || "Y price",
                        config.catalogs[0],
                        row,
                        || Value::known(Fr::from(price)),
                    )?;
                }
                // Equal table-column heights; duplicates do not add allowed prices.
                for (row, price) in [20, 40, 60].into_iter().cycle().take(9).enumerate() {
                    table.assign_cell(
                        || "Z price",
                        config.catalogs[1],
                        row,
                        || Value::known(Fr::from(price)),
                    )?;
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "private catalog prices and public package prices",
            |mut region| {
                config.core.first_package.enable(&mut region, 0)?;
                config.core.second_package.enable(&mut region, 1)?;
                config.catalog_selector.enable(&mut region, 0)?;
                for (column, price) in config.core.unit_prices.into_iter().zip([
                    self.prices.x,
                    self.prices.y,
                    self.prices.z,
                ]) {
                    region.assign_advice(
                        || "private unit price",
                        column,
                        0,
                        || Value::known(Fr::from(price)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

const RESIDUE_BUCKET_MODULI: [u64; 3] = [3, 5, 7];
const RESIDUE_BUCKET_BOUND: u64 = 105;

#[derive(Clone, Debug)]
struct ResidueBucketsCircuit<const PUBLISHED: usize> {
    secret: u64,
    quotients: [u64; 3],
    remainders: [u64; 3],
}

impl<const PUBLISHED: usize> ResidueBucketsCircuit<PUBLISHED> {
    fn new(secret: u64) -> Self {
        Self {
            secret,
            quotients: RESIDUE_BUCKET_MODULI.map(|modulus| secret / modulus),
            remainders: RESIDUE_BUCKET_MODULI.map(|modulus| secret % modulus),
        }
    }
}

#[derive(Clone, Debug)]
struct ResidueBucketsConfig {
    secret: Column<Advice>,
    quotients: [Column<Advice>; 3],
    remainders: [Column<Advice>; 3],
    public: Column<Instance>,
    selector: Selector,
    tables: [TableColumn; 7],
}

impl<const PUBLISHED: usize> Circuit<Fr> for ResidueBucketsCircuit<PUBLISHED> {
    type Config = ResidueBucketsConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(0)
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        assert!(PUBLISHED <= RESIDUE_BUCKET_MODULI.len());
        let secret = meta.advice_column();
        let quotients = array::from_fn(|_| meta.advice_column());
        let remainders = array::from_fn(|_| meta.advice_column());
        let public = meta.instance_column();
        meta.enable_equality(public);
        for column in remainders {
            meta.enable_equality(column);
        }
        let selector = meta.complex_selector();
        let tables = array::from_fn(|_| meta.lookup_table_column());
        for (index, modulus) in RESIDUE_BUCKET_MODULI.into_iter().enumerate() {
            meta.create_gate("bounded quotient and remainder", |meta| {
                let q = meta.query_selector(selector);
                let x = meta.query_advice(secret, Rotation::cur());
                let quotient = meta.query_advice(quotients[index], Rotation::cur());
                let remainder = meta.query_advice(remainders[index], Rotation::cur());
                vec![q * (x - Expression::Constant(Fr::from(modulus)) * quotient - remainder)]
            });
        }
        let columns = [
            secret,
            quotients[0],
            quotients[1],
            quotients[2],
            remainders[0],
            remainders[1],
            remainders[2],
        ];
        // Independent memberships, not tuples that correlate the seven table columns.
        for (column, table) in columns.into_iter().zip(tables) {
            meta.lookup(|meta| {
                let q = meta.query_selector(selector);
                let value = meta.query_advice(column, Rotation::cur());
                vec![(q * value, table)]
            });
        }
        ResidueBucketsConfig {
            secret,
            quotients,
            remainders,
            public,
            selector,
            tables,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "bounded integer division ranges",
            |mut table| {
                for row in 0..RESIDUE_BUCKET_BOUND {
                    let values = [
                        row,
                        row % (RESIDUE_BUCKET_BOUND / 3),
                        row % (RESIDUE_BUCKET_BOUND / 5),
                        row % (RESIDUE_BUCKET_BOUND / 7),
                        row % 3,
                        row % 5,
                        row % 7,
                    ];
                    // Repeated entries give all columns equal height without changing their sets.
                    for (column, value) in config.tables.into_iter().zip(values) {
                        table.assign_cell(
                            || "allowed integer value",
                            column,
                            row as usize,
                            || Value::known(Fr::from(value)),
                        )?;
                    }
                }
                Ok(())
            },
        )?;
        let remainder_cells = layouter.assign_region(
            || "private input and bounded divisions",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                region.assign_advice(
                    || "private input x",
                    config.secret,
                    0,
                    || Value::known(Fr::from(self.secret)),
                )?;
                for (column, value) in config.quotients.into_iter().zip(self.quotients) {
                    region.assign_advice(
                        || "private quotient",
                        column,
                        0,
                        || Value::known(Fr::from(value)),
                    )?;
                }
                let mut cells = Vec::new();
                for (column, value) in config.remainders.into_iter().zip(self.remainders) {
                    cells.push(region.assign_advice(
                        || "remainder, published only when selected",
                        column,
                        0,
                        || Value::known(Fr::from(value)),
                    )?);
                }
                Ok(cells)
            },
        )?;
        for (row, cell) in remainder_cells.iter().take(PUBLISHED).enumerate() {
            layouter.constrain_instance(cell.cell(), config.public, row)?;
        }
        Ok(())
    }
}

fn analyzer_input_without_public_inputs() -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::None,
        verification_input: VerificationInput {
            instance_cells: HashMap::new(),
            iterations: 5,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn run_analyzer_only<C: Circuit<Fr>>(
    circuit: &C,
    k: u32,
    analyzer_input: &AnalyzerInput,
) -> (AnalyzerOutputStatus, Duration) {
    let start = Instant::now();
    let mut analyzer = Analyzer::<Fr>::new(
        circuit,
        k,
        AnalyzerType::UnderconstrainedCircuit,
        Some(analyzer_input),
    )
    .unwrap();
    let output = analyzer.analyze_underconstrained(analyzer_input).unwrap();

    (output.output_status, start.elapsed())
}

fn speedup(analyzer_duration: Duration, pipeline_duration: Duration) -> f64 {
    let pipeline_seconds = pipeline_duration.as_secs_f64().max(0.000_001);
    analyzer_duration.as_secs_f64() / pipeline_seconds
}

fn bit_targets<const N: usize>() -> Vec<CellId> {
    (0..N).map(|column| CellId::advice(column, 0)).collect()
}

fn chain_output_targets<const N: usize>() -> Vec<CellId> {
    (0..N).map(|index| CellId::advice(index + 1, 0)).collect()
}

// Demo 1:
// Hasznos circuit: egy privát amount bitjeit bizonyítjuk booleannek, majd
// összepakoljuk őket egy public amount értékbe.
//
// Miért csúcspont?
//   - extractor kiszedi a Halo2 gate-eket és a selector értéket,
//   - Fig. 10 Root megtanulja, hogy minden bit {0,1},
//   - Base-Conv uniqueness/value inference összeköti a biteket a public amounttal,
//   - ezért a pipeline tisztán UCP-vel zár, SMT query nélkül.
#[test]
fn demo_private_amount_bits_ucp_beats_analyzer_only() {
    const N: usize = 8;
    let amount = 173_u64;
    let circuit = PrivateAmountBitsCircuit::<N>::new(amount);
    let analyzer_input = analyzer_input_with_public_amount(amount as i64);
    let targets = bit_targets::<N>();

    let (analyzer_status, analyzer_duration) = run_analyzer_only(&circuit, 5, &analyzer_input);

    let pipeline_start = Instant::now();
    let pipeline_output = analyze_underconstrained_with_ucp::<Fr, _, _>(
        &circuit,
        5,
        &analyzer_input,
        targets.clone(),
    )
    .unwrap();
    let pipeline_duration = pipeline_start.elapsed();

    println!(
        "Public amount={amount}; {N} private bits: {:?}; SMT uniqueness queries: {}; elapsed: {:.2?}\nSMT-only: {:?}; elapsed: {:.2?}; single-run speedup: {:.2}x (not a benchmark)",
        pipeline_output.status, pipeline_output.semantic_queries, pipeline_duration,
        analyzer_status, analyzer_duration, speedup(analyzer_duration, pipeline_duration)
    );
    if demo_verbose() {
        println!(
            "Unresolved targets: {:?}; learned domains: {:?}",
            pipeline_output.target_check.unresolved_targets,
            pipeline_output.ucp_result.value_facts.domains()
        );
    }

    assert_eq!(
        analyzer_status,
        AnalyzerOutputStatus::NotUnderconstrainedLocal
    );
    assert_eq!(
        pipeline_output.status,
        UcpAnalyzerPipelineStatus::VerifiedByUcp
    );
    assert!(!pipeline_output.used_smt);
    assert_eq!(pipeline_output.semantic_queries, 0);
    assert!(pipeline_output.target_check.all_targets_unique());
    for target in targets {
        assert!(pipeline_output.ucp_result.facts.is_unique(&target));
    }
}

// Demo 3:
// Valódi ZK-szerű helyzet: a public commitment/output constrained, de a secret
// és nonce külön-külön nem következtethető ki. Ez nem hiba, hanem a privát input
// lényege: a target output determinált, a witness titkos része több megoldást enged.
#[test]
fn demo_secret_remains_private_while_commitment_output_is_constrained() {
    let circuit = SecretCommitmentCircuit::new(42, 58);
    let analyzer_input = analyzer_input_with_public_amount(circuit.commitment() as i64);
    let secret = CellId::advice(0, 0);
    let nonce = CellId::advice(1, 0);
    let commitment = CellId::advice(2, 0);

    let pipeline_start = Instant::now();
    let pipeline_output = analyze_underconstrained_with_ucp::<Fr, _, _>(
        &circuit,
        4,
        &analyzer_input,
        [commitment.clone()],
    )
    .unwrap();
    let pipeline_duration = pipeline_start.elapsed();

    println!(
        "Public sum=100: {:?}; elapsed: {:.2?}; SMT uniqueness queries: {}\nProven unique: output={}; secret={}; nonce={}",
        pipeline_output.status,
        pipeline_duration,
        pipeline_output.semantic_queries,
        pipeline_output.ucp_result.facts.is_unique(&commitment),
        pipeline_output.ucp_result.facts.is_unique(&secret),
        pipeline_output.ucp_result.facts.is_unique(&nonce),
    );
    if demo_verbose() {
        println!(
            "Known values: {:?}",
            pipeline_output.ucp_result.value_facts.known_values()
        );
    }

    assert_eq!(
        pipeline_output.status,
        UcpAnalyzerPipelineStatus::VerifiedByUcp
    );
    assert!(pipeline_output.target_check.all_targets_unique());
    assert!(pipeline_output.ucp_result.facts.is_unique(&commitment));

    //A secret és nonce nem unique-k: public commitmentből csak az összegük ismert.
    assert!(!pipeline_output.ucp_result.facts.is_unique(&secret));
    assert!(!pipeline_output.ucp_result.facts.is_unique(&nonce));
    assert!(pipeline_output
        .ucp_result
        .value_facts
        .known_value(&secret)
        .is_none());
    assert!(pipeline_output
        .ucp_result
        .value_facts
        .known_value(&nonce)
        .is_none());
}

// Demo 2:
// Hibrid circuit: egy expandált négyzetgyök-szerű anchor SMT-t igényel, de
// utána hosszú lineáris output-lánc záródik UCP-vel.
//
// Miért csúcspont?
//   - a sima analyzer az egész rendszert SMT-vel vizsgálja,
//   - a pipeline csak egy cellára kérdez rá,
//   - az SMT által tanult egyetlen unique cella bekerül K-ba,
//   - majd a Fig. 8/10 Assign propagáció lezárja az összes output targetet.
//A bizonyitott SMT modellertet Delta is megkapja: anchor=1, outputok=2,3,... lesznek Exact-ek.
#[test]
fn demo_one_smt_query_then_ucp_closes_many_outputs() {
    const N: usize = 12;
    let circuit = SmtAnchorChainCircuit::<N>::default();
    let analyzer_input = analyzer_input_without_public_inputs();
    let targets = chain_output_targets::<N>();

    let (analyzer_status, analyzer_duration) = run_analyzer_only(&circuit, 5, &analyzer_input);

    let pipeline_start = Instant::now();
    let pipeline_output = analyze_underconstrained_with_ucp::<Fr, _, _>(
        &circuit,
        5,
        &analyzer_input,
        targets.clone(),
    )
    .unwrap();
    let pipeline_duration = pipeline_start.elapsed();

    println!(
        "SMT anchor, then {N} UCP outputs: {:?}; SMT uniqueness queries: {}; elapsed: {:.2?}\nSMT-only: {:?}; elapsed: {:.2?}; single-run speedup: {:.2}x (not a benchmark)",
        pipeline_output.status, pipeline_output.semantic_queries, pipeline_duration,
        analyzer_status, analyzer_duration, speedup(analyzer_duration, pipeline_duration)
    );
    if demo_verbose() {
        println!(
            "SMT-learned cells: {:?}; unresolved targets: {:?}; recovered values: {:?}",
            pipeline_output.smt_learned_cells,
            pipeline_output.target_check.unresolved_targets,
            pipeline_output.ucp_result.value_facts.known_values()
        );
    }

    assert_eq!(
        analyzer_status,
        AnalyzerOutputStatus::NotUnderconstrainedLocal
    );
    assert_eq!(
        pipeline_output.status,
        UcpAnalyzerPipelineStatus::VerifiedBySmt
    );
    assert!(pipeline_output.used_smt);
    assert_eq!(pipeline_output.semantic_queries, 1);
    assert!(pipeline_output.target_check.all_targets_unique());
    assert_eq!(
        pipeline_output
            .ucp_result
            .value_facts
            .known_value(&CellId::advice(0, 0)),
        Some(&num_bigint::BigInt::from(1)),
    );
    for (index, target) in targets.into_iter().enumerate() {
        assert!(pipeline_output.ucp_result.facts.is_unique(&target));
        assert_eq!(
            pipeline_output.ucp_result.value_facts.known_value(&target),
            Some(&num_bigint::BigInt::from(index + 2)),
        );
    }
}

//A privat bemeneteket kulon kijeloljuk: az output constrainedsege nem mondja meg,
//hogy a titkok is visszaallithatok-e. A riport mindket esetben ellenorzi a SAT-ot.
#[test]
fn demo_privacy_report_separates_recovered_bits_from_ambiguous_secrets() {
    const N: usize = 8;
    let amount = 173;
    let exposed = analyze_private_recoverability::<Fr, _, _>(
        &PrivateAmountBitsCircuit::<N>::new(amount),
        5,
        &analyzer_input_with_public_amount(amount as i64),
        bit_targets::<N>(),
        PrivacyAnalysisOptions::fast_probe_only(),
    )
    .unwrap();
    print_privacy_demo("Public amount=173 exposes all private bits:", &exposed);
    assert_eq!(exposed.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(exposed.summary.exact_values, N);
    assert_eq!(exposed.summary.refined_domains, 0);
    assert!(!exposed.structural_baseline_computed);
    assert_eq!(exposed.semantic_queries, 0);
    for (index, cell) in exposed.cells.iter().enumerate() {
        let expected = num_bigint::BigInt::from((amount >> index) & 1);
        assert_eq!(
            cell.domain,
            Some(super::value::UcpValueDomain::exact(expected))
        );
    }

    //Masodik, fuggetlen futas: egyetlen megtanult bitet sem adunk be feltetelnek.
    let validated = validate_private_recovery_report::<Fr, _>(
        &PrivateAmountBitsCircuit::<N>::new(amount),
        5,
        &analyzer_input_with_public_amount(amount as i64),
        &exposed,
    )
    .unwrap();
    print_validation_demo("Independent check of the recovered bits:", &validated);
    assert_eq!(validated.status, RecoveryValidationStatus::VerifiedDomains);
    assert_eq!(validated.domain_queries, N);

    //Ez csak egy osszeges illusztracio, nem kriptografiai commitment vagy ZK-bizonyitas.
    //100 = secret + nonce tobb megoldast enged; a synthesisbeli 42 es 58 nem Delta-teny.
    let ambiguous = analyze_private_recoverability::<Fr, _, _>(
        &SecretCommitmentCircuit::new(42, 58),
        4,
        &analyzer_input_with_public_amount(100),
        [CellId::advice(0, 0), CellId::advice(1, 0)],
        PrivacyAnalysisOptions::fast_probe_only(),
    )
    .unwrap();
    print_privacy_demo(
        "Public sum=100 does not determine its private operands:",
        &ambiguous,
    );
    assert_eq!(ambiguous.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(ambiguous.summary.exact_values, 0);
    assert_eq!(ambiguous.summary.non_unique_cells, 2);
    assert!(ambiguous.cells.iter().all(|cell| {
        cell.uniqueness == PrivateCellUniqueness::NonUnique && cell.domain.is_none()
    }));
    let validated = validate_private_recovery_report::<Fr, _>(
        &SecretCommitmentCircuit::new(42, 58),
        4,
        &analyzer_input_with_public_amount(100),
        &ambiguous,
    )
    .unwrap();
    assert_eq!(validated.status, RecoveryValidationStatus::NoDomainClaims);
}

//Negativ kontroll: ha a riport egyik visszaallitott bitjet elrontjuk,
//a fuggetlen SMT ellenorzest ez nem tevesztheti meg.
#[test]
fn demo_independent_validation_detects_a_wrong_recovered_bit() {
    let circuit = PrivateAmountBitsCircuit::<4>::new(13);
    let input = analyzer_input_with_public_amount(13);
    let mut report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        bit_targets::<4>(),
        PrivacyAnalysisOptions::fast_probe_only(),
    )
    .unwrap();
    report.cells[0].domain = Some(super::value::UcpValueDomain::exact(
        num_bigint::BigInt::from(0),
    ));
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    print_validation_demo("A false recovered bit is refuted:", &validation);
    assert_eq!(validation.status, RecoveryValidationStatus::Refuted);
    assert_eq!(
        validation.cells[0].counterexample,
        Some(num_bigint::BigInt::from(1))
    );
    //A hibas allitas nem szennyezheti a tobbi bit ellenorzeset.
    assert!(validation.cells[1..].iter().all(|cell| {
        cell.status == super::privacy_validation::DomainValidationStatus::Entailed
    }));
}

#[test]
fn demo_independent_validation_can_use_a_separate_timeout() {
    let circuit = PrivateAmountBitsCircuit::<4>::new(13);
    let input = analyzer_input_with_public_amount(13);
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        bit_targets::<4>(),
        PrivacyAnalysisOptions {
            solver_timeout_ms: Some(2_000),
            ..PrivacyAnalysisOptions::fast_probe_only()
        },
    )
    .unwrap();
    let inherited =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    assert_eq!(inherited.solver_timeout_ms, Some(2_000));
    assert_eq!(inherited.status, RecoveryValidationStatus::VerifiedDomains);
    let longer = validate_private_recovery_report_with_timeout::<Fr, _>(
        &circuit,
        4,
        &input,
        &report,
        Some(30_000),
    )
    .unwrap();
    assert_eq!(longer.solver_timeout_ms, Some(30_000));
    assert_eq!(longer.status, inherited.status);
    assert_eq!(longer.domain_queries, inherited.domain_queries);
    assert_eq!(report.options.solver_timeout_ms, Some(2_000));
    for (before, after) in inherited.cells.iter().zip(&longer.cells) {
        assert_eq!(before.cell, after.cell);
        assert_eq!(before.status, after.status);
        assert_eq!(before.counterexample, after.counterexample);
    }
    assert!(validate_private_recovery_report_with_timeout::<Fr, _>(
        &circuit,
        4,
        &input,
        &report,
        Some(0),
    )
    .is_err());
}

#[test]
fn demo_package_prices_recover_one_private_unit_price() {
    let circuit = PackagePriceCircuit {
        x: 100,
        y: 30,
        z: 70,
    };
    let alternate = PackagePriceCircuit {
        x: 100,
        y: 40,
        z: 60,
    };
    let instances = || vec![vec![Fr::from(300), Fr::from(500)]];
    for witness in [&circuit, &alternate] {
        zcash_halo2_proofs::dev::MockProver::run(4, witness, instances())
            .unwrap()
            .assert_satisfied();
    }
    let wrong = PackagePriceCircuit {
        x: 101,
        ..circuit.clone()
    };
    assert!(
        zcash_halo2_proofs::dev::MockProver::run(4, &wrong, instances())
            .unwrap()
            .verify()
            .is_err()
    );
    for prices in [[301, 500], [300, 501]] {
        assert!(zcash_halo2_proofs::dev::MockProver::run(
            4,
            &circuit,
            vec![prices.into_iter().map(Fr::from).collect()],
        )
        .unwrap()
        .verify()
        .is_err());
    }

    let input = AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new(
            [("I-0-0".into(), 300), ("I-0-1".into(), 500)],
            1,
        ),
        lookup_method: LookupMethod::InlineConstraints,
    };
    let targets = [
        CellId::advice(0, 0),
        CellId::advice(1, 0),
        CellId::advice(2, 0),
    ];
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        targets.clone(),
        PrivacyAnalysisOptions::fast_probe_only(),
    )
    .unwrap();
    print_privacy_demo(
        "Package prices: A=2x+y+z=300, B=3x+2y+2z=500; x=2A-B=100:",
        &report,
    );
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.exact_values, 1);
    assert_eq!(report.summary.unique_cells, 1);
    assert_eq!(report.summary.non_unique_cells, 2);
    assert_eq!(report.cells[0].cell, targets[0]);
    assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
    assert_eq!(
        report.cells[0].domain,
        Some(UcpValueDomain::exact(100.into()))
    );
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.baseline_domain.is_none()));
    for (cell, target) in report.cells[1..].iter().zip(&targets[1..]) {
        assert_eq!(&cell.cell, target);
        assert_eq!(cell.uniqueness, PrivateCellUniqueness::NonUnique);
        assert!(cell.domain.is_none());
    }

    // Az elimináció a teljes tanú egyértelműsége nélkül is elkülöníti x értékét.
    let propagated = analyze_private_recoverability::<Fr, _, _>(
        &alternate,
        4,
        &input,
        [targets[0].clone()],
        PrivacyAnalysisOptions {
            max_semantic_queries: 0,
            ..PrivacyAnalysisOptions::fast_probe_only()
        },
    )
    .unwrap();
    assert_eq!(propagated.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(propagated.semantic_queries, 0);
    assert_eq!(propagated.summary.exact_values, 1);
    assert_eq!(
        propagated.cells[0].uniqueness,
        PrivateCellUniqueness::Unique
    );
    assert_eq!(
        propagated.cells[0].domain,
        Some(UcpValueDomain::exact(100.into()))
    );

    let recovered_again = analyze_private_recoverability::<Fr, _, _>(
        &alternate,
        4,
        &input,
        [targets[0].clone()],
        PrivacyAnalysisOptions::fast_probe_only(),
    )
    .unwrap();
    assert_eq!(recovered_again.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(recovered_again.cells[0].domain, report.cells[0].domain);
    assert_eq!(
        recovered_again.cells[0].uniqueness,
        PrivateCellUniqueness::Unique
    );
    assert_eq!(recovered_again.semantic_queries, 0);

    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    print_validation_demo(
        "Independent check of the recovered unit price:",
        &validation,
    );
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
    assert_eq!(validation.domain_queries, 1);
}

#[test]
fn demo_package_price_catalogs_recover_x_and_restrict_y() {
    let circuit = CatalogPackagePriceCircuit {
        prices: PackagePriceCircuit {
            x: 100,
            y: 40,
            z: 60,
        },
    };
    let instances = || vec![vec![Fr::from(300), Fr::from(500)]];
    // Every remaining Y candidate has a full satisfying witness under the same observations.
    for (y, z) in [(40, 60), (60, 40), (80, 20)] {
        let witness = CatalogPackagePriceCircuit {
            prices: PackagePriceCircuit { x: 100, y, z },
        };
        zcash_halo2_proofs::dev::MockProver::run(5, &witness, instances())
            .unwrap()
            .assert_satisfied();
    }
    // The first two witnesses satisfy their package equations but violate one catalog each.
    for (prices, public) in [
        (
            PackagePriceCircuit {
                x: 100,
                y: 15,
                z: 20,
            },
            [235, 370],
        ),
        (
            PackagePriceCircuit {
                x: 100,
                y: 50,
                z: 50,
            },
            [300, 500],
        ),
        (
            PackagePriceCircuit {
                x: 101,
                y: 40,
                z: 60,
            },
            [300, 500],
        ),
        (circuit.prices.clone(), [301, 500]),
        (circuit.prices.clone(), [300, 501]),
    ] {
        assert!(zcash_halo2_proofs::dev::MockProver::run(
            5,
            &CatalogPackagePriceCircuit { prices },
            vec![public.into_iter().map(Fr::from).collect()],
        )
        .unwrap()
        .verify()
        .is_err());
    }

    let input = AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new(
            [("I-0-0".into(), 300), ("I-0-1".into(), 500)],
            1,
        ),
        lookup_method: LookupMethod::InlineConstraints,
    };
    let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
    let options = PrivacyAnalysisOptions {
        compute_structural_baseline: true,
        max_semantic_queries: 16,
        solver_timeout_ms: Some(2_000),
        domain_refinement: super::privacy_domain::PrivacyDomainRefinementOptions {
            max_solver_checks: 64,
            max_candidates_per_cell: 16,
        },
        ..PrivacyAnalysisOptions::fast_probe_only()
    };
    println!(
        "Public packages: A=300, B=500; Y catalog={:?}; Z catalog={:?}",
        [10, 20, 30, 40, 50, 60, 70, 80, 90],
        [20, 40, 60]
    );
    let propagated = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        5,
        &input,
        targets.clone(),
        PrivacyAnalysisOptions {
            max_semantic_queries: 0,
            domain_refinement: Default::default(),
            ..options
        },
    )
    .unwrap();
    print_privacy_demo(
        "Catalog package prices: propagation-only recovery:",
        &propagated,
    );
    // Catalog domains enable stronger UCP deductions than the unrestricted merchant example.
    assert_eq!(propagated.status, PrivacyAnalysisStatus::QueryLimitReached);
    assert_eq!(propagated.semantic_queries, 0);
    assert_eq!(propagated.domain_refinement_statistics.solver_checks, 0);
    assert_eq!(propagated.domain_discovery_statistics.solver_checks, 0);
    assert_eq!(
        propagated.cells[0].domain,
        Some(UcpValueDomain::exact(100.into()))
    );
    assert_eq!(
        propagated.cells[0].uniqueness,
        PrivateCellUniqueness::Unique
    );
    assert_eq!(
        propagated.cells[1].domain,
        UcpValueDomain::finite_set([40, 60, 80].map(num_bigint::BigInt::from))
    );
    assert_eq!(
        propagated.cells[1].uniqueness,
        PrivateCellUniqueness::Unknown
    );
    assert!(!propagated.cells[1].domain_is_complete);

    let report =
        analyze_private_recoverability::<Fr, _, _>(&circuit, 5, &input, targets.clone(), options)
            .unwrap();
    print_privacy_demo(
        "Catalog package prices: recover x=100 and narrow Y from nine prices to {40,60,80}:",
        &report,
    );
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.exact_values, 1);
    assert_eq!(report.summary.finite_domains, 1);
    assert_eq!(report.summary.unique_cells, 1);
    assert_eq!(report.summary.non_unique_cells, 1);
    assert!(report.domain_refinement_statistics.solver_checks > 0);
    let [x, y] = report.cells.as_slice() else {
        panic!("Expected exactly the selected private prices x and y");
    };
    assert_eq!(x.cell, targets[0]);
    assert_eq!(x.domain, Some(UcpValueDomain::exact(100.into())));
    assert_eq!(x.uniqueness, PrivateCellUniqueness::Unique);
    assert!(x.domain_is_complete);
    assert!(x.baseline_domain.is_none());
    assert_eq!(y.cell, targets[1]);
    assert_eq!(
        y.baseline_domain,
        UcpValueDomain::finite_set((10..=90).step_by(10).map(num_bigint::BigInt::from))
    );
    assert_eq!(
        y.domain,
        UcpValueDomain::finite_set([40, 60, 80].map(num_bigint::BigInt::from))
    );
    assert_eq!(y.uniqueness, PrivateCellUniqueness::NonUnique);
    assert!(y.domain_refined_from_baseline);
    assert!(y.domain_is_complete);

    let alternate = CatalogPackagePriceCircuit {
        prices: PackagePriceCircuit {
            x: 100,
            y: 80,
            z: 20,
        },
    };
    let recovered_again =
        analyze_private_recoverability::<Fr, _, _>(&alternate, 5, &input, targets, options)
            .unwrap();
    assert_eq!(recovered_again.status, report.status);
    for (first, second) in report.cells.iter().zip(&recovered_again.cells) {
        assert_eq!(first.cell, second.cell);
        assert_eq!(first.domain, second.domain);
        assert_eq!(first.uniqueness, second.uniqueness);
        assert_eq!(first.domain_is_complete, second.domain_is_complete);
    }

    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 5, &input, &report).unwrap();
    print_validation_demo(
        "Independent check of the exact price and covering domain:",
        &validation,
    );
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
    assert_eq!(validation.domain_queries, 2);

    let mut false_report = report;
    false_report.cells[1].domain =
        UcpValueDomain::finite_set([40, 60].map(num_bigint::BigInt::from));
    let refuted =
        validate_private_recovery_report::<Fr, _>(&circuit, 5, &input, &false_report).unwrap();
    assert_eq!(refuted.status, RecoveryValidationStatus::Refuted);
    assert_eq!(refuted.cells[1].counterexample, Some(80.into()));
}

#[test]
fn demo_residue_buckets_combine_partial_domains_into_exact_recovery() {
    fn check<const PUBLISHED: usize>(validation_timeout_ms: Option<u64>) -> PrivacyAnalysisStatus {
        let circuit = ResidueBucketsCircuit::<PUBLISHED>::new(68);
        let observations = [2_u64, 3, 5];
        let instances = || {
            vec![observations[..PUBLISHED]
                .iter()
                .copied()
                .map(Fr::from)
                .collect()]
        };
        // This bounded enumeration is the test oracle, never an analyzer premise.
        let expected: Vec<_> = (0..RESIDUE_BUCKET_BOUND)
            .filter(|value| {
                RESIDUE_BUCKET_MODULI
                    .iter()
                    .zip(observations)
                    .take(PUBLISHED)
                    .all(|(modulus, remainder)| value % modulus == remainder)
            })
            .collect();
        assert_eq!(expected.len(), [105, 35, 7, 1][PUBLISHED]);
        for value in 0..RESIDUE_BUCKET_BOUND {
            let accepted = zcash_halo2_proofs::dev::MockProver::run(
                7,
                &ResidueBucketsCircuit::<PUBLISHED>::new(value),
                instances(),
            )
            .unwrap()
            .verify()
            .is_ok();
            assert_eq!(accepted, expected.contains(&value));
        }
        for row in 0..PUBLISHED {
            let mut wrong = instances();
            wrong[0][row] = Fr::from((observations[row] + 1) % RESIDUE_BUCKET_MODULI[row]);
            assert!(zcash_halo2_proofs::dev::MockProver::run(7, &circuit, wrong)
                .unwrap()
                .verify()
                .is_err());
        }
        if PUBLISHED == 0 {
            let mut bad_remainder = circuit.clone();
            // Preserve x=3q+r, but violate r<3 while keeping the quotient in range.
            bad_remainder.quotients[0] -= 1;
            bad_remainder.remainders[0] += 3;
            assert!(
                zcash_halo2_proofs::dev::MockProver::run(7, &bad_remainder, instances())
                    .unwrap()
                    .verify()
                    .is_err()
            );
            assert!(zcash_halo2_proofs::dev::MockProver::run(
                7,
                &ResidueBucketsCircuit::<PUBLISHED>::new(105),
                instances(),
            )
            .unwrap()
            .verify()
            .is_err());
        }

        let input = AnalyzerInput {
            verification_method: if PUBLISHED == 0 {
                VerificationMethod::None
            } else {
                VerificationMethod::Specific
            },
            verification_input: VerificationInput::new(
                observations
                    .iter()
                    .take(PUBLISHED)
                    .enumerate()
                    .map(|(row, value)| (format!("I-0-{row}"), *value)),
                1,
            ),
            lookup_method: LookupMethod::InlineConstraints,
        };
        let target = CellId::advice(0, 0);
        let expected_domain =
            UcpValueDomain::finite_set(expected.iter().copied().map(num_bigint::BigInt::from))
                .unwrap();
        let propagation_options = PrivacyAnalysisOptions {
            max_semantic_queries: 0,
            solver_timeout_ms: Some(2_000),
            ..PrivacyAnalysisOptions::fast_probe_only()
        };
        let propagate = |witness: &ResidueBucketsCircuit<PUBLISHED>| {
            let analyzable =
                crate::circuit_analyzer::analyzable::Analyzable::<Fr>::config_and_synthesize(
                    witness, 7,
                )
                .unwrap();
            let problem = super::extractor::extract_ucp_problem(&analyzable);
            let mut values = problem.initial_value_facts.clone();
            for (row, value) in observations.iter().take(PUBLISHED).enumerate() {
                values.mark_known(CellId::instance(0, row as i32), (*value).into());
            }
            problem.analyze_with_values(problem.initial_facts.clone(), values)
        };
        // MockProver establishes fixture satisfiability; this kernel check is not an API report.
        let propagated = propagate(&circuit);
        println!(
            "CRT buckets: {PUBLISHED} public remainders; UCP kernel: {}",
            short_demo_domain(propagated.value_facts.domain(&target))
        );
        assert_eq!(
            propagated.value_facts.domain(&target),
            Some(&expected_domain)
        );
        assert_eq!(propagated.facts.is_unique(&target), PUBLISHED == 3);
        if let Some(other) = expected.iter().copied().find(|value| *value != 68) {
            let alternate = propagate(&ResidueBucketsCircuit::<PUBLISHED>::new(other));
            assert_eq!(
                alternate.value_facts.domain(&target),
                propagated.value_facts.domain(&target)
            );
            assert_eq!(
                alternate.facts.is_unique(&target),
                propagated.facts.is_unique(&target)
            );
        }

        let options = PrivacyAnalysisOptions {
            max_semantic_queries: 8,
            search: super::privacy::PrivacySearchOptions {
                max_bridge_queries: 0,
                max_retries_per_target: 0,
                retry_solver_timeout_ms: None,
                ..Default::default()
            },
            domain_refinement: super::privacy_domain::PrivacyDomainRefinementOptions {
                // The no-publication control need not re-enumerate the entire known input range.
                max_solver_checks: if PUBLISHED == 0 { 0 } else { 64 },
                max_candidates_per_cell: RESIDUE_BUCKET_BOUND as usize,
            },
            ..propagation_options
        };
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            7,
            &input,
            [target.clone()],
            options,
        )
        .unwrap();
        print_privacy_demo(
            &format!(
                "CRT buckets: {PUBLISHED} public remainders, expected {} feasible inputs:",
                expected.len()
            ),
            &report,
        );
        let status = report.status;
        if report.ucp_result.is_none() {
            assert_eq!(status, PrivacyAnalysisStatus::SolverUnknown);
            assert!(report.cells.iter().all(|cell| {
                cell.domain.is_none() && cell.uniqueness == PrivateCellUniqueness::Unknown
            }));
            println!("CRT buckets: {PUBLISHED} public remainders; initial SAT incomplete");
            return status;
        }
        assert_ne!(status, PrivacyAnalysisStatus::Inconsistent);
        assert_eq!(report.cells.len(), 1);
        assert_eq!(report.cells[0].cell, target);
        assert_eq!(report.cells[0].domain.as_ref(), Some(&expected_domain));
        assert!(!report.structural_baseline_computed);
        assert!(report.cells[0].baseline_domain.is_none());
        if PUBLISHED == 3 {
            assert_eq!(status, PrivacyAnalysisStatus::Analyzed);
            assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
            assert!(report.cells[0].domain_is_complete);
            assert_eq!(report.semantic_queries, 0);
        } else {
            assert_ne!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
            if report.cells[0].domain_is_complete {
                assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
            }
        }

        match validate_private_recovery_report_with_timeout::<Fr, _>(
            &circuit,
            7,
            &input,
            &report,
            validation_timeout_ms,
        ) {
            Ok(validation) => {
                print_validation_demo("Fresh check of the CRT covering domain:", &validation);
                assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
                assert_eq!(validation.domain_queries, 1);
                assert_eq!(
                    validation.solver_timeout_ms,
                    validation_timeout_ms.or(report.options.solver_timeout_ms)
                );
            }
            Err(error)
                if error
                    .downcast_ref::<crate::smt_solver::smt_parser::UnknownSolverResult>()
                    .is_some() =>
            {
                println!(
                    "CRT buckets: {PUBLISHED} public remainders; validation incomplete: {error:#}"
                );
            }
            Err(error) => panic!("CRT validation failed: {error:#}"),
        }

        if PUBLISHED >= 2 {
            let mut false_report = report;
            false_report.cells[0].domain = if PUBLISHED == 3 {
                Some(UcpValueDomain::exact(67.into()))
            } else {
                UcpValueDomain::finite_set(
                    expected
                        .iter()
                        .copied()
                        .filter(|value| *value != 68)
                        .map(num_bigint::BigInt::from),
                )
            };
            match validate_private_recovery_report_with_timeout::<Fr, _>(
                &circuit,
                7,
                &input,
                &false_report,
                validation_timeout_ms,
            ) {
                Ok(refuted) => {
                    print_validation_demo(
                        "Fresh check of an intentionally false CRT domain:",
                        &refuted,
                    );
                    assert_eq!(refuted.status, RecoveryValidationStatus::Refuted);
                    assert_eq!(refuted.cells[0].counterexample, Some(68.into()));
                }
                Err(error)
                    if error
                        .downcast_ref::<crate::smt_solver::smt_parser::UnknownSolverResult>()
                        .is_some() =>
                {
                    println!("CRT buckets: false-domain check incomplete: {error:#}");
                }
                Err(error) => panic!("CRT false-domain check failed: {error:#}"),
            }
        }
        status
    }

    let validation_timeout_ms = std::env::var_os("UCP_CRT_VALIDATION_TIMEOUT_MS").map(|value| {
        let value = value
            .to_str()
            .expect("CRT validation timeout must be valid text")
            .parse::<u64>()
            .expect("CRT validation timeout must be a positive integer in milliseconds");
        assert!(
            value > 0,
            "CRT validation timeout must be greater than zero"
        );
        value
    });
    println!(
        "CRT timeouts: recovery=2000 ms/invocation; validation={} ms/invocation",
        validation_timeout_ms.unwrap_or(2_000)
    );
    let statuses = [
        check::<0>(validation_timeout_ms),
        check::<1>(validation_timeout_ms),
        check::<2>(validation_timeout_ms),
        check::<3>(validation_timeout_ms),
    ];
    println!("CRT bounded API statuses for 0/1/2/3 public remainders: {statuses:?}");
    assert_eq!(statuses[3], PrivacyAnalysisStatus::Analyzed);
}

//Mindket publikacio kulon-kulon tobb ervenyes titkot enged: nincs Exact teny.
#[test]
fn demo_linear_masking_individual_publications_are_ambiguous() {
    fn check<const MODE: u8>() {
        let mode = LinearMaskingCircuit::<MODE>::mode();
        let input = linear_masking_input(mode);
        let circuit = LinearMaskingCircuit::<MODE>::new(42, 58, 0);
        let alternate_mask = if mode == LinearMaskingMode::FirstOnly {
            83
        } else {
            108
        };
        let alternate = LinearMaskingCircuit::<MODE>::new(17, alternate_mask, 0);
        //A tobbfele witness nem csak az analyzer allitasa: Halo2 is elfogadja mindkettot.
        assert_linear_masking_witness_satisfied(&circuit, &input);
        assert_linear_masking_witness_satisfied(&alternate, &input);
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input,
            linear_masking_targets(mode),
            PrivacyAnalysisOptions::fast_probe_only(),
        )
        .unwrap();
        print_privacy_demo(
            &format!("One publication ({mode:?}): secret remains ambiguous:"),
            &report,
        );
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.exact_values, 0);
        assert_eq!(report.summary.non_unique_cells, 2);
        assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
        let validation =
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
        assert_eq!(validation.status, RecoveryValidationStatus::NoDomainClaims);
    }
    check::<{ LinearMaskingMode::FirstOnly as u8 }>();
    check::<{ LinearMaskingMode::SecondOnly as u8 }>();
}

//a=100 es b=142 ugyanazzal a maszkkal: a ket egyenlet egyutt feloldja a titkot.
#[test]
fn demo_linear_masking_reused_mask_leaks_secret_through_composition() {
    let mode = LinearMaskingMode::ReusedMask;
    let input = linear_masking_input(mode);
    let circuit = LinearMaskingCircuit::<{ LinearMaskingMode::ReusedMask as u8 }>::new(42, 58, 0);
    assert_linear_masking_witness_satisfied(&circuit, &input);
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        linear_masking_targets(mode),
        PrivacyAnalysisOptions::fast_probe_only(),
    )
    .unwrap();
    print_privacy_demo(
        "\nReused mask: a=100, b=142; a=s+r, b=2s+r -> s=b-a, r=2a-b",
        &report,
    );
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.exact_values, 2);
    assert_eq!(report.summary.unique_cells, 2);
    assert_eq!(report.summary.refined_domains, 0);
    assert!(!report.structural_baseline_computed);
    assert_eq!(report.semantic_queries, 0);
    for (cell, expected) in report.cells.iter().zip([42, 58]) {
        assert_eq!(cell.uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(
            cell.domain,
            Some(super::value::UcpValueDomain::exact(
                num_bigint::BigInt::from(expected)
            ))
        );
        assert!(cell.baseline_domain.is_none());
    }
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    print_validation_demo(
        "Independent check of the recovered secret and mask:",
        &validation,
    );
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
    assert_eq!(validation.domain_queries, 2);
    assert!(validation
        .cells
        .iter()
        .all(|cell| cell.status == super::privacy_validation::DomainValidationStatus::Entailed));
    //Elrontott titok eseten az ellenorzo az eredeti C-bol ellenpeldat kell talaljon.
    let mut wrong = report;
    wrong.cells[0].domain = Some(super::value::UcpValueDomain::exact(
        num_bigint::BigInt::from(17),
    ));
    let refuted = validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &wrong).unwrap();
    assert_eq!(refuted.status, RecoveryValidationStatus::Refuted);
    assert_eq!(
        refuted.cells[0].counterexample,
        Some(num_bigint::BigInt::from(42))
    );
}

//Ugyanaz a=100, b=142, de ket kulon maszk: pl. s=41 es s=17 is ervenyes lehet.
#[test]
fn demo_linear_masking_independent_masks_keep_secret_ambiguous() {
    let mode = LinearMaskingMode::IndependentMasks;
    let input = linear_masking_input(mode);
    let circuit =
        LinearMaskingCircuit::<{ LinearMaskingMode::IndependentMasks as u8 }>::new(41, 59, 60);
    let alternate =
        LinearMaskingCircuit::<{ LinearMaskingMode::IndependentMasks as u8 }>::new(17, 83, 108);
    assert_linear_masking_witness_satisfied(&circuit, &input);
    assert_linear_masking_witness_satisfied(&alternate, &input);
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        linear_masking_targets(mode),
        PrivacyAnalysisOptions::fast_probe_only(),
    )
    .unwrap();
    let alternate_report = analyze_private_recoverability::<Fr, _, _>(
        &alternate,
        4,
        &input,
        linear_masking_targets(mode),
        PrivacyAnalysisOptions::fast_probe_only(),
    )
    .unwrap();
    print_privacy_demo(
        "Independent masks: a=100, b=142; secret remains ambiguous:",
        &report,
    );
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.exact_values, 0);
    assert_eq!(report.summary.non_unique_cells, 3);
    assert_eq!(report.cells, alternate_report.cells);
    assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    assert_eq!(validation.status, RecoveryValidationStatus::NoDomainClaims);
    //Ez tobb megoldast bizonyit, nem teljes titkossagot vagy kriptografiai biztonsagot.
}

// SMT narrows a private input to two feasible values; UCP then recovers a dependent cell.
#[test]
fn demo_finite_domain_refinement_restarts_ucp_without_guessing_the_secret() {
    use super::{
        privacy_domain_tests::{
            finite_projection_demo_input, finite_projection_demo_options,
            finite_projection_demo_targets, FiniteProjectionCircuit,
        },
        value::UcpValueDomain,
    };
    use num_bigint::BigInt;

    // Public product=21 and fixed sum=10: s^2-10s+21=0, with s in {0,...,15}.
    // The second equation d*(s-5)=0 becomes informative only once 5 is excluded for s.
    let circuit = FiniteProjectionCircuit::<false>::new(3);
    let input = finite_projection_demo_input();
    let options = finite_projection_demo_options();
    MockProver::run(5, &circuit, vec![vec![Fr::from(21)]])
        .unwrap()
        .assert_satisfied();
    let coarse = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        5,
        &input,
        finite_projection_demo_targets(),
        PrivacyAnalysisOptions {
            domain_refinement: Default::default(),
            ..options
        },
    )
    .unwrap();
    let refined = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        5,
        &input,
        finite_projection_demo_targets(),
        options,
    )
    .unwrap();
    print_privacy_demo("Before finite-domain SMT refinement:", &coarse);
    print_privacy_demo(
        "After SMT excludes fourteen candidates; UCP learns d=0:",
        &refined,
    );
    println!("Additional recovery, not a speedup comparison.");
    assert_eq!(coarse.cells[1].domain, None);
    assert_eq!(
        refined.cells[0].domain,
        UcpValueDomain::finite_set([3, 7].into_iter().map(BigInt::from))
    );
    assert_eq!(
        refined.cells[0].uniqueness,
        PrivateCellUniqueness::NonUnique
    );
    assert_eq!(
        refined.cells[1].domain,
        Some(UcpValueDomain::exact(0.into()))
    );
    assert_eq!(refined.semantic_queries, 0);
    assert_eq!(refined.domain_refinement_statistics.solver_checks, 16);
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 5, &input, &refined).unwrap();
    print_validation_demo("Fresh independent coverage validation:", &validation);
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
}

// No UCP seed: SMT enumerates the two roots, proves exhaustion, then UCP recovers d=0.
#[test]
fn demo_smt_discovers_a_private_domain_without_ucp_candidates() {
    use super::{
        privacy_discovery_tests::{
            discovery_demo_input, discovery_demo_options, discovery_demo_targets,
            UnboundedProjectionCircuit, TWO_ROOTS,
        },
        value::UcpValueDomain,
    };
    use num_bigint::BigInt;
    let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0));
    let input = discovery_demo_input();
    let options = discovery_demo_options();
    MockProver::run(4, &circuit, vec![vec![Fr::from(21)]])
        .unwrap()
        .assert_satisfied();
    let coarse = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        discovery_demo_targets(),
        PrivacyAnalysisOptions {
            domain_discovery: Default::default(),
            ..options
        },
    )
    .unwrap();
    let discovered = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        discovery_demo_targets(),
        options,
    )
    .unwrap();
    print_privacy_demo("Without discovery: no recovered domains:", &coarse);
    print_privacy_demo(
        "Discovery: two SAT values, final UNSAT, then UCP:",
        &discovered,
    );
    println!("Additional recovery, not a speedup comparison.");
    assert!(coarse.cells.iter().all(|cell| cell.domain.is_none()));
    assert_eq!(
        discovered.cells[0].domain,
        UcpValueDomain::finite_set([3, 7].into_iter().map(BigInt::from))
    );
    assert_eq!(
        discovered.cells[1].domain,
        Some(UcpValueDomain::exact(0.into()))
    );
    assert_eq!(discovered.domain_discovery_statistics.solver_checks, 3);
    assert_eq!(discovered.semantic_queries, 0);
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &discovered).unwrap();
    print_validation_demo("Fresh independent coverage validation:", &validation);
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
}

// A free first cell must not hide the later public-dependent private chain behind the query cap.
#[test]
fn demo_fair_domain_discovery_recovers_later_targets_with_a_small_budget() {
    use super::{
        privacy_discovery::PrivacyDomainDiscoveryOptions,
        privacy_discovery_tests::{
            discovery_demo_input, UnboundedProjectionCircuit, FREE_FIRST_RECOVERABLE_CHAIN,
        },
        value::UcpValueDomain,
    };
    let circuit =
        UnboundedProjectionCircuit::<FREE_FIRST_RECOVERABLE_CHAIN>::new(Fr::from(37), Fr::from(21));
    let input = discovery_demo_input();
    MockProver::run(4, &circuit, vec![vec![Fr::from(21)]])
        .unwrap()
        .assert_satisfied();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        [
            CellId::advice(0, 0),
            CellId::advice(1, 0),
            CellId::advice(2, 0),
        ],
        PrivacyAnalysisOptions {
            max_semantic_queries: 0,
            solver_timeout_ms: Some(2_000),
            domain_discovery: PrivacyDomainDiscoveryOptions {
                max_solver_checks: 4,
                ..Default::default()
            },
            ..PrivacyAnalysisOptions::fast_probe_only()
        },
    )
    .unwrap();
    print_privacy_demo("Public p=21; a is free; b*b-2*p*b+p*p=0; c=b+2:", &report);
    println!("Budget-limited recovery is not a privacy certificate.");
    assert!(report.cells[0].domain.is_none());
    assert_eq!(
        report.cells[1].domain,
        Some(UcpValueDomain::exact(21.into()))
    );
    assert_eq!(
        report.cells[2].domain,
        Some(UcpValueDomain::exact(23.into()))
    );
    assert_eq!(report.summary.exact_values, 2);
    assert_eq!(report.domain_discovery_statistics.solver_checks, 4);
    assert_eq!(report.domain_discovery_statistics.attempted_cells, 3);
    assert_eq!(report.domain_discovery_statistics.resumed_checks, 1);
    assert_eq!(report.semantic_queries, 0);
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    print_validation_demo("Fresh independent coverage validation:", &validation);
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
}

// An expanded private root needs SMT, then UCP propagates it; 16 unrelated quadratics stay outside the exclusion subset.
#[test]
fn demo_targeted_subset_exclusion_recovers_private_values_beside_unrelated_gates() {
    use super::{
        privacy_discovery::PrivacyDomainDiscoveryOptions,
        privacy_discovery_tests::{
            discovery_demo_input, discovery_demo_targets, LocalizedRecoveryCircuit,
        },
        value::UcpValueDomain,
    };
    let circuit = LocalizedRecoveryCircuit::<16> { amount: 21 };
    let input = discovery_demo_input();
    MockProver::run(4, &circuit, vec![vec![Fr::from(21)]])
        .unwrap()
        .assert_satisfied();
    let options = PrivacyAnalysisOptions {
        max_semantic_queries: 0,
        solver_timeout_ms: Some(2_000),
        domain_discovery: PrivacyDomainDiscoveryOptions {
            max_solver_checks: 2,
            max_values_per_cell: 1,
            max_checks_per_round: 2,
            ..Default::default()
        },
        ..PrivacyAnalysisOptions::fast_probe_only()
    };
    let full = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        discovery_demo_targets(),
        options,
    )
    .unwrap();
    let targeted = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        discovery_demo_targets(),
        PrivacyAnalysisOptions {
            domain_discovery: PrivacyDomainDiscoveryOptions {
                use_targeted_subsets: true,
                ..options.domain_discovery
            },
            ..options
        },
    )
    .unwrap();
    println!("Public amount=21; s*s-2*amount*s+amount*amount=0; next=s+2; 16 unrelated gates.");
    print_privacy_demo("Full-model discovery:", &full);
    print_privacy_demo(
        "Targeted exclusion: original SAT sample, local UNSAT proof, then UCP:",
        &targeted,
    );
    println!("Times include initial SAT and preprocessing; this is not a benchmark.");
    for report in [&full, &targeted] {
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(21.into()))
        );
        assert_eq!(
            report.cells[1].domain,
            Some(UcpValueDomain::exact(23.into()))
        );
        assert_eq!(report.domain_discovery_statistics.solver_checks, 2);
        assert_eq!(report.semantic_queries, 0);
        assert!(report.cells[1].domain_discovery.is_none()); // Recovered by UCP, not a second model sample.
    }
    assert_eq!(full.domain_discovery_statistics.full_solver_checks, 2);
    assert_eq!(targeted.domain_discovery_statistics.full_solver_checks, 1);
    assert_eq!(targeted.domain_discovery_statistics.subset_solver_checks, 1);
    assert_eq!(targeted.domain_discovery_statistics.subset_unsat_proofs, 1);
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &targeted).unwrap();
    print_validation_demo("Fresh original-context coverage validation:", &validation);
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
}

// Compare an intrinsic constant missed by UCP with a secret exposed by two public masked values.
#[test]
fn demo_public_observation_control_separates_smt_progress_from_publication_effects() {
    use super::{
        privacy_observation::{
            analyze_public_observation_effect, PrivateDomainObservationEffect,
            PublicObservationEffectOptions, PublicObservationEffectStatus,
        },
        privacy_observation_tests::intrinsic_control_demo,
    };
    let (intrinsic_circuit, intrinsic_input, intrinsic) = intrinsic_control_demo();
    let intrinsic_effect = analyze_public_observation_effect::<Fr, _>(
        &intrinsic_circuit,
        4,
        &intrinsic_input,
        &intrinsic,
        PublicObservationEffectOptions::default(),
    )
    .unwrap();
    print_privacy_demo("Intrinsic: s*s-2*s+1=0; next=s+2:", &intrinsic);
    print_observation_demo(
        "Exact domains already follow without public observations:",
        &intrinsic_effect,
    );
    assert!(intrinsic.cells[0].domain_refined_from_baseline);
    assert_eq!(
        intrinsic_effect.status,
        PublicObservationEffectStatus::Analyzed
    );
    assert!(intrinsic_effect
        .cells
        .iter()
        .all(|cell| cell.effect == PrivateDomainObservationEffect::AlreadyImplied));

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
        PrivacyAnalysisOptions {
            solver_timeout_ms: Some(2_000),
            ..PrivacyAnalysisOptions::fast_probe_only()
        },
    )
    .unwrap();
    let effect = analyze_public_observation_effect::<Fr, _>(
        &circuit,
        4,
        &input,
        &recovery,
        PublicObservationEffectOptions::default(),
    )
    .unwrap();
    print_privacy_demo("Publication: first=s+r=100; second=2*s+r=142:", &recovery);
    print_observation_demo(
        "Without observations, alternatives exist outside the recovered domains:",
        &effect,
    );
    println!("This checks domain dependence, not entropy or protocol zero-knowledge.");
    assert_eq!(recovery.summary.exact_values, 2);
    assert_eq!(effect.status, PublicObservationEffectStatus::Analyzed);
    assert!(effect.cells.iter().all(|cell| cell.effect
        == PrivateDomainObservationEffect::ObservationDependent
        && cell.observed_domain_verified
        && cell.unobserved_counterexample.is_some()));
    assert_eq!(effect.solver_checks, 5); // One original SAT plus two full-model exclusions per cell.
}

mod output_tests {
    use super::super::{
        privacy::{PrivacyAnalysisSummary, PrivateCellReport, RecoveryLimitation},
        privacy_discovery::PrivateDomainDiscovery,
        privacy_observation::{
            PrivateDomainObservationEffect, PrivateObservationEffect,
            PublicObservationEffectOptions, PublicObservationEffectStatus,
        },
        privacy_validation::{DomainValidationStatus, PrivateDomainValidation},
    };
    use super::*;

    fn report() -> PrivacyAnalysisReport {
        PrivacyAnalysisReport {
            solver_invocations: 1,
            phases: Vec::new(),
            structural_baseline_computed: true,
            status: PrivacyAnalysisStatus::Analyzed,
            cells: [42, 58]
                .into_iter()
                .enumerate()
                .map(|(column, value)| PrivateCellReport {
                    cell: CellId::advice(column, 0),
                    query_attempts: 0,
                    uniqueness: PrivateCellUniqueness::Unique,
                    domain: Some(UcpValueDomain::exact(value.into())),
                    domain_is_complete: true,
                    baseline_domain: None,
                    domain_refined_from_baseline: true,
                    recovery_limitation: None,
                    domain_refinement: None,
                    domain_discovery: None,
                })
                .collect(),
            summary: PrivacyAnalysisSummary {
                private_cells: 2,
                exact_values: 2,
                unique_cells: 2,
                refined_domains: 2,
                ..Default::default()
            },
            public_values: vec![(CellId::instance(0, 0), 100.into())],
            semantic_queries: 0,
            search_statistics: Default::default(),
            domain_refinement_statistics: Default::default(),
            domain_discovery_statistics: Default::default(),
            satisfiability_checks: 1,
            satisfiability_evidence: None,
            elapsed: Duration::from_millis(6),
            options: PrivacyAnalysisOptions {
                compute_structural_baseline: true,
                ..PrivacyAnalysisOptions::fast_probe_only()
            },
            ucp_result: None,
        }
    }

    #[test]
    fn compact_output_preserves_values_counts_and_timing_without_configuration() {
        let report = report();
        let text = demo_report_text(&report, || short_privacy_report(&report), false);
        assert!(text.contains("Privacy: Analyzed; cells: 2; exact: 2"));
        assert!(text.contains("A-0-0: Unique; Exact(42)"));
        assert!(text.contains("A-1-0: Unique; Exact(58)"));
        assert!(text.contains("Initial SAT checks: 1; SMT uniqueness queries: 0"));
        assert!(text.contains("elapsed: 6.00ms"));
        assert!(!text.contains("Search policy:"));
        assert!(!text.contains("Search limits:"));
        assert!(!text.contains("refinement checks:"));
        assert!(!text.contains("discovery checks:"));
        assert_eq!(text.lines().count(), 4);
    }

    #[test]
    fn verbose_output_uses_the_unchanged_full_report() {
        let report = report();
        let text = demo_report_text(
            &report,
            || panic!("Compact formatting should not run"),
            true,
        );
        assert_eq!(text, report.to_string());
        assert!(text.contains("Search policy:"));
        assert!(text.contains("Domain discovery:"));
    }

    #[test]
    fn compact_output_preserves_unknown_status_and_timeout() {
        let mut report = report();
        report.status = PrivacyAnalysisStatus::SolverUnknown;
        report.cells[0].uniqueness = PrivateCellUniqueness::Unknown;
        report.cells[0].domain = None;
        report.cells[0].recovery_limitation = Some(RecoveryLimitation::SolverTimeout);
        report.summary.exact_values = 1;
        report.summary.unique_cells = 1;
        report.summary.unresolved_uniqueness = 1;
        let text = short_privacy_report(&report);
        assert!(text.contains("Privacy: SolverUnknown"));
        assert!(text.contains("unresolved: 1"));
        assert!(text.contains("A-0-0: Unknown; No recovered domain; limitation: SolverTimeout"));
    }

    #[test]
    fn compact_output_does_not_hide_partial_search_after_recovery() {
        let mut report = report();
        report.cells[0].domain_discovery = Some(PrivateDomainDiscovery {
            limitation: Some(RecoveryLimitation::QueryLimit),
            ..Default::default()
        });
        report.domain_discovery_statistics.budget_exhausted = true;
        let text = short_privacy_report(&report);
        assert!(text.contains("Privacy: Analyzed"));
        assert!(text.contains("Exact(42); discovery: Partial (Some(QueryLimit))"));
        assert!(text.contains("discovery budget exhausted: true"));
    }

    #[test]
    fn compact_finite_domains_have_a_bounded_preview() {
        let domain = UcpValueDomain::finite_set((0..16).map(num_bigint::BigInt::from)).unwrap();
        assert_eq!(
            short_demo_domain(Some(&domain)),
            "Candidates({0, 1, 2, 3, 4, 5, 6, 7, ...}; size=16)"
        );
        assert_eq!(
            short_demo_domain(Some(&UcpValueDomain::exact(42.into()))),
            "Exact(42)"
        );
        assert_eq!(short_demo_domain(None), "No recovered domain");
    }

    #[test]
    fn compact_validation_keeps_refutations_and_actual_check_counts() {
        let report = PrivateRecoveryValidationReport {
            status: RecoveryValidationStatus::Refuted,
            cells: vec![PrivateDomainValidation {
                cell: CellId::advice(0, 0),
                status: DomainValidationStatus::Refuted,
                counterexample: Some(42.into()),
            }],
            domain_queries: 1,
            solver_checks: 2,
            subset_checks: 1,
            solver_timeout_ms: Some(2_000),
            elapsed: Duration::from_millis(16),
        };
        let text = short_validation_report(&report);
        assert!(text.contains("Domain validation: Refuted; checked claims: 1; SMT checks: 2"));
        assert!(text.contains("A-0-0: Refuted; counterexample: 42"));
    }

    #[test]
    fn compact_observation_control_keeps_incomplete_coverage_evidence() {
        let report = PublicObservationEffectReport {
            status: PublicObservationEffectStatus::QueryLimitReached,
            cells: vec![PrivateObservationEffect {
                cell: CellId::advice(0, 0),
                domain: Some(UcpValueDomain::exact(42.into())),
                effect: PrivateDomainObservationEffect::Unresolved,
                observed_domain_verified: true,
                unobserved_counterexample: None,
                observed_counterexample: None,
                limitation: Some(RecoveryLimitation::QueryLimit),
            }],
            public_values: vec![],
            solver_checks: 2,
            satisfiability_checks: 1,
            observed_domain_checks: 1,
            unobserved_domain_checks: 0,
            elapsed: Duration::from_millis(10),
            options: PublicObservationEffectOptions::default(),
        };
        let text = short_observation_report(&report);
        assert!(text.contains("Observation control: QueryLimitReached; SMT checks: 2"));
        assert!(text
            .contains("A-0-0: Unresolved; observed domain verified: true; limitation: QueryLimit"));
    }
}

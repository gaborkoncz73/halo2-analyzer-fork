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

use super::{
    cell::CellId,
    pipeline::{analyze_underconstrained_with_ucp, UcpAnalyzerPipelineStatus},
    privacy::{
        analyze_private_recoverability, PrivacyAnalysisOptions, PrivacyAnalysisStatus,
        PrivateCellUniqueness,
    },
    privacy_validation::{validate_private_recovery_report, RecoveryValidationStatus},
};
use crate::{
    circuit_analyzer::{analyzer::Analyzer, halo2_proofs_libs::*},
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerOutputStatus, AnalyzerType, LookupMethod, VerificationInput,
        VerificationMethod,
    },
};
use std::{array, collections::HashMap, marker::PhantomData, time::Duration, time::Instant};

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
        "demo_private_amount_bits analyzer_only={:?} analyzer_time={:?} pipeline_status={:?} pipeline_time={:?} speedup={:.2}x used_smt={} semantic_queries={} unresolved_targets={:?} learned_domains={:?}",
        analyzer_status,
        analyzer_duration,
        pipeline_output.status,
        pipeline_duration,
        speedup(analyzer_duration, pipeline_duration),
        pipeline_output.used_smt,
        pipeline_output.semantic_queries,
        pipeline_output.target_check.unresolved_targets,
        pipeline_output.ucp_result.value_facts.domains(),
    );

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
        "demo_secret_commitment pipeline_status={:?} pipeline_time={:?} used_smt={} semantic_queries={} commitment_unique={} secret_unique={} nonce_unique={} known_values={:?}",
        pipeline_output.status,
        pipeline_duration,
        pipeline_output.used_smt,
        pipeline_output.semantic_queries,
        pipeline_output.ucp_result.facts.is_unique(&commitment),
        pipeline_output.ucp_result.facts.is_unique(&secret),
        pipeline_output.ucp_result.facts.is_unique(&nonce),
        pipeline_output.ucp_result.value_facts.known_values(),
    );

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
        "demo_one_smt_then_ucp analyzer_only={:?} analyzer_time={:?} pipeline_status={:?} pipeline_time={:?} speedup={:.2}x used_smt={} semantic_queries={} smt_learned={:?} unresolved_targets={:?} recovered_values={:?}",
        analyzer_status,
        analyzer_duration,
        pipeline_output.status,
        pipeline_duration,
        speedup(analyzer_duration, pipeline_duration),
        pipeline_output.used_smt,
        pipeline_output.semantic_queries,
        pipeline_output.smt_learned_cells,
        pipeline_output.target_check.unresolved_targets,
        pipeline_output.ucp_result.value_facts.known_values(),
    );

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
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    println!("Public amount exposes all private bits:\n{exposed}");
    assert_eq!(exposed.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(exposed.summary.exact_values, N);
    assert_eq!(exposed.summary.refined_domains, N);
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
    println!("Checking recovered bits against original constraints:\n{validated}");
    assert_eq!(validated.status, RecoveryValidationStatus::VerifiedDomains);
    assert_eq!(validated.domain_queries, N);

    //Ez csak egy osszeges illusztracio, nem kriptografiai commitment vagy ZK-bizonyitas.
    //100 = secret + nonce tobb megoldast enged; a synthesisbeli 42 es 58 nem Delta-teny.
    let ambiguous = analyze_private_recoverability::<Fr, _, _>(
        &SecretCommitmentCircuit::new(42, 58),
        4,
        &analyzer_input_with_public_amount(100),
        [CellId::advice(0, 0), CellId::advice(1, 0)],
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    println!("Public sum does not determine its private operands:\n{ambiguous}");
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
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    report.cells[0].domain = Some(super::value::UcpValueDomain::exact(
        num_bigint::BigInt::from(0),
    ));
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    println!("A false recovered bit is refuted:\n{validation}");
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
            PrivacyAnalysisOptions::default(),
        )
        .unwrap();
        println!("One publication ({mode:?}) cannot determine the secret:\n{report}");
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
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    println!("Reused mask: a=100, b=142 imply s=b-a=42, r=2a-b=58:\n{report}");
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.exact_values, 2);
    assert_eq!(report.summary.unique_cells, 2);
    assert_eq!(report.summary.refined_domains, 2);
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
    println!("Independent check of the recovered secret and mask:\n{validation}");
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
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    let alternate_report = analyze_private_recoverability::<Fr, _, _>(
        &alternate,
        4,
        &input,
        linear_masking_targets(mode),
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    println!("Independent masks: the same public observations do not determine s:\n{report}");
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
    println!("Before finite-domain SMT refinement:\n{coarse}");
    println!("Original SMT excludes fourteen candidates; UCP then learns d=0:\n{refined}");
    println!(
        "Elapsed: coarse={:?}, refined={:?}. This measures additional recovery, not a speedup.",
        coarse.elapsed, refined.elapsed
    );
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
    assert_eq!(refined.domain_refinement_statistics.solver_checks, 17);
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 5, &input, &refined).unwrap();
    println!("Fresh independent coverage validation:\n{validation}");
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
    println!("Without discovery, neither private target has a Delta domain:\n{coarse}");
    println!("Original-model enumeration: two SAT values and a final UNSAT, followed by UCP:\n{discovered}");
    println!(
        "Elapsed: coarse={:?}, discovery={:?}. This is extra recovery, not a speedup claim.",
        coarse.elapsed, discovered.elapsed
    );
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
    println!("Fresh independent coverage validation:\n{validation}");
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
            ..Default::default()
        },
    )
    .unwrap();
    println!("Public p=21; a is free; b*b-2*p*b+p*p=0; c=b+2.");
    println!("UCP priority plus fair rounds: four discovery checks recover b and c:\n{report}");
    println!("The free cell remains unresolved. This demonstrates budget allocation, not cryptographic privacy or a general speedup.");
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
    println!("Fresh independent coverage validation:\n{validation}");
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
        ..Default::default()
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
    println!("Public amount=21; s*s-2*amount*s+amount*amount=0; next=s+2; 16 independent v*v-(amount+i)^2=0 gates.");
    println!(
        "Full-model discovery: {:?}; elapsed: {:?}",
        full.domain_discovery_statistics, full.elapsed
    );
    println!(
        "Targeted exclusion: {:?}; elapsed: {:?}",
        targeted.domain_discovery_statistics, targeted.elapsed
    );
    println!("The first sample still satisfies the full original model. The terminal UNSAT uses only two original gates; UCP then learns next=23.\n{targeted}");
    println!("Times include mandatory full-original SAT and preprocessing. This single debug comparison is not a general speedup estimate.");
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
    println!("Fresh original-context coverage validation:\n{validation}");
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
    println!("Intrinsic: s*s-2*s+1=0, next=s+2. An unrelated public observation is not needed.");
    println!(
        "UCP baseline for s: {:?}; recovered: {:?}; refined from UCP baseline: {}",
        intrinsic.cells[0].baseline_domain,
        intrinsic.cells[0].domain,
        intrinsic.cells[0].domain_refined_from_baseline
    );
    println!("Original-SMT control correctly attributes both exact values to C alone:\n{intrinsic_effect}");
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
            ..Default::default()
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
    println!("Publication: first=s+r=100; second=2*s+r=142. Together they expose s=42, r=58.");
    println!(
        "Without those concrete observations, original satisfying alternatives exist:\n{effect}"
    );
    println!("Recovery time: {:?}; separate control time: {:?}. This control checks domain dependence, not entropy or protocol ZK.", recovery.elapsed, effect.elapsed);
    assert_eq!(recovery.summary.exact_values, 2);
    assert_eq!(effect.status, PublicObservationEffectStatus::Analyzed);
    assert!(effect.cells.iter().all(|cell| cell.effect
        == PrivateDomainObservationEffect::ObservationDependent
        && cell.observed_domain_verified
        && cell.unobserved_counterexample.is_some()));
    assert_eq!(effect.solver_checks, 5); // One original SAT plus two full-model exclusions per cell.
}

# halo2-analyzer fork: Korrekt + private-value recovery

This repository is a fork of [Quantstamp's halo2-analyzer (Korrekt)](https://github.com/quantstamp/halo2-analyzer).
It analyzes [Halo2](https://github.com/zcash/halo2) circuits in two ways:

1. **Private-value recovery (this fork).** You give it a circuit, the public
   (instance) values an observer can see, and the secret (advice) cells you care
   about. It reports, per secret cell, whether the public values **determine it
   exactly**, restrict it to a **finite set of candidates**, or leave it
   **undetermined**. It combines a fast propagation engine (UCP) with the
   [cvc5](https://cvc5.github.io/) SMT solver over finite fields.
2. **The original Korrekt checks.** Unused gates, unused columns, unconstrained
   cells and underconstrained circuits. The original Korrekt decides
   underconstrainedness with SMT alone: it encodes the whole circuit for the
   solver and asks for a second witness with the same public values. It has no
   propagation step. **For exactly this problem, deciding whether the public
   values determine the witness, this fork adds the UCP engine:** propagation
   runs first, and SMT is only called for what propagation leaves open.

You do not need to modify this repository to analyze your own circuit. You
create a small Rust crate next to it, depend on the `korrekt` library, and run
it. Section 4 walks through that from start to finish.

---

## Contents

1. [Requirements](#1-requirements)
2. [Install cvc5 with finite-field support](#2-install-cvc5-with-finite-field-support)
3. [Clone, build and smoke-test](#3-clone-build-and-smoke-test)
4. [Analyze your own circuit](#4-analyze-your-own-circuit)
5. [Reading the report](#5-reading-the-report)
6. [Tuning and limits](#6-tuning-and-limits)
7. [Troubleshooting](#7-troubleshooting)
8. [Thesis examples and formal verification](#8-thesis-examples-and-formal-verification)
9. [Repository layout](#9-repository-layout)
10. [How it works](#10-how-it-works)

---

## 1. Requirements

| What | Why | Tested with |
| --- | --- | --- |
| Linux | The only tested platform | Linux, GCC 15 |
| `git` | Clone this repo and the Git dependencies | |
| [rustup](https://rustup.rs/) | `rust-toolchain.toml` selects a **nightly** toolchain automatically | `rustc 1.97.0-nightly (2026-05-12)` |
| `cvc5` **built with CoCoA** (finite-field support) on your `PATH` | Every SMT query uses the finite-field theory | cvc5 1.3.x (`main`) |
| Network access for the first build | Halo2 and a few other dependencies are fetched from Git | |

`rust-toolchain.toml` pins only the `nightly` channel, not a specific date. If a
future nightly fails to build the project, pin a dated nightly from around the
tested date in that file (`channel = "nightly-YYYY-MM-DD"`).

---

## 2. Install cvc5 with finite-field support

The cvc5 binaries you get from package managers are usually built **without**
CoCoA, which means no finite-field support. Build it from source.

**Ubuntu / Debian**

```bash
sudo apt-get update
sudo apt-get install -y build-essential cmake git python3 python3-venv python3-pip libgmp-dev m4

git clone https://github.com/cvc5/cvc5.git
cd cvc5
./configure.sh --auto-download --cocoa --gpl --poly
cd build
make -j"$(nproc)"
sudo make install          # installs /usr/local/bin/cvc5
```

Notes:

- `--cocoa` enables finite fields. CoCoA is GPL-licensed, so cvc5 requires
  `--gpl` together with it.
- `--auto-download` fetches and patches CoCoA and the other dependencies, and
  installs the Python build modules (`tomli`, `pyparsing`) in a virtualenv.
- If CMake cannot find GMP, point it at your installation with
  `--dep-path=/path/to/prefix`, or export `GMP_LIB=/path/to/libgmp.a`.
- Full upstream instructions: <https://github.com/cvc5/cvc5/blob/main/INSTALL.rst>.

**Verify:**

```bash
cvc5 --version | head -1
cvc5 --show-config | grep cocoa      # must print: cocoa : yes
```

---

## 3. Clone, build and smoke-test

```bash
git clone https://github.com/gaborkoncz73/halo2-analyzer-fork.git
cd halo2-analyzer-fork

cargo build -p korrekt                # first build fetches Git dependencies
cargo test -p korrekt --lib demo_risk_audit -- --nocapture --test-threads=1
```

The test command should finish with output similar to:

```text
test result: ok. 5 passed; 0 failed; 2 ignored; ...
```

That run calls cvc5, so a passing result confirms that Rust, the dependencies
and the solver all work. Always pass `--test-threads=1` to solver-backed
tests: the analyzer writes its SMT queries to fixed file names under
`src/output/`, so parallel runs would overwrite each other's files.

---

## 4. Analyze your own circuit

The example below runs as written. It contains a small circuit with three
secrets (`a`, `b`, `x`) and three public outputs (`a + b`, `a - b`, `x²`). From
the public outputs, `a` and `b` can be recovered exactly. `x` can only be
narrowed down to `{5, -5}`. To analyze your own circuit, replace the circuit
section and adjust steps (a)–(d), as described in [4.5](#45-adapting-it-to-your-circuit).

### 4.1 Create a crate next to the clone

```bash
cd ..                                            # the directory that contains halo2-analyzer-fork/
cargo new --vcs none my-circuit-audit
cd my-circuit-audit
cp ../halo2-analyzer-fork/rust-toolchain.toml .  # use the same nightly toolchain
```

### 4.2 `Cargo.toml`

Replace the generated file with:

```toml
[package]
name = "my-circuit-audit"
version = "0.1.0"
edition = "2021"
publish = false

# Keeps this crate standalone, even if it is placed inside another workspace.
[workspace]

[dependencies]
korrekt = { path = "../halo2-analyzer-fork/korrekt" }
num-bigint = "0.4"
anyhow = "1"

# Required. The analyzer needs an instrumented Halo2 build and halo2curves fork.
# Without these patches, korrekt does not compile outside its own workspace.
[patch."https://github.com/zcash/halo2.git"]
halo2_proofs = { git = "https://github.com/Analyzable-Halo2/zcash-halo2.git", rev = "7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb" }

[patch."https://github.com/privacy-scaling-explorations/halo2curves.git"]
halo2curves = { git = "https://github.com/quantstamp/halo2curves.git", rev = "2ef5a9a60e02f4ae567e24725a5b27b2dce1bc07" }
```

### 4.3 `src/main.rs`

```rust
use korrekt::{
    circuit_analyzer::{
        analyzable::Analyzable,
        analyzer::Analyzer,
        halo2_proofs_libs::*,
        ucp::{
            cell::CellId,
            privacy::{analyze_private_recoverability_with_witness, PrivacyAnalysisOptions},
            privacy_validation::validate_private_recovery_report,
        },
    },
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerType, LookupMethod, VerificationInput, VerificationMethod,
    },
};
use num_bigint::BigInt;
use std::collections::BTreeMap;

// ============================================================================
// 1. YOUR CIRCUIT  (replace this part with your own circuit)
//    Secrets: a, b, x.   Public: a + b, a - b, x * x.
// ============================================================================
#[derive(Clone, Debug)]
pub struct MyConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    sum: Column<Advice>,
    diff: Column<Advice>,
    instance: Column<Instance>,
    s_lin: Selector,
    s_sq: Selector,
}

#[derive(Default)]
pub struct MyCircuit {
    a: Value<Fr>,
    b: Value<Fr>,
    x: Value<Fr>,
}

impl Circuit<Fr> for MyCircuit {
    type Config = MyConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> MyConfig {
        let [a, b, sum, diff] = [(); 4].map(|_| meta.advice_column());
        let instance = meta.instance_column();
        meta.enable_equality(sum);
        meta.enable_equality(diff);
        meta.enable_equality(instance);
        let s_lin = meta.selector();
        let s_sq = meta.selector();
        meta.create_gate("sum and difference", |meta| {
            let s = meta.query_selector(s_lin);
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let sum = meta.query_advice(sum, Rotation::cur());
            let diff = meta.query_advice(diff, Rotation::cur());
            vec![
                s.clone() * (a.clone() + b.clone() - sum),
                s * (a - b - diff),
            ]
        });
        meta.create_gate("square", |meta| {
            let s = meta.query_selector(s_sq);
            let x = meta.query_advice(a, Rotation::cur());
            let y = meta.query_advice(sum, Rotation::cur());
            vec![s * (x.clone() * x - y)]
        });
        MyConfig { a, b, sum, diff, instance, s_lin, s_sq }
    }

    fn synthesize(&self, c: MyConfig, mut layouter: impl Layouter<Fr>) -> Result<(), Error> {
        let (sum, diff) = layouter.assign_region(
            || "secret pair",
            |mut region| {
                c.s_lin.enable(&mut region, 0)?;
                region.assign_advice(|| "a", c.a, 0, || self.a)?;
                region.assign_advice(|| "b", c.b, 0, || self.b)?;
                let sum = region.assign_advice(|| "a+b", c.sum, 0, || self.a + self.b)?;
                let diff = region.assign_advice(|| "a-b", c.diff, 0, || self.a - self.b)?;
                Ok((sum, diff))
            },
        )?;
        let square = layouter.assign_region(
            || "secret root",
            |mut region| {
                c.s_sq.enable(&mut region, 0)?;
                region.assign_advice(|| "x", c.a, 0, || self.x)?;
                region.assign_advice(|| "x*x", c.sum, 0, || self.x * self.x)
            },
        )?;
        layouter.constrain_instance(sum.cell(), c.instance, 0)?;
        layouter.constrain_instance(diff.cell(), c.instance, 1)?;
        layouter.constrain_instance(square.cell(), c.instance, 2)?;
        Ok(())
    }
}

// ============================================================================
// 2. THE AUDIT
// ============================================================================
/// Same `k` you would pass to MockProver (the circuit has 2^k rows).
const K: u32 = 4;

fn main() -> anyhow::Result<()> {
    // (a) One honest witness and the public values it produces.
    let circuit = MyCircuit {
        a: Value::known(Fr::from(7)),
        b: Value::known(Fr::from(3)),
        x: Value::known(Fr::from(5)),
    };
    let public: Vec<u64> = vec![10, 4, 25]; // instance column 0, rows 0, 1, 2

    // (b) Sanity check: the witness must satisfy the circuit with these public values.
    let instance = public.iter().map(|v| Fr::from(*v)).collect();
    MockProver::run(K, &circuit, vec![instance])?.assert_satisfied();

    // (c) What the attacker sees. Keys are "I-<instance column>-<row>".
    let mut observations = AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new(
            public
                .iter()
                .enumerate()
                .map(|(row, v)| (format!("I-0-{row}"), BigInt::from(*v))),
            1,
        ),
        lookup_method: LookupMethod::InlineConstraints,
    };

    // (d) Which advice cells are secret? Found by region name + advice column index.
    let layout = Analyzable::<Fr>::config_and_synthesize(&circuit, K)?;
    let mut targets = BTreeMap::new();
    for region in &layout.regions {
        for (column, row) in region.cells.iter() {
            if *column.column_type() != Any::Advice {
                continue;
            }
            // Uncomment to see every advice cell of your circuit:
            // println!("region {:?}: advice column {}, row {}", region.name, column.index(), row);
            let label = match (region.name.as_str(), column.index()) {
                ("secret pair", 0) => "a",
                ("secret pair", 1) => "b",
                ("secret root", 0) => "x",
                _ => continue,
            };
            targets.insert(CellId::advice(column.index(), *row as i32), label.to_string());
        }
    }

    // (e) Private-value recovery (UCP propagation + cvc5).
    let mut options = PrivacyAnalysisOptions::default();
    options.solver_timeout_ms = Some(3_000); // per cvc5 call during the search
    options.initial_sat_timeout_ms = Some(60_000); // only for the SMT fallback of the first SAT check
    let report = analyze_private_recoverability_with_witness::<Fr, _, _>(
        &circuit,
        K,
        &observations,
        targets.keys().cloned(),
        options,
    )?;
    println!("{}", report.phase_report_with_names(|cell| targets.get(cell).cloned()));
    println!("{report}");

    // (f) Optional: independent, fresh SMT check of every reported domain.
    let validation = validate_private_recovery_report::<Fr, _>(&circuit, K, &observations, &report)?;
    println!("Validation: {:?} ({} solver checks)", validation.status, validation.solver_checks);

    // (g) Optional: the original Korrekt structural checks on the same circuit.
    for kind in [
        AnalyzerType::UnusedGates,
        AnalyzerType::UnusedColumns,
        AnalyzerType::UnconstrainedCells,
        AnalyzerType::UnderconstrainedCircuit,
    ] {
        let mut analyzer = Analyzer::new(&circuit, K, kind.clone(), Some(&observations))?;
        let output = analyzer.dispatch_analysis(&mut observations)?;
        println!("{kind:?}: {:?}", output.output_status);
    }
    Ok(())
}
```

### 4.4 Run it

Run it from the crate's root directory. The SMT query files are written to
`./src/output/`, relative to the current working directory.

```bash
cargo run --release
```

The first build takes a few minutes. The output starts with the phase
report:

```text
Initial SAT: VerifiedWitness; 0 solver calls

1. UCP (0.00 s)
  Targets: 2 exact values, 0 domains. New: 2 exact, 0 new/refined domains.
  a = 7 (exact)
  b = 3 (exact)

1. SMT (0.03 s; 4 solver calls)
  ...
    x in {-5, 5} (covering domain); complete domain
  ...
Result: Analyzed; 2 exact values, 1 domains; 3 complete domains; 1 non-unique, 0 unresolved; 4 solver calls; ...
```

After the phase report come the full report (one line per secret cell, e.g.
`A-0-0: Unique; Recovered; ... Exact(7)`), then
`Validation: VerifiedDomains`, then the four Korrekt checks. `x` can be `5` or
`-5`, so `UnderconstrainedCircuit: Underconstrained` is the correct result for
this example.

If you use git for this crate, add `src/output/` to its `.gitignore`.

### 4.5 Adapting it to your circuit

Work through these steps in order:

1. **Circuit.** Replace section 1 with your `Circuit<Fr>` implementation.
   `use korrekt::circuit_analyzer::halo2_proofs_libs::*;` re-exports the Halo2
   types the analyzer is built against: `Circuit`, `ConstraintSystem`,
   `Layouter`, `Value`, `Column`, `Advice`, `Instance`, `Fixed`, `Selector`,
   `TableColumn`, `Expression`, `Rotation`, `MockProver`, and `Fr`. `Fr` is the
   **Pasta `Fp`** field of the zcash backend. If your code imports
   `halo2_proofs::...`, either change those imports to the re-exports or see
   [4.6](#46-if-your-circuit-already-lives-in-another-crate).
2. **`K`.** Use the same `k` you pass to `MockProver::run`.
3. **Witness and public values (a)–(c).** Construct the circuit with one valid
   witness and collect the public values it produces. They are the same values
   you pass to `MockProver::run(K, &circuit, vec![col0, col1, ...])`. The value
   at instance column `c`, row `r` gets the key `"I-c-r"`. List only the instance
   cells that the observer actually sees. Values are `BigInt`s: negative numbers
   mean `p - |v|`, and values up to full field width are accepted.
4. **Secret cells (d).** A target is `CellId::advice(column_index, absolute_row)`.
   - `column_index` is the position of the column among your
     `meta.advice_column()` calls (0, 1, 2, ...).
   - `absolute_row` is where the floor planner placed the cell. Read it from
     `layout.regions` and don't hard-code it. Uncomment the `println!` in (d) to
     list every advice cell with its region name, column and row. Then match
     on the region names you passed to `assign_region` (as the example does).
   - Choose only the secrets you care about. Intermediate cells are analyzed
     anyway and do not need to be targets.
5. **Lookups.** Private recovery requires
   `LookupMethod::InlineConstraints` and lookup tables that are **fixed,
   unrotated** columns (the usual `TableColumn` / `assign_table` pattern).
6. **Run** with `cargo run --release` and read the report (section 5).

### 4.6 If your circuit already lives in another crate

Add that crate as a dependency of `my-circuit-audit` and keep both `[patch]`
sections. The patch makes your crate and `korrekt` compile against the **same**
instrumented Halo2, so the types match:

```toml
[dependencies]
korrekt = { path = "../halo2-analyzer-fork/korrekt" }
my-circuit = { path = "../my-circuit" }       # or { git = "...", rev = "..." }
num-bigint = "0.4"
anyhow = "1"
```

- If your crate depends on `halo2_proofs = { git = "https://github.com/zcash/halo2.git" }`,
  the existing `[patch."https://github.com/zcash/halo2.git"]` entry already
  covers it.
- If it depends on `halo2_proofs` from crates.io, also add the following. The
  fork is version `0.3.0`, so your requirement must accept `0.3.0`.
  ```toml
  [patch.crates-io]
  halo2_proofs = { git = "https://github.com/Analyzable-Halo2/zcash-halo2.git", rev = "7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb" }
  ```
- Your circuit must be generic over, or instantiated with, the zcash backend's
  Pasta field (`Fr` above).

[external-evaluation/permutation](external-evaluation/permutation/) is a working
example of this setup. It imports an unmodified circuit from someone else's Git
repository and runs the full recovery on it.

### 4.7 Without a witness

If you have no valid witness, call `analyze_private_recoverability` instead
(same arguments, same module) and pass the circuit built with
`MyCircuit::default()`. The first "does any witness exist?" check then runs in
cvc5 instead of MockProver. That can take much longer on large circuits; it is
limited by `initial_sat_timeout_ms`. In both variants, the recovery itself
never reads the witness values.

---

## 5. Reading the report

**Per secret cell** (lines such as `A-0-0: Unique; Recovered; ...`; `A-c-r` =
advice column `c`, row `r`):

| You see | Meaning |
| --- | --- |
| `Unique; Recovered; Exact(v)` | The public values determine the cell: it **leaks** and equals `v`. |
| `NonUnique; ...; Candidates({...}); domain complete: true` | At least two values are possible, and the set lists **exactly** the possible values. |
| `...; Candidates({...}); domain complete: false` | The true value is in the set, but some listed values may be impossible (a covering superset). |
| `Unique; UniqueWithoutValue` | Proven to be determined, but the value was not computed. |
| `Unknown; Unresolved; No recovered domain` | Nothing was proven either way. This is **not** a privacy guarantee; see the `limitation` field. |

Values are printed as signed field representatives: `-5` means `p - 5`.

**Overall status** (`Privacy analysis: ...` / `Result: ...`):

| Status | Meaning |
| --- | --- |
| `Analyzed` | The search finished normally. Some cells may still be unresolved. |
| `QueryLimitReached` | A query budget ran out (see section 6). |
| `SolverUnknown` | cvc5 returned unknown or timed out on a step the run depended on. |
| `Inconsistent` | No witness satisfies the circuit with these public values. Check the instance keys and values. |

The per-cell `limitation` field explains why a cell stayed open:
`QueryLimit`, `SolverTimeout`, `SolverUnknown`, `DomainSizeLimit` (more than 256
candidates), `ValueRepresentationLimit`, `NoConcreteValue` or `InconsistentContext`.

**Validation** (`validate_private_recovery_report`) re-encodes the original
circuit and the public values from scratch. It assumes nothing that the
recovery inferred, and checks that every reported domain covers all feasible
values. Possible results: `VerifiedDomains`, `Refuted` (with a counterexample),
`NoDomainClaims` or `Inconsistent`.

**Korrekt checks** print one status each:
`NoUnusedCustomGates` / `UnusedCustomGates`, `NoUnusedColumns` / `UnusedColumns`,
`NoUnconstrainedCells` / `UnconstrainedCells`, and
`Underconstrained` / `NotUnderconstrained` (plus `...Local` variants).

---

## 6. Tuning and limits

All settings are fields of `PrivacyAnalysisOptions`:

| Field | Default | Effect |
| --- | --- | --- |
| `solver_timeout_ms` | `None` | Time limit for each cvc5 call during the search. `None` falls back to the `HALO2_ANALYZER_SMT_TIMEOUT_MS` environment variable; if that is unset too, there is no limit. |
| `initial_sat_timeout_ms` | `None` | Time limit for the initial existence check when it runs in cvc5. |
| `max_semantic_queries` | 256 | Total uniqueness probes. |
| `domain_refinement.max_solver_checks` / `.max_candidates_per_cell` | 160 / 128 | Budget for shrinking existing candidate sets. |
| `domain_discovery.max_solver_checks` / `.max_values_per_cell` | 64 / 16 | Budget for enumerating values of cells that have no candidate set yet. |
| `search.retry_solver_timeout_ms` | 10 000 | Longer time limit for one retry of a timed-out target. |
| `compute_structural_baseline` | `false` | Also runs UCP without public values, for comparison only. |

`options.with_profile(PrivacyAnalysisProfile::PropagationOnly)` (also
`FastProbeOnly`, `RefinementOnly`, `DiscoveryOnly`) turns off the other
strategies. The profiles are meant for ablation studies. `Standard` is the
default and enables everything.

Known limits:

- Finite candidate sets are capped at 256 values per cell.
- Lookups must be inline, with fixed, unrotated table columns (section 4.5).
- Run one analysis at a time per working directory, because the query files
  in `src/output/` are shared.
- Use `--release`. Debug builds work but are much slower.
- The private-recovery path is tested on the default **zcash** backend only.

---

## 7. Troubleshooting

| Symptom | Fix |
| --- | --- |
| `Failed to execute cvc5` / `Failed to start solver` | `cvc5` is not on `PATH`. Check with `which cvc5`. |
| cvc5 errors about finite fields or the `FF` logic | cvc5 was built without CoCoA. Rebuild with `--cocoa --gpl` (section 2). |
| Compile errors about private fields, or mismatched `halo2_proofs` / `halo2curves` types | The `[patch]` sections are missing or don't match your dependency's source (section 4.2 / 4.6). |
| Git fetch errors during the first build | The first build needs network access. Later builds can use `--offline`. |
| `MockProver ... assert_satisfied` panics | The witness and public values don't match. Fix those before analyzing. |
| `Select at least one private advice cell` | Step (d) selected nothing. Print the cells and check the region names and column indices. |
| `Privacy analysis requires inline lookup constraints ...` | Set `lookup_method: LookupMethod::InlineConstraints`. |
| `... requires concrete, unrotated fixed lookup tables` | A lookup table uses advice columns or rotations; this is not supported. |
| Status `Inconsistent` | The public values cannot be produced by the circuit. Check the `I-c-r` keys. |
| Many `SolverTimeout` / `QueryLimitReached` | Raise `solver_timeout_ms` and the budgets in section 6. |
| Random test failures in this repo | Solver-backed tests must run with `--test-threads=1`. |
| A new nightly breaks the build | Pin a dated nightly in `rust-toolchain.toml` (section 1). |

---

## 8. Thesis examples and formal verification

### Examples from the thesis

These are the experiments of the evaluation chapter (Chapter 6) of the thesis
*Automated Detection of Information Leakage in Overconstrained ZKP Circuits*.
Each one is a full UCP + SMT recovery, checked against an independent
reference. They are `#[ignore]`d tests, so they need `--ignored`; run them one
at a time, in release mode.

| Thesis section | Experiment | Test name | Thesis run |
| --- | --- | --- | --- |
| 6.2.2 | Base invoice | `thesis_invoice_recovery_smoke` | 0.91 s, 6 SMT calls |
| 6.2.3 | Invoice with approval-dependent surcharge and fee catalogue | `thesis_invoice_surcharge_catalog_recovery` | 4.60 s, 13 SMT calls |
| 6.2.4 | Control: invoice with unrestricted surcharge | `thesis_invoice_approval_control_recovery` | 44.53 s, 88 SMT calls |
| 6.3 | External Zordle circuit, game `fluff` | `zordle_recovery_upstream_game` | 174.42 s, 85 SMT calls |
| 6.3 | External Zordle circuit, game `light` | `zordle_recovery_varied_game` | 326.85 s, 95 SMT calls |

```bash
# replace <test name> with a name from the table
cargo test --release -p korrekt --lib <test name> -- --ignored --nocapture --test-threads=1
```

The times are single runs on the thesis machine and only indicate the order of
magnitude. The invoice circuit, its reference model and further commands are
described in
[korrekt/src/circuit_analyzer/ucp/thesis_examples/README.md](korrekt/src/circuit_analyzer/ucp/thesis_examples/README.md)
(in Hungarian). The Zordle circuit is vendored unchanged in
[korrekt/src/circuit_analyzer/ucp/external_examples/zordle/](korrekt/src/circuit_analyzer/ucp/external_examples/zordle/).

Setting `UCP_DEMO_VERBOSE=1` makes the thesis examples print full reports.

Full test suite (takes several minutes; long measurements only run with `--ignored`):

```bash
cargo test -p korrekt -- --test-threads=1
```

### Formal verification

The Lean 4 proofs of the recovery core are in
[korrekt/verification/](korrekt/verification/README.md). They are not needed to
analyze circuits. To check them, run the following from the repo root (needs
`curl` and `jq`):

```bash
bash korrekt/verification/aeneas/bootstrap.sh   # installs the pinned Aeneas, Lean and nightly toolchains
bash korrekt/verification/aeneas/verify.sh      # re-extracts the Rust sources and checks every proof
```

What is proved, and where the trust boundary lies, is listed in
[THESIS_CLAIMS.md](korrekt/verification/THESIS_CLAIMS.md) and
[IMPLEMENTATION_STATUS.md](korrekt/verification/IMPLEMENTATION_STATUS.md).

---

## 9. Repository layout

| Path | Contents |
| --- | --- |
| `korrekt/src/circuit_analyzer/analyzer.rs` | Korrekt checks and the SMT backend (Halo2 → SMT-LIB, cvc5 calls) |
| `korrekt/src/circuit_analyzer/analyzable.rs` | Records regions, gates, copies and fixed values during synthesis |
| `korrekt/src/circuit_analyzer/ucp/` | Private-value recovery: extraction, propagation rules, search, reports ([module guide](korrekt/src/circuit_analyzer/ucp/README.md)) |
| `korrekt/src/circuit_analyzer/ucp/thesis_examples/` | Thesis invoice example with an independent reference model |
| `korrekt/src/circuit_analyzer/ucp/tests/` | Regression tests, demos, measurements, upstream fixtures |
| `korrekt/src/io/analyzer_io_type.rs` | `AnalyzerInput`, `VerificationInput`, analysis and lookup modes |
| `korrekt/src/smt_solver/` | SMT-LIB printer, supervised cvc5 process, response parser |
| `korrekt/verification/` | Lean 4 models and proofs |
| `external-evaluation/` | Standalone crates that analyze unmodified third-party circuits |

---

## 10. How it works

1. **Synthesis.** The circuit is synthesized with an analysis layouter that does
   not create a proof. It records every region, enabled selector, fixed value,
   copy constraint and lookup.
2. **Extraction.** Every enabled gate polynomial, copy constraint and lookup is
   turned into equations over concrete cells. This is the *UCP problem*.
3. **Propagation (UCP).** Starting from the public values, inference rules run
   until nothing changes (a fixpoint): linear elimination, wrap-aware interval
   bounds, base and bit decomposition, invertible linear systems, the
   "all-but-one is zero" rule, and lookup tuples. The rules derive exact values,
   finite candidate sets and uniqueness facts.
4. **SMT search.** When propagation gets stuck, the scheduler picks the most
   promising cvc5 query for the original circuit: a uniqueness probe, a
   candidate-set refinement, or value discovery. New facts go back into UCP,
   and propagation runs again.
5. **Report.** The final report lists each target with its value or candidate
   set, its completeness and uniqueness, and which limits were hit. An optional
   fresh SMT pass validates every reported domain.

The original Korrekt checks (unused gates, columns and cells; the
underconstrained check) use the same synthesis step. They are explained in the
[upstream README](https://github.com/quantstamp/halo2-analyzer#how-it-works).
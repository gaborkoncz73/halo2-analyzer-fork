# Full-Width Private Recovery

## Purpose

The TDK abstract distinguishes proving uniqueness from practically recovering a
private value. The original signed-i64 Delta limit prevented recovery of many
ordinary field elements even when a concrete value was easily computable. Delta
now stores BigInt representatives with a magnitude limit of `MAX_VALUE_BITS = 4096`.
The scalar, Base-Conv, and All-But-One concrete-value paths share the same bound.
This covers the supported Halo2 fields without claiming unbounded arithmetic.

`MAX_FINITE_DOMAIN_SIZE = 256` still bounds finite sets and Cartesian-product
exploration. An oversized value or set aborts that inference; no truncated set is
exported as a complete domain. The bit limit bounds stored values, not every
temporary arithmetic allocation or the time spent in UCP.

Field arithmetic uses the actual field modulus and a signed representative.
For example, `p - 1` can be stored as `-1`; the SMT bridge maps it back to the same
field element. Integers cannot be compared as ordered field elements without an
explicitly justified range interpretation.

## Demonstration

The new Halo2 regression circuit uses a public observation `m = 1`:

```text
secret = 2^253 * m
derived = secret + 7
```

UCP recovers both values exactly without semantic cell queries. A fresh analyzer
then checks their entailment from the original constraints and observations.
Additional tests cover `-2^253`, direct SMT-only model recovery, and deliberately
incorrect advice assignments: recovery must use the constraints, not those
assignments. The context is satisfiable even when the supplied witness is wrong.
This is an illustrative leakage circuit, not an external application or a claim
that the relationships are cryptographically hard to invert.

```sh
cargo test -p korrekt --lib wide_value_tests -- --nocapture --test-threads=1
```

## Remaining Limits

- Public observations now accept BigInt values, also bounded to a 4096-bit raw
  magnitude. Oversized inputs return errors before field reduction or solver queries,
  even if their reduced field representative would fit.
- A finite domain is a proven candidate superset, not proof that every candidate
  is feasible, nor a measured entropy or security level.
- Solver budgets now supervise each direct CVC5 process; they are not an end-to-end
  deadline. Expired processes yield unknown, never a recovered value from partial
  output. See [bounded recovery](bounded-private-recovery.md).
- Passing fresh SMT checks and regression tests is not a formal proof of the
  entire implementation. The abstract's correctness argument and broader external
  evaluation remain separate work.

## Public Observation API

`VerificationInput.instance_cells` and `Analyzer.instance_cells` now use
`HashMap<String, BigInt>`. This changes source compatibility for callers that
directly construct maps of primitive integers. Convert values with `.into()`, or
use `VerificationInput::new`, which accepts an existing i64 map or BigInt values:

```rust
use korrekt::io::analyzer_io_type::{
    AnalyzerInput, VerificationInput, VerificationMethod, LookupMethod,
};
use num_bigint::BigInt;

let public_value = (BigInt::from(1) << 200usize) * 3 + 7;
let input = AnalyzerInput {
    verification_method: VerificationMethod::Specific,
    verification_input: VerificationInput::new([("I-0-0".into(), public_value)], 1),
    lookup_method: LookupMethod::InlineConstraints,
};
// Small values are also supported: VerificationInput::new([("I-0-0".into(), 42i64)], 1).
```

Interactive Specific input parses signed decimal BigInt values rather than i64.
Privacy analysis, the UCP pipeline, semantic queries, and the legacy whole-witness
SMT path reduce concrete observations using the actual field modulus. The report
stores normalized observations, so fresh validation accepts a field-equivalent
representation, but still rejects a changed statement. Only Specific mode fixes
provided values; privacy analysis rejects concrete observations in other modes.

The added published-affine example uses `public = 3 * secret + 7` with
`secret = 2^200`, plus `derived = secret + 7`. It exercises a large public
observation through recovery, fresh validation, direct SMT-only recovery and the
UCP pipeline. Tests supply canonical, wrapped positive, and wrapped negative
representatives of that same public value. A separate control publishes
`secret + mask`: neither private operand becomes unique. This is an ambiguity
check, not a cryptographic privacy proof.

## Historical Verification Snapshot

With the default Zcash backend, `cargo test -p korrekt -- --test-threads=1`
passed 226 tests with no failures in 31.43 seconds; the opt-in measurement suite
remained ignored before the public-input API migration. This includes four full-width Halo2 tests, large-root/domain-limit
checks, and five solver-supervision tests. These are regression results, not a
new repeated release-performance benchmark.

`cargo check -p korrekt --all-targets`, formatting checks, and `git diff --check`
passed. Workspace-wide `cargo check --all-targets` remains blocked by the separate
`benchmarks` package's external legacy analyzer dependency, which imports the
unavailable Halo2 `arithmetic::FieldExt` API. Other backend feature configurations
were not tested in this step.

After the public-input migration, the same default-feature serial test command
passed 233 tests with no failures in 30.71 seconds (one opt-in measurement test
ignored). The eight wide-value Halo2 tests cover the original private-value cases
and the new large-public-observation cases; three input-unit tests cover small-map
conversion, signed decimal parsing, and both signs of the bit-limit boundary.
The package-wide check and formatting checks also passed. The workspace benchmark
dependency limitation remains separate and unchanged.

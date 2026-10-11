# Compositional Leakage Through Reused Linear Masks

## What This Demonstrates

Two public observations can jointly determine a private input even when neither
observation determines it on its own. This is a synthetic finite-field example,
not a cryptographic commitment scheme or a claim about protocol zero-knowledge.

The demo uses the existing recovery and independent validation APIs unchanged.
The circuit variants are in `korrekt/src/circuit_analyzer/ucp/demo_tests.rs`, and
the repeated measurement suite reuses those same gates.

## Three Controls

| Variant | Constraints | Public Observations | Expected Recovery |
| --- | --- | --- | --- |
| One publication | `s + r = a` | `a = 100` | Neither `s` nor `r` is unique. |
| Reused mask | `s + r = a`, `2s + r = b` | `a = 100`, `b = 142` | `s = 42`, `r = 58`. |
| Independent masks | `s + r1 = a`, `2s + r2 = b` | `a = 100`, `b = 142` | `s`, `r1`, and `r2` are not unique. |

The individual-publication test also checks `2s + r = b` alone with `b = 142`.
Only the published equation is configured into each one-publication variant;
the unobserved publication is not supplied as an analysis premise.

## Why Reuse Leaks

Over the circuit's field:

```text
b - a = (2s + r) - (s + r) = s
2a - b = 2(s + r) - (2s + r) = r
```

With fixed `a = 100` and `b = 142`, these force `s = 42` and `r = 58`.
The UCP value engine can solve the full-rank linear system without semantic cell
queries. The privacy API still performs its initial SAT check, so this is not a
completely SMT-free analysis.

The independent checker then verifies both exact claims on fresh SMT constraints,
without assuming the inferred values. A negative control replaces the claimed
secret by `17`; validation must refute it and return counterexample value `42`.

## Why The Other Cases Are Ambiguous

For the first publication, both `(s, r) = (42, 58)` and `(17, 83)` satisfy
`s + r = 100`. For the second publication alone, `(42, 58)` and `(17, 108)` satisfy
`2s + r = 142`.

With independent masks, both of these witnesses fit the same two observations:

```text
(s, r1, r2) = (41, 59, 60)
(s, r1, r2) = (17, 83, 108)
```

MockProver accepts both witnesses. SMT reports `NonUnique` for all selected cells,
and changing the supplied witness does not change the privacy report. No exact
value is claimed, so domain validation returns `NoDomainClaims`, not a privacy
certification.

This establishes ambiguity in the modeled relation. It does not measure entropy,
validate a randomness distribution, or prove the security of a masking protocol.

## Run

From the repository root:

```sh
cargo test --offline -p korrekt demo_linear_masking -- --nocapture --test-threads=1
cargo test --offline -p korrekt privacy_measurement_smoke_covers_compositional_masking -- --test-threads=1
```

The demo prints the recovery reports and the successful independent validation.
The measurement suite additionally compares the same cells against the SMT-only
reference and exports recovery and validation timings separately. Its new cases
are `mask_single_publication`, `mask_reused_composition`, and
`mask_independent_publications`. See [measurement instructions](private-recovery-measurements.md).

## Local Measurement Snapshot

One release run used three measured repetitions after one warmup per case,
serial execution, and a 2000 ms per-query solver budget. Times are medians;
these small synthetic cases do not establish general performance guarantees.

| Case | Recovery (ms) | SMT-Only (ms) | Independent Validation (ms) | Recovery Speedup |
| --- | ---: | ---: | ---: | ---: |
| One publication | 17.83 | 18.49 | 4.07 | 1.04x |
| Reused mask | 3.97 | 19.17 | 17.77 | 4.83x |
| Independent masks | 27.63 | 28.38 | 3.99 | 1.03x |

For the reused-mask case, the median total recovery-plus-validation time was
21.71 ms, so the independent checking workflow was not faster than SMT-only.
For the ambiguous controls, validation only checks consistency because there
are no recovered-domain claims; it does not certify privacy.

The complete run finished ten cases; the 16- and 32-bit cases returned solver
`unknown` during the SMT-only initial SAT check and were excluded from speedups.
The raw, summary, and incomplete-case TSV files from this run are available at
`/tmp/compositional-recovery-measurements.tsv`,
`/tmp/compositional-recovery-measurements.summary.tsv`, and
`/tmp/compositional-recovery-measurements.incomplete.tsv` on this workspace.

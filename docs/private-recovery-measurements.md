# Private Recovery Measurements

## Purpose And Scope

The opt-in `privacy_measurement_suite` compares the same selected cells under the
same concrete public observations. It checks correctness before reporting times,
then independently validates every recovered domain against the original SMT
constraints. The fixtures do not use advice assignments as recovery facts.

This is a local measurement harness, not a broad external benchmark corpus or a
reproduction of the QED2 paper's evaluation. It includes three repository samples,
synthetic demos, one unchanged external Halo2 Book fixture (`external_upstream`),
and a separately marked local modification (`external_derived_control`). New
`external_gadget_harness` cases import real range gadgets, with local aggregation
circuits; these are not additional unchanged external applications.

## Cases

| Case | Origin | Selected Cells | Purpose |
| --- | --- | --- | --- |
| `two_bit_gates` | Repository sample | Two private digits | Public `3` exposes both digits as `1`. |
| `two_bit_lookup` | Repository sample | Two private digits | Same recovery with lookup-based boolean ranges. |
| `two_bit_missing_range` | Repository sample | Two private digits | Bug control: a duplicated boolean constraint permits multiple witnesses. |
| `halo2_book_original` | External upstream | Original private `a`, `b` | Public `c = 7a^2b^2 = 252` permits multiple input pairs. |
| `halo2_book_publication_control` | External-derived local control | Remaining secret `b` | Publishing `a = 2` and `ab = 6` additionally reveals `b = 3`. |
| `gadget_polynomial_interior` | Imported gadget harness | Two private bounded balances | Polynomial running sums, total `15`, multiple valid splits. |
| `gadget_lookup_interior` | Imported gadget harness | Two private bounded balances | Lookup running sums, same ambiguity control. |
| `gadget_polynomial_boundary` | Imported gadget harness | Two private bounded balances | Total `30` and four-bit ranges force both to `15`. |
| `gadget_lookup_boundary` | Imported gadget harness | Two private bounded balances | The same recovery using actual fixed-table range lookups. |
| `masked_sum` | Synthetic demo | Secret and nonce | Their public sum permits multiple operand values; not a cryptographic commitment. |
| `mask_single_publication` | Synthetic demo | Secret and mask | One public equation leaves both values ambiguous. |
| `mask_reused_composition` | Synthetic demo | Secret and reused mask | Two observations jointly reveal both values. |
| `mask_independent_publications` | Synthetic demo | Secret and two masks | The same two observations admit different secrets. |
| `packed_bits_4/8/16/32` | Synthetic demo | All private bits | Scaling: the public packed word exposes all its bits. |
| `hybrid_chain_12` | Synthetic demo | Twelve derived cells | An SMT-derived anchor unlocks value propagation; these are not private inputs. |

Repository sources are
`korrekt/src/sample_circuits/zcash/bit_decomposition/two_bit_decomp.rs` and
`two_bit_decomp_lookup.rs`. Synthetic fixtures are reused from `ucp/tests/demos/demo_tests.rs`
instead of introducing different copies of their gates.

Multiple witnesses in the missing-range control are not evidence of healthy
privacy. Likewise, the ambiguity of the synthetic masked sum is not a proof of
zero-knowledge or a cryptographic security level.

The [compositional masking demo](compositional-masking-demo.md) explains the three
publication controls and verifies alternate witnesses with Halo2 MockProver.

The [external Halo2 Book case](external-halo2-book-evaluation.md) documents the
pinned source, original-vs-modified distinction, and private-input selection.

The [imported range-gadget evaluation](imported-range-gadget-evaluation.md)
describes the pinned library dependency, strict running-sum bounds, and the
difference between a local harness and an unchanged external application.

## Compared Methods

**UCP + SMT recovery:** the existing private recoverability API, including its
initial SAT check, public-value initialization, fixed-point inference, and semantic
queries when needed. The current [selective export policy](selective-smt-domain-export.md)
omits unchanged extracted finite domains from recovery query assertions, not
from Delta or the report. Exact and domains beyond those extracted inputs remain exported.
The optional `compute_structural_baseline` comparison defaults to false and,
when explicitly enabled, runs after recovery and is included in API time. The TSV
metadata records this policy so earlier full-export runs remain distinguishable.

**SMT-only reference:** a fresh analyzer queries every selected cell directly,
without asserting UCP domains or uniqueness facts and without propagating learned
values between queries. It shares the same interface checks, circuit synthesis
and extraction setup. Extracted domains are constructed but never used as solver
premises. This is a cell-wise reference built on the current analyzer, not a claim
about the best possible SMT-only algorithm or the original whole-witness analyzer.

Per-cell uniqueness and recovered exact values must match between the two methods.
The reference does not infer multi-value domains, so these are checked by the
separate independent validation pass rather than compared as identical outputs.

The normal regression tests assert matching results and selected query counts,
never relative execution times.

## Measurement Protocol

The opt-in suite also includes `poseidon_publication_control`, classified as
`external_derived_control`, targeting the two private message words of a full
upstream Poseidon circuit with additional local publication constraints. The
same original-SAT guard and fresh validation requirements apply; unknown cases
are excluded, not assigned speedups. The separate digest-only bounded probe is
described in [Poseidon evaluation](external-poseidon-evaluation.md).

1. Run all cases serially because the analyzer currently uses a shared SMT file.
2. Discard one complete warm-up per case, including both methods and validation.
3. Repeat each case; alternate whether UCP or the reference runs first.
4. Validate every reported domain using a fresh analyzer after both methods.
5. Export every trial and compute separate median times, preserving raw results.

The explicit suite requires `HALO2_ANALYZER_SMT_TIMEOUT_MS`, passed to CVC5 as its
check budget and to the analyzer's supervisor as a per-process wall-clock budget.
An `unknown` answer aborts that case, which is recorded
separately and excluded from all speedup summaries. It is not labeled safe,
recovered, or refuted. Other errors, including mismatched results, fail the suite.
On process expiry, the supervisor kills and reaps CVC5 and discards partial output.
This does not bound synthesis, UCP, or total analysis time. With the variable
absent, ordinary analyzer calls retain their previous unlimited policy. Historical
measurement snapshots predating supervision used only the solver-managed limit;
new exports identify the process policy and stored-value bit limit in metadata.

Times include frontend setup and solver process/file overhead, but exclude Rust
compilation and the comparison asserts. Recovery and independent validation are
measured separately. `ucp_speedup` is the reference median divided by the recovery
median, excluding optional validation. `validated_ucp_median_ms` is the median of
each trial's recovery plus validation times; it is not the sum of two medians.

Recovery now returns structured reports for solver unknown, with per-cell reasons;
the harness also excludes these incomplete reports. Other failures still fail
the run. See [bounded recovery](bounded-private-recovery.md) for API-level limits
and the distinction between timeout, unsupported representation, and ambiguity.

Query counts refer to semantic cell queries, not individual solver checks. Each
ordinary variable query performs two solver checks, and each path also has an
initial SAT check. Fixed/permutation-constant shortcuts can avoid solver work.
Validation exports its actual solver-check count separately, including
`validation_subset_checks`. Current exports use schema
`private-recovery-measurements-v3`; the validation columns and
`validation_policy: original-subset-unsat-full-fallback` metadata distinguish
these runs from earlier validation protocols. An initial SAT stage may have one
or two attempts. The subset optimization changes validation, not the SMT-only
uniqueness reference.

Schema v3 also records target/bridge/retry/progress counts and the adaptive search
policy. The comparison uses the same per-process budget for recovery and the
SMT-only reference: its retry timeout floor is disabled. Query-limited reports
are incomplete, just like solver-unknown reports. See
[adaptive recovery](adaptive-private-recovery.md).

## Running And Exporting

From the workspace root, normal correctness checks:

```sh
cargo test --offline -p korrekt privacy_measurement_smoke -- --test-threads=1
```

The explicit release measurement suite:

```sh
PRIVACY_MEASUREMENTS_REPETITIONS=5 \
PRIVACY_MEASUREMENTS_OUTPUT=/tmp/private-recovery-measurements.tsv \
HALO2_ANALYZER_SMT_TIMEOUT_MS=2000 \
cargo test --offline -p korrekt --lib --release privacy_measurement_suite \
  -- --ignored --nocapture --test-threads=1
```

`PRIVACY_MEASUREMENTS_REPETITIONS` defaults to five and accepts 1 through 100.
`PRIVACY_MEASUREMENTS_OUTPUT` is optional. When supplied, the parent directory must
exist; the suite writes that TSV path and sibling `.summary.tsv` and
`.incomplete.tsv` files. Without
it, the summary is still printed. No extra dependencies or solver downloads are
required beyond the existing project setup.

Finite-domain SMT refinement and domain discovery are disabled in this
uniqueness/recovery comparison. Metadata records both policies and zero check
allowances explicitly. The separate [refinement](finite-domain-refinement.md) and
[discovery](smt-domain-discovery.md) demos measure additional analysis and do not
silently reuse these measurements as a speedup for stronger claims.

The separate [Optional Recovery Profile Measurements](private-recovery-profile-measurements.md)
compare enabled refinement, full discovery, and targeted discovery against the
baseline, and measure public-observation control separately. They preserve
partial attempts and per-cell evidence instead of extending this SMT-only
comparison with mismatched claim strengths.

The metadata records the schema, timestamp, debug/release profile, platform,
Rust/CVC5 versions, field modulus, git revision, dirty-worktree flag, and warm-up
policy, solver budget, and counts of completed/incomplete cases. Data rows identify the public observations, target role, repetition, run
order, structural counts, recovered/ambiguous cells, semantic query counts, and
validation results. Lines starting with `#` are metadata rather than TSV rows.

Each row is one concrete public context. These examples do not evaluate all public
inputs, exhaustively enumerate feasible witnesses, quantify entropy, or establish
inversion hardness.

Incomplete cases include the full error context and the duration of the attempted
case, which can include warm-up or earlier successful repetitions. They do not
contribute partial samples or artificial timeout values to the timing medians.

## Extending The Corpus

For a new circuit, record its provenance/version, genuinely secret input cell
locations, public observations, and an independently justified expected result.
Keep derived-witness performance controls separate from private-input examples.
Use the `measure` helper in `privacy_measurement_tests.rs`; add each case to the
explicit suite and a small correctness test before including its timing results.

Larger externally sourced Halo2 circuits, especially cryptographic computations
and composition-induced leakage, remain necessary for the TDK evaluation. These
local samples prepare the measurement method but do not replace that corpus.

## Initial Local Release Run

An initial run on 2026-10-08 used three measured repetitions, one warm-up, and a
2000 ms solver-managed budget per query. The profile was release on Linux x86_64,
with rustc `1.97.0-nightly` and CVC5 `1.3.5.dev+main@1e05d08b9`. These are illustrative
local observations, not portable performance guarantees or statistical significance
claims.

| Case | Recovery Median (ms) | SMT Reference Median (ms) | Validation Median (ms) | Recovery Speedup |
| --- | ---: | ---: | ---: | ---: |
| Two-bit gates | 3.69 | 18.73 | 18.09 | 5.08x |
| Two-bit lookup | 4.25 | 20.79 | 20.59 | 4.90x |
| Missing-range control | 24.44 | 24.59 | 14.92 | 1.01x |
| Masked sum | 17.93 | 18.47 | 3.99 | 1.03x |
| Packed 4 bits | 4.65 | 37.58 | 37.13 | 8.09x |
| Packed 8 bits | 159.33 | 1698.24 | 1684.05 | 10.66x |
| Hybrid derived chain | 16.96 | 123.40 | 124.67 | 7.28x |

The 16-bit and 32-bit cases returned solver `unknown` during the reference's initial
SAT check and are excluded, not assigned artificial speedups. The attempts took
approximately 2.01 s and 2.99 s; the latter illustrates that the solver budget is
not a strict process wall-clock deadline. Recovery for those cases was not reached
in this run, so it provides no comparative recovery result for them.

There are two useful conclusions. UCP reduces the need for individual cell queries
on determinate examples, but contributes little on the ambiguity controls. Also,
full independent SMT validation can consume the recovery savings: the validated
8-bit recovery median was 1843.38 ms, versus 1698.24 ms for the SMT reference. The
initial SAT check itself remains a scaling bottleneck. These costs must stay
visible in the TDK evaluation instead of being omitted from speedup claims.

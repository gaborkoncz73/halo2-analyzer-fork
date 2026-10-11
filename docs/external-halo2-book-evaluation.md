# External Halo2 Book Evaluation

## Provenance And Scope

This is the first pinned external circuit in the private recovery measurements.
It is the official [Halo2 Book simple example](https://zcash.github.io/halo2/user/simple-example.html)
originating in `zcash/halo2`, retrieved unchanged from the analyzer-compatible
`Analyzable-Halo2/zcash-halo2` fork at revision
`7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb`.
The unchanged source, SHA-256, original path, and MIT license are recorded in
`korrekt/src/circuit_analyzer/ucp/external_fixtures/README.md`.

This is an educational example, not a production application or an upstream
privacy vulnerability. The positive leakage control below is our own modification
and must not be counted as a second independent external circuit.

The real upstream implementation exercises multiple regions, advice copies,
permutation equalities, a fixed constant, selectors, a next-row query, and a
public instance binding. It is not replaced by a single equivalent polynomial.

## Unchanged Original

The original circuit proves a relation between private field inputs `a`, `b` and
the public value `c`:

```text
ab = a * b
absq = ab * ab
c = 7 * absq
```

For `c = 252`, both `(a, b) = (2, 3)` and `(1, 6)` satisfy the circuit.
The test verifies both assignments with Halo2 MockProver, then asks recovery to
analyze only the two genuinely private inputs. Both are `NonUnique`; no exact
secret value is claimed. Changing the supplied witness leaves the report unchanged.

Inputs are selected from the two upstream `load private` regions. Assertions
guard the expected region shape, cell types, and number of inputs; derived
intermediates and their advice copies are not counted as additional secrets.
Independent validation returns `NoDomainClaims`, not a privacy certificate.

## Local Additional-Publication Control

The adapter uses the same upstream chip and multiplication gates, but adds public
bindings for `a` and the intermediate `ab`:

```text
I-0-0: c = 252
I-0-1: a = 2
I-0-2: ab = 6
```

The remaining selected secret is `b`, not the intentionally published `a`.
Since `a` is nonzero, `b = ab / a = 3` in the field. Recovery reports `Unique`
and `Exact(3)`; a fresh SMT encoding independently checks that no other value
is possible. A fabricated `Exact(4)` must be refuted with counterexample `3`.

The test also supplies an invalid witness with `b = 4`. MockProver rejects that
witness, while analysis of the constraints under the fixed public observations
still recovers `3`. This checks that recovery does not sample the supplied witness;
it does not mean an invalid witness can produce a valid proof.

Missing any of the three required public observations is rejected rather than
silently guessing it or opening an interactive input prompt.

On the initial local run, the existing hybrid algorithm needed one semantic cell
query for this control. Correctness tests do not require a particular query count
or a speedup. Recovery and optional validation are measured separately.

## Running

From the repository root, run the circuit checks and same-target SMT comparison:

```sh
HALO2_ANALYZER_SMT_TIMEOUT_MS=2000 \
cargo test --offline -p korrekt --lib external_halo2_book -- --nocapture --test-threads=1
```

The [measurement suite](private-recovery-measurements.md) includes
`halo2_book_original` (`external_upstream`) and
`halo2_book_publication_control` (`external_derived_control`). It checks per-cell
agreement against SMT-only and validates domain claims before exporting timings.

## Local Release Measurement

On 2026-10-08, one serial release run used three measured repetitions after one
warmup per case and a 2000 ms solver-managed per-query budget. Times are medians,
not portable performance guarantees:

| Case | Recovery (ms) | SMT-Only (ms) | Independent Validation (ms) |
| --- | ---: | ---: | ---: |
| Unchanged original | 29.62 | 28.56 | 5.23 |
| Local publication control | 11.82 | 12.01 | 11.00 |

There is no meaningful speedup on these two small cases. Both recovery paths
needed semantic queries. The original has no recovered-domain claims, so its
validation timing covers consistency only. For the publication control, the
median recovery-plus-validation total was 23.43 ms; validation is an additional
cost, not part of the 11.82 ms recovery figure.

The run completed twelve cases in the full suite. The existing 16- and 32-bit
cases returned solver `unknown` during the SMT-only initial SAT check and were
recorded separately, not included in speedup summaries. Raw data is available in
this workspace at `/tmp/external-halo2-book-measurements.tsv`, with sibling
`.summary.tsv` and `.incomplete.tsv` files.

## Interpretation And Next Corpus Work

This establishes compatibility and per-instance recovery on one traceable external
example. It does not prove cryptographic privacy, general inversion hardness,
universal frontend correctness, or success for every public input.

The TDK still needs additional independent external circuits, preferably with
realistic range/lookup use and cryptographic computations. Unknown solver answers
must remain incomplete cases, not be presented as protected secrets.

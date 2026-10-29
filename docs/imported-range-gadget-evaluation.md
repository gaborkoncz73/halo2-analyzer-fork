# Imported Range-Gadget Evaluation

## Sources And Reproducibility

This evaluation calls external range-check implementations through the
`halo2_gadgets` Cargo dev-dependency, rather than copying or reimplementing them:

- `halo2_gadgets::utilities::decompose_running_sum::RunningSumConfig`
- `halo2_gadgets::utilities::lookup_range_check::LookupRangeCheckConfig`

The analyzer-compatible source is
[Analyzable-Halo2/zcash-halo2](https://github.com/Analyzable-Halo2/zcash-halo2),
revision `7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb`, package version `0.3.0`.
Both the root Halo2 patch and the gadget dev-dependency are explicitly pinned to
this same revision. The backend commit and field did not change; this prevents
mixing the current upstream gadgets with the older analyzer-compatible API.
Cargo confirms that the analyzer and gadgets share one `halo2_proofs` instance.

The algorithms originate in the Zcash Halo2 project. For the exact version used:

| Implementation | Pinned Path | SHA-256 |
| --- | --- | --- |
| Polynomial running sum | `halo2_gadgets/src/utilities/decompose_running_sum.rs` | `5b87bd31430f360e7830d54b84952fb4cc4bf146b4045e1d9068c3acdf2bb3e7` |
| Lookup running sum | `halo2_gadgets/src/utilities/lookup_range_check.rs` | `64ae61788bf0afea6f1d4d0121c8bcab5512bda7f0a54107a5d7df1c2d439c30` |

The source license is MIT OR Apache-2.0, as declared by the dependency. No gadget
source is redistributed as a fixture. `Cargo.lock` is ignored by this repository;
the explicit git revisions therefore matter, although registry dependency versions
still depend on the locally resolved lockfile.

The local harness is `ucp/tests/external/external_range_tests.rs`. It supplies private values,
the polynomial strict-mode constant column, the lookup table `{0,1,2,3}`, one
addition gate, and one public instance binding. All range gates, rotations,
running-sum assignments, and strict final-zero constraints come from the imported
gadgets. Table loading belongs to the caller in this API.

These are `external_gadget_harness` cases, not unchanged external applications,
not independently authored projects, and not newly discovered upstream bugs.
They extend structural coverage beyond the Halo2 Book fixture; they do not by
themselves fulfill the abstract's broader independent-application evaluation.

## Bounded Aggregate Example

Interpret two private field elements as small bounded balances:

```text
0 <= a <= 15
0 <= b <= 15
a + b = public_total
```

Each gadget decomposes an input into two two-bit windows. The actual cells are
running sums, with base four:

```text
z0 = private input
z0 - 4*z1 in {0,1,2,3}
z1 - 4*z2 in {0,1,2,3}
z2 = 0                 // strict mode
```

The polynomial implementation constrains each difference with a root polynomial;
the lookup implementation checks it against a fixed table. In both cases, `z1`,
`z2`, and advice copies are derived witnesses, not additional private inputs.
The harness locates `z0` from the two actual range regions and asserts the expected
layout before selecting it as a target.

With `public_total = 15`, `(a,b) = (3,12)` and `(7,8)` both satisfy the circuit.
MockProver verifies both, and the analyzer reports both inputs as `NonUnique`.
Changing the supplied witness does not change the recovery report. Both private
input domains are now recovered as `{0,...,15}`, and fresh SMT validation verifies
their coverage. These ranges already follow from the circuit without fixing the
aggregate, so they are not reported as public-dependent refinements.

With `public_total = 16`, the domains narrow to `{1,...,15}` without a semantic
cell query. The zero-query test reports unresolved uniqueness rather than
inventing a `NonUnique` conclusion. Independent validation verifies the narrowed
domains and refutes an incorrectly stronger `{2,...,15}` claim.

With `public_total = 30`, the range constraints force `a = b = 15`. Neither the
individual range checks nor the aggregate equation alone determines those inputs;
the leakage follows from their conjunction. Fresh SMT validation verifies both
exact values, and a fabricated `a = 14` claim is refuted with counterexample `15`.

The current engine needs zero semantic cell queries on this boundary case: the
range domains and aggregate equation suffice. The original SAT check still runs;
this is not an entirely solver-free privacy analysis. Tests enforce this zero-cell-
query recovery, never a speed ratio. The SMT-only reference asks about both
selected private inputs separately. See [relational Delta propagation](relational-delta-propagation.md).

## Controls And Limits

- The witness `(16,14)` has the same aggregate `30` but fails both strict range
  implementations. Merely computing a decomposition is not accepted as a range proof.
- Public total `31` is inconsistent with the two ranges. Initial SAT checking
  must prevent vacuous recovery, and fresh validation also reports inconsistency.
- Interior ambiguity is not a cryptographic privacy certificate. No distribution,
  entropy, or computational hardness claim follows from counting these cells.
- Lookup memberships now remain available throughout the Delta fixpoint, and
  polynomial roots may constrain a shared affine expression. Both use bounded
  finite sets, not intervals or a full relational-domain solver. Unsupported or
  oversized projections are left unresolved; they are never truncated.

## Run And Measure

```sh
cargo test --offline -p korrekt --lib external_range -- --nocapture --test-threads=1
cargo test --offline -p korrekt --lib privacy_measurement_smoke_matches_smt_on_imported_range_gadgets -- --test-threads=1
```

The existing serial measurement suite now includes:

```text
gadget_polynomial_interior
gadget_lookup_interior
gadget_polynomial_boundary
gadget_lookup_boundary
```

Each compares the same secrets, original gadget constraints, and public observation
against the SMT-only reference, with optional validation timed separately. Use the
[measurement instructions](private-recovery-measurements.md) for repeated release
runs and TSV exports. Solver unknown cases remain incomplete, not safe or recovered.

## Before Relational Propagation

Historical local release run on 2026-10-08, before the relational Delta changes:
one warmup and three serial measured trials per
case, alternating method order, CVC5 `1.3.5.dev+main@1e05d08b9`, and a 2000 ms
solver-managed per-check budget. Times below are medians, not general performance
guarantees. Both methods use the same two private inputs and public observation.

| Case | UCP + SMT (ms) | SMT Only (ms) | Speedup | Fresh Validation (ms) |
| --- | ---: | ---: | ---: | ---: |
| Polynomial, total 15 | 130.01 | 128.58 | 0.99x | 20.71 |
| Lookup, total 15 | 62.93 | 62.44 | 0.99x | 10.25 |
| Polynomial, total 30 | 76.81 | 127.84 | 1.66x | 128.32 |
| Lookup, total 30 | 265.87 | 443.57 | 1.67x | 443.03 |

The boundary cases used one semantic cell query with propagation versus two
SMT-only queries. Interior cases used two queries with either method and recovered
no exact values. Their validation result is `NoDomainClaims`: the validation time
there only covers the original satisfiability check, not a secrecy certificate.
Boundary validation independently verified both exact claims. Validation is timed
separately; adding it to recovery removes the speed advantage over unvalidated
SMT-only recovery in these examples.

The complete suite attempted 18 cases: 16 completed and two older packed-bit cases
(16 and 32 bits) returned solver `TIMEOUT`. They were excluded from speedup
summaries, not classified as privacy-safe. Raw local artifacts:
`/tmp/imported-range-gadget-measurements.tsv`,
`/tmp/imported-range-gadget-measurements.summary.tsv`, and
`/tmp/imported-range-gadget-measurements.incomplete.tsv`.

## After Relational Propagation

Another local release run on 2026-10-08 used the same protocol: one warmup, three
serial trials with alternating order, the same CVC5 build, and a 2000 ms per-check
budget. These are local observations, not a controlled cross-machine benchmark.

| Case | UCP + SMT (ms) | SMT Only (ms) | Speedup | Fresh Validation (ms) |
| --- | ---: | ---: | ---: | ---: |
| Polynomial, total 15 | 127.73 | 126.17 | 0.99x | 485.10 |
| Lookup, total 15 | 474.41 | 63.48 | 0.13x | 188.69 |
| Polynomial, total 30 | 25.59 | 126.99 | 4.96x | 127.33 |
| Lookup, total 30 | 89.55 | 438.03 | 4.89x | 436.67 |

Both boundary cases now use zero semantic cell queries rather than one. Interior
cases still use two queries, but now report and independently validate two finite
domains. Their validation work is greater than the earlier `NoDomainClaims` SAT-
only pass, so the validation columns do not represent identical tasks across runs.

The lookup interior recovery was about 7.5 times slower than SMT-only recovery in
this run. Exporting additional learned finite domains can make the solver search
harder. A later [selective export policy](selective-smt-domain-export.md) reduces
this regression while retaining the reported domains; this table records the
earlier full-export implementation.
The precision improvement therefore does not support a claim of universal speedup.
Including independent validation also removes the boundary speed advantage over
the unvalidated reference in these cases.

The suite again completed 16 of 18 cases. The packed 16/32-bit cases returned
`TIMEOUT`, were recorded as incomplete, and were excluded from speedup summaries.
The new raw, summary, and incomplete TSVs are
`/tmp/relational-delta-measurements.tsv`,
`/tmp/relational-delta-measurements.summary.tsv`, and
`/tmp/relational-delta-measurements.incomplete.tsv`.

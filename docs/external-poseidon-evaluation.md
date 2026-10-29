# External Poseidon Evaluation

## Source And Scope

The fixture is the real hash circuit from the upstream
[Halo2 Poseidon benchmark](https://github.com/Analyzable-Halo2/zcash-halo2/blob/7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb/halo2_gadgets/benches/poseidon.rs),
pinned to the analyzer-compatible revision `7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb`.
The contiguous circuit/spec excerpt is unchanged, uses the imported Pow5Chip,
and keeps 8 full rounds, 56 partial rounds, width 3, rate 2 and a two-word message.
There is no reduced-round or polynomial surrogate. Source/excerpt hashes and the
MIT notice are recorded in `ucp/tests/external/fixtures/README.md`.

This extends the evaluation to a cryptographic circuit, but does not establish
compatibility with a production application. It comes from the same external
project as the existing Book fixture, and must not inflate the count of
independent application sources. The extra-publication control below is ours,
not an upstream vulnerability.

## Cases

The unchanged circuit publishes only `Poseidon(a, b)`. The adapter computes that
public digest using the upstream native primitive with the same parameters.
Recovery is given the digest, not `a` or `b`. Only the two message cells in the
upstream loading region are selected as secrets; round states, copies and digest
cells are not counted as additional private inputs. Layout assertions guard this.
MockProver accepts `[2, 3]` with its digest and rejects a different message against
that same digest. This checks constraint satisfaction, not proof-generation or
the cryptographic ZK property.

The local control retains the full hash and additionally publishes:

```text
s = a + b = 5
t = a + 2*b = 8
```

Both message words are genuinely private inputs, not direct publications. However,
these combined observations expose them: `b = t - s = 3`, `a = 2*s - t = 2`.
The added observations are bound through permutation equalities. MockProver
checks the whole circuit and rejects changes to any public observation.

## Subsystem Precision

This case exposed a real UCP precision gap: the small full-rank message subsystem
was attached to a larger linear component with additional free cells. The previous
Delta solver required the entire component to be small and full rank.

The solver now also groups equations with exactly the same variable support and
solves eligible full-rank groups with the existing modular Gaussian elimination.
The additional grouping pass examines at most the first 256 linear equations per
iteration. The 64-cell/256-equation solving limits and domain-compatibility checks
remain. This limits precision, not correctness: any selected subsystem is still
a subset of the original equations. Groups do
not silently drop extra variables from their equations, and duplicate inferences
are merged deterministically. Singular groups yield no concrete assignments.

Local correctness argument: all solutions of the full conjunction must satisfy
each selected subsystem. If its coefficient matrix is full rank over the actual
prime field, its coordinates have one solution, so those values hold in every
full solution, even if other cells remain free. Existing Delta domains are respected.
This is an argument for this path, not a formal proof of the full implementation.
Tests cover attachment to an underdetermined/oversized component and enumerate
all satisfying assignments for representative systems over F3, F5 and F7.

The kernel test recovers `a=2, b=3` without seeding any advice assignments.
MockProver separately establishes that the fixture is satisfiable. The kernel
test alone is not an end-to-end privacy report or fresh full-SMT validation.

## Historical Bounded Outcome

On the local debug probe with a 2000 ms solver-process/check budget, both the
unchanged digest-only case and the publication control returned `SolverUnknown`
with `SolverTimeout` during the initial original-SAT check. Both returned zero
recovered domains and two unresolved targets, with no semantic cell queries.
Elapsed times were about 3.44 seconds per analysis, including frontend work;
the 2-second limit applies to the solver process, not the whole analysis.

These outcomes expose a scalability bottleneck, not a claim that Poseidon is safe,
broken, or inherently impossible to invert. The publication control is algebraically
recoverable, yet the API correctly withholds claims when it cannot establish
original satisfiability. The SAT guard was not weakened to make the demo pass.

The repeated measurement suite attempts `poseidon_publication_control` using its
existing same-target SMT-only reference and fresh validation protocol. If either
path or validation returns unknown, the entire case is recorded as incomplete
and excluded from speedup summaries. The digest-only probe records statuses
without presupposing whether its message words are unique.

The three-repetition local release run with the same 2000 ms budget completed
16 cases and recorded 3 incomplete cases: the Poseidon publication control and
the 16/32-bit packed-amount cases. Poseidon stopped at the initial SMT-only SAT
check after about 2.04 seconds, so no Poseidon speedup was exported. Raw results,
summaries and incomplete reasons were written to
`/tmp/poseidon-private-recovery-measurements.tsv`, `.summary.tsv` and
`.incomplete.tsv`. These are local measurements, not universal performance bounds.

## Current Recovery Path

The copy extractor now follows every non-self permutation edge rather than
filtering cells by `sizes[col][row]`. Upstream maintains cycle sizes at
representatives; some non-representative members still have size 1. The old
filter omitted real copy equalities and broke propagation through Poseidon state
copies. A four-member cycle regression covers both copy insertion orders.

Recovery now attempts a positive-only SAT check with temporary exact-value
candidates derived by UCP from the public observations and original constraints.
The full original constraints remain asserted. Only SAT proves original
satisfiability; UNSAT/unknown falls back to the original check. The candidates are
popped before recovery and are never imported from synthesized advice values.
See [SAT Hint Acceleration](sat-hint-acceleration.md) for the argument and limits.

The end-to-end publication-control test now reports `Analyzed`, two exact values
(`a=2, b=3`), one initial SAT attempt and zero semantic cell queries under a
2000 ms/process policy. One local debug run took about 1.90 seconds including
frontend work and propagation; the scoped SAT-only experiment took about 72 ms.
These are observations, not timing assertions or a repeated speedup estimate.

The fresh validator now also permits positive-only SAT hints and proves domain
exclusion using literal original-constraint subsets, with full-C fallback.
The control passes this fresh validation without assuming the recovered values;
see [subset validation](subset-domain-validation.md). The SMT-only performance
reference remains unchanged and can still time out, so validated recovery does
not by itself produce a completed comparative measurement.

## Running

```sh
cargo test -p korrekt --lib external_poseidon -- --nocapture --test-threads=1
cargo test -p korrekt --lib external_poseidon_records_bounded -- --ignored --nocapture --test-threads=1
```

Use the existing opt-in measurement command in
[Private Recovery Measurements](private-recovery-measurements.md) to obtain raw
and summary TSVs; incomplete cases have a separate file. There are no timing
assertions or fabricated speedups for unknown results.

## Current Verification Snapshot

After the adaptive search update, the default-backend suite passed 260 tests
with no failures and two opt-in tests ignored. The publication-control test checks
both exact values and fresh `VerifiedDomains`. The three-repetition release suite
still excluded the Poseidon comparison because its SMT-only initial SAT check
timed out. Search policy and schema-v3 artifacts are documented in
[adaptive recovery](adaptive-private-recovery.md).

## Historical Before Subset Validation

The final default Zcash backend package suite passed with 245 tests, zero failures
and two opt-in tests ignored (44.38 seconds). The explicit debug bounded probe
returned `SolverUnknown` with zero domains for the original case (one SAT attempt,
about 3.21 seconds), and `Analyzed` with both exact message values for the control
(one SAT attempt, zero cell queries, about 1.90 seconds). Fresh control validation
returned a typed `WALLCLOCK_TIMEOUT`, not `VerifiedDomains`.

## Historical Verification Snapshot

The default Zcash backend package suite passed with 240 tests, zero failures and
two opt-in tests ignored (42.20 seconds). The full Poseidon bounded probe and the
three-repetition release measurement suite were also run explicitly and passed;
their solver-unknown outcomes remain incomplete measurements. Package-wide
`cargo check -p korrekt --all-targets`, formatting checks for the changed Rust
modules and `git diff --check` passed. The pinned fixture/source SHA-256 values
were rechecked. Other Halo2 backends were not tested in this step.

## Next Corpus Work

This step does not complete the abstract's multiple-independent-application goal.
Initial external candidates were screened but not incorporated: the checked
Summa experiments use a different PSE API and had no explicit license in the
inspected checkout; the checked soundness-example repo also lacked a license,
and its Sudoku discussion was motivation rather than a Sudoku implementation.
No source from those repos is redistributed here.

Remaining work is to integrate licensed, pinned application circuits with clearly
defined public observations/private inputs, and improve the original-consistency
check for large deterministic computations without weakening its guarantees.

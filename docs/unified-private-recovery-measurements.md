# Joint Scheduler: Before/After Invocation Counts

## Method

Baseline: `a1c49765493b1fda99b9b57c6810bcc2035fbe1e`, with only the same test
harness and solver counter added. The original comparison below measures the
three-operation v2 joint scheduler; the two-operation integrated v3 follow-up
is reported separately below. Current behavior is described in
[unified-private-recovery.md](unified-private-recovery.md). Default Zcash/Pasta
backend, debug build, cvc5 `1.3.5.dev+main@1e05d08b9`, serial execution.

Five synthetic circuit variants, four option profiles, one warmup followed by
three recorded repetitions per combination: 60 recorded analyses per version,
not 60 independent circuits. Solver limit: 2000 ms per invocation; semantic
allowance: 8 attempts, refinement: 32 checks, discovery: 16 checks when enabled.
The complete harness specifies the remaining options.

Counts measure actual solver process invocations, including initial SAT, not
semantic cell-query counts. Independent validation runs outside the measured
counter interval and must accept every reported covering claim. All 60 paired
results have identical final cell domains, uniqueness classifications, and
overall statuses. There were no incomplete results or exclusions in this sample.

## Results

Each entry is the mean invocation count per analysis, **before -> after**.
Counts were identical across the three repetitions of each combination.

| Circuit | Semantic Only | Refinement Enabled | Discovery Enabled | Combined |
| --- | --- | --- | --- | --- |
| Two roots, no initial domain | 5 -> 5 | 5 -> 5 | 6 -> 6 | 6 -> 6 |
| Singleton, no initial domain | 3 -> 3 | 3 -> 3 | 4 -> 4 | 4 -> 4 |
| Lookup, two roots | 5 -> 5 | 18 -> 20 | 5 -> 5 | 18 -> 20 |
| Lookup, singleton | 3 -> 3 | 18 -> 3 | 5 -> 3 | 18 -> 3 |
| Lookup with Boolean offset | 5 -> 5 | 23 -> 23 | 5 -> 5 | 23 -> 23 |
| **Mean Across Five Circuits** | **4.2 -> 4.2** | **13.4 -> 10.8** | **5.0 -> 4.6** | **13.8 -> 11.2** |

Across all 60 recorded analyses: **546 -> 462 actual invocations**.
Mean: **9.1 -> 7.7**, a **15.38% reduction** for this equally weighted sample.
Of the 20 distinct case/profile combinations, 3 improved, 15 were unchanged,
and 2 worsened. No claim of universal improvement follows from this mean.

The largest gains come from trying fast singleton recovery before a large
finite-domain candidate batch. Shared SAT samples also eliminate duplicate
candidate checks: a dedicated regression needs 15 refinement checks after the
two feasible roots were already found, rather than 17 fresh checks.

The two regressions occur when early work on a dependent target costs two
invocations that later domain refinement plus UCP could have avoided. In the
refinement profile, fast uniqueness of that target costs two checks; in the
combined profile its independent discovery costs two. Reusing the root samples
saves duplicate feasibility checks but cannot undo this earlier redundant work.
The heuristic has no oracle for whether an expanded polynomial has one or two
roots, so it cannot guarantee the minimum number of calls on both cases.

These are invocation counts, not a general runtime speedup or a representative
application benchmark. Scheduling simulations and snapshot construction also
consume CPU time. Wider independent circuit coverage is still needed.

Raw measurements, including elapsed times and paired final results:
[before](measurements/unified-private-recovery-before.tsv),
[after](measurements/unified-private-recovery-after.tsv).

## Integrated Two-Operation Follow-Up

The same 60 recorded analyses were rerun after replacing the separate `Unique`
action with internal refinement/discovery probe strategies
(`refine-discover-integrated-probe-v3`). The same harness, options, warmups,
repetition count, and fresh validation were used. All 60 paired invocation counts,
final domains, uniqueness classifications, and statuses match v2 exactly.

The integrated version therefore still uses **462 total invocations**, or
**7.7 per analysis**, compared with the original baseline's 546 and 9.1. This
integration adds **no further measured call reduction** on this sample; its
benefit is a simpler two-operation workflow with preserved recovery behavior.
The earlier limitations and two regressions against the baseline still apply.

Raw current-version data:
[integrated v3](measurements/unified-private-recovery-integrated.tsv).

## Verification

The v2 package suite passed 396 tests, with four opt-in tests ignored. The
integrated v3 suite passed 402 tests, with four opt-in tests ignored. New checks
cover internal-strategy selection, the two-feasible-value guard, discovery
fairness, exact recovery with candidate enumeration disabled, and no repeated
probe after timeout fallback. The invocation measurement was also run explicitly
and passed. `cargo check --offline -p korrekt --all-targets` passed with the
repository's existing warnings. Other Halo2 feature backends were not tested.

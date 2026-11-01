# Casino Recovery and Constraint Controls

This suite uses the `CasinoCircuit` from
[upstream casino2.rs](https://github.com/teddav/halo2-soundness-bugs/blob/4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4/src/casino/casino2.rs),
at the same pinned commit as the square-root examples. It selects all real
private deposits, not the initial dummy row or derived running-sum cells.
The number of deposits defaults to four and can be varied independently of
the analyzer. No recovery rules or solver premises are specialized for this
example.

## Circuit and Local Controls

The original circuit has two advice columns (deposits and running sums), a
public total, a zero initial row, a running-sum gate, and one lookup argument
with 1000 entries, **0 through 999**. It is not a cryptographic hash circuit.
It publishes an exact total; it does not implement a separate less-than-one-
million check.

The original `if i > 1` condition skips the equation connecting the first
deposit to the initial sum. The intended equations are

```text
d_0 = 0, S_0 = 0
S_i = S_(i-1) + d_i    for every i = 1..n
S_n = public_total
```

The upstream code lacks the equation for `i=1`. Its first sum is consequently
free, and the public total does not constrain the individual deposits beyond
the lookup range. The host's honest witness generation computes the sum
correctly, but this does not replace a missing circuit constraint.

Four versions are explicitly distinguished:

| Version | First sum link | Lookup entries | Provenance |
| --- | --- | ---: | --- |
| Upstream | Missing | 1000 | Byte-for-byte original source |
| First-deposit control | Present | 1000 | Only `casino-first-deposit.patch` |
| Small-lookup original control | Missing | 16 | Only `casino-small-lookup.patch` |
| Small-lookup repaired control | Present | 16 | Both patches |

The first patch changes only `if i > 1` to `if i > 0`. The second changes
only the lookup range `0..1000` to `0..16`. These are **local circuit changes**,
not fixes or hidden settings in the analyzer. The small versions must not be
reported as unchanged external circuits. Comparing the two small versions
isolates the missing equation with an identical range, target set, and budget.

`prepare.sh` keeps the original source untouched, generates separate patched
copies under `target/`, and checks their SHA-256 digests. The same PSE API
facade and BN256 field used by the square-root suite are retained. These
tests concern MockProver and constraint analysis, not proving-key generation
or production protocol security; they do not claim to repair the entire
upstream application.

## Cases

For the small lookup, each deposit is in `0..=15`. The test checks that the
maximum integer sum is below the field modulus, excluding modular wraparound
from the reference argument.

| Version and public observation | Ground truth |
| --- | --- |
| Missing first link, total 0 | Every deposit still admits all 16 lookup values |
| Repaired first link, total 0 | Every deposit is exactly 0 |
| Repaired first link, total `15*n` | Every deposit is exactly 15 |
| Repaired first link, total 1 | Every deposit has complete domain `{0,1}`, with exactly one deposit equal to 1 |

The last domains are individual projections, not independent choices. The
suite checks a second honest witness with the single nonzero deposit in a
different position. None of those private values or reference domains is
supplied to recovery as a premise.

Observed four-deposit release outcomes:

| Case | Exact | Multi-value domains | NonUnique | Complete domains | Solver calls |
| --- | ---: | ---: | ---: | ---: | ---: |
| Small original, total 0 | 0 | 4 | 4 | 2 | 35 |
| Small repaired, total 0 | 4 | 0 | 0 | 4 | 0 |
| Small repaired, total 60 | 4 | 0 | 0 | 4 | 0 |
| Small repaired, total 1 | 0 | 4 | 4 | 4 | 4 |

UCP recovers all deposits for the boundary totals. For total 1 it narrows all
four domains from `0..=15` to `{0,1}`; SMT then certifies feasibility,
non-uniqueness, and completeness. Model projections from one candidate query
are reused for other targets. Completeness-only updates do not trigger a new
propagation phase. In the missing-link control the refinement budget is
exhausted before every candidate of every domain is checked; the report
retains that limitation instead of falsely certifying all domains complete.

The four-deposit small suite took about 15 s in one release run: approximately
14.18 s for the missing-link control, under 0.01 s per boundary recovery, and
0.92 s for total 1. These are single-run observations, not benchmark averages.
Preparation for target selection and compilation are outside the reported
recovery wall time. There is no separate post-recovery SMT validation.

The repaired controls were also checked at eight deposits: both boundary
observations recovered all eight values through UCP with zero solver calls;
total 1 yielded eight complete `{0,1}` domains and eight non-uniqueness proofs
in eight solver calls (about 1.99 s in one release run).

## Original 1000-Entry Lookup

The untouched large lookup is retained as an explicit resource measurement,
not silently replaced by the small range. At four deposits, `k=10`, and
3000 ms per solver invocation, the first-deposit-repaired 1000-entry variant
produced 10 solver timeouts, no recovered deposit values, and four unresolved
targets in approximately 30.63 s. This is a resource limitation, not evidence
that those deposits are non-unique or confidential: the reference zero-total
case is mathematically unique.

A separate explicitly executed measurement with a 500 ms per-call timeout
completed both original-table variants: each reported ten timeouts, four
unresolved targets, and no recovered domains, taking about 5.5 s per variant.
That passing measurement validates the handling of inconclusive outcomes,
not successful exact recovery.

The explicit UCP domain-size limit cannot represent the 1000-element set,
so it does not retain a truncated candidate set. The original SMT lookup
constraints are preserved. Globally active lookups also generate constraints
for unused advice rows, increasing query construction and solver effort.
The harness sizes `k` from the table and deposit count, with backend row
headroom: four- and eight-deposit small controls use `k=5`; the original
1000-entry versions use `k=10`.

The ignored full-lookup measurement allows an inconclusive report but checks
every reported conclusion against ground truth. A passing measurement does
not mean the solver recovered everything. The ordinary small-control tests
instead require their stated exact values and non-uniqueness conclusions.

## Run

From the repository root:

```bash
bash external-evaluation/soundness-bugs/prepare.sh
cargo test --release --locked \
  --manifest-path external-evaluation/soundness-bugs/Cargo.toml \
  external_casino -- --nocapture --test-threads=1
```

This runs the native controls and the three small-lookup tests. The original
1000-entry recovery measurement is ignored by default. To run it explicitly:

```bash
cargo test --release --locked \
  --manifest-path external-evaluation/soundness-bugs/Cargo.toml \
  external_casino_full_lookup_measurement \
  -- --ignored --nocapture --test-threads=1
```

To check eight deposits in the repaired small-lookup controls:

```bash
UCP_CASINO_DEPOSITS=8 cargo test --release --locked \
  --manifest-path external-evaluation/soundness-bugs/Cargo.toml \
  external_casino_small_lookup_repaired \
  -- --nocapture --test-threads=1
```

`UCP_CASINO_DEPOSITS` accepts 2 through 32. `UCP_CASINO_TIMEOUT_MS` overrides
the positive per-solver timeout (default 3000). All cases use the same
Standard strategy configuration: `2*n+4` semantic attempts, 32 refinement
checks, eight discovery checks with at most four sampled values per cell,
two bridge units, four no-progress units, and no semantic retries. All search
strategies remain enabled. Limits are cumulative within each recovery run.
The per-call solver timeout is not an overall wall-time limit. Increasing
the deposit count can exhaust a budget; it does not silently increase every
allowance or turn an unknown result into success.

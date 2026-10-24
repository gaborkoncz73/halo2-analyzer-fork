# Target Coverage And Adaptive Private Recovery

## Configuration

The privacy driver separates first attempts on selected private targets from
optional intermediate-cell queries and retries. This changes search coverage,
not the original constraints or what counts as a proof.

The current driver uses a [joint cell/operation scheduler](unified-private-recovery.md).
Refinement and discovery compete for the next step. A fast uniqueness/value probe
is an internal strategy of those operations, not a third scheduled operation.
The existing separate hard budgets and default-disabled domain enumeration
remain in effect; exact-only recovery stays available without enumeration.

```rust
use korrekt::circuit_analyzer::ucp::privacy::{PrivacyAnalysisOptions, PrivacySearchOptions};

let options = PrivacyAnalysisOptions {
    max_semantic_queries: 256,
    solver_timeout_ms: Some(2_000),
    search: PrivacySearchOptions {
        max_bridge_queries: 32,
        max_queries_without_progress: 32,
        max_retries_per_target: 1,
        retry_solver_timeout_ms: Some(10_000),
    },
    ..Default::default()
};
```

The default total increased from 32 to 256. The initial solver budget still
defaults to None, inheriting the environment or unlimited time. `search` is a
source-level API addition; existing struct literals can add `..Default::default()`.
The new search policy applies to the privacy API, not the legacy underconstrained
pipeline. Initial SAT and optional fresh validation remain separate stages.

## Scheduling And Retry Conditions

Before a non-target bridge query, reserve one remaining total-budget slot for
every unresolved target that has never been attempted. Bridges also have their
own total allowance. The stagnation limit stops optional bridge/retry work, never
a target's first attempt. A smaller hard total limit or an unknown initial SAT
check can still prevent coverage; missing coverage is reported explicitly.

With domain searches enabled, the bridge allowance is shared by semantic bridge
attempts and actual non-target domain checks. These are different units: a
semantic attempt normally invokes the solver twice. This option is not a global
solver-invocation limit. Domain bridges also consume their operation's hard
check allowance, while reserving first target opportunities in that allowance.

After the first target pass, an inconclusive target can be retried after actual
K/Delta progress or with a strictly larger solver budget. Per-target retry,
stagnation, and hard total limits still apply. Proven non-uniqueness and permanent
value-representation failures are not retried. Repeating a failed query without
new information or an increased budget is not allowed, even with a large retry
allowance. The default allows at most one retry per target.

The retry budget is the maximum of the initial budget and the configured retry
floor. An initially unlimited budget remains unlimited. A missing retry floor
uses the initial budget. Zero milliseconds is rejected before synthesis.

The mandatory original-SAT check retains its positive-only candidate policy.
An unknown initial check still yields no recovered facts; semantic retries do not
bypass nonvacuity. No candidate/model sample becomes an exact value without the
existing uniqueness proof. Malformed responses and execution errors remain errors.

## Progress And Accounting

Progress is an added unique cell, a newly constrained domain, or a strict
field-aware domain refinement. Repeated facts and field-equivalent values do not
count. Progress resets only `queries_without_progress`, never the total counters.

The driver retains the current propagation fixpoint across SMT steps. It reruns
propagation only when merging a result adds a uniqueness fact or changes a Delta
domain. Unchanged finite-domain checks, partial discovery samples, non-uniqueness
evidence, and inconclusive queries still update search bookkeeping, but do not
trigger redundant propagation. A new or narrowed domain, including an exact value,
is propagated before the next search step.

Reports now include:

- `semantic_queries`: target attempts plus bridge attempts.
- `search_statistics.target_queries`, `bridge_queries`, and `retry_queries`.
  Retries are already included in target queries, not added a second time.
- `search_statistics.bridge_domain_checks`: non-target domain checks, already
  included in the refinement/discovery totals, not an additional cost.
- `progress_rounds`, `queries_without_progress`, and a typed `stop_reason`.
- `search_statistics.propagation_runs`: recovery fixpoint runs, including the
  first run under public observations but excluding structural baseline analysis,
  initial SAT hints, and query-scheduling simulations.
- `unqueried_targets`: cells without an exact value or any uniqueness,
  finite-domain refinement, or domain-discovery attempt.
- Per-cell `query_attempts`.

Unresolved target queries produce `SolverUnknown`. Hard-total or stagnation stops
produce `QueryLimitReached`, distinguished by `stop_reason`. A successful retry
clears an earlier unknown from the final outcome. An unknown bridge does not
invalidate fully resolved targets. Unknown is never evidence of secrecy.

## Validation And Measurements

Fresh validation still assumes no recovered facts in its exclusion queries. It
uses the report's initial solver timeout, not automatically the larger retry
timeout. Recovery success therefore does not guarantee that optional validation
will finish under that shorter budget.

Same-target measurements disable the longer retry floor, keeping the same
per-process budget as the SMT-only reference. Retries after actual progress remain
allowed, but no hidden longer deadline is used. Schema v3 records search policy,
options, and per-trial target/bridge/retry/progress counts. Unknown and query-limited
cases remain incomplete and do not receive speedups.

Budgets do not impose an end-to-end synthesis/UCP deadline. The search policy does
not provide complete inversion or a formal proof of the analyzer. Optional
[finite-domain refinement](finite-domain-refinement.md) now checks small existing
sets with a separate budget and distinguishes complete from partial projections.
[SMT domain discovery](smt-domain-discovery.md) can find a small complete projection
without an existing candidate set, using its own hard total allowance. Its fair
rounds and UCP priority preserve per-cell samples; larger-timeout discovery retries
are separately opt-in and do not inherit the uniqueness retry floor.
Broader independent evaluation remains necessary.

## Regression Evidence

Tests cover target reservation after a bridge timeout; reserved-budget target-only
fallback; progress renewal without resetting total counts; retry after another
target's recovery; larger-budget retry without candidate assumptions; bounded
no-progress behavior; and field-equivalent facts that must not reset the counter.
Timeouts are injected deterministically; successful recovery paths use real SMT,
and selected reports are checked by fresh validation.

A Halo2 fixture additionally recovers forty independent expanded-square private
inputs beyond the old 32-query default. MockProver checks the fixture; each input
must be recovered as 1. This is a coverage regression, not a general recovery-rate
or performance estimate.

```sh
cargo test --offline -p korrekt --lib privacy::tests::search_ -- --nocapture --test-threads=1
```

## Local Verification Snapshot

The default-backend serial package suite passed 260 tests with zero failures and
two opt-in tests ignored (49.10 seconds). The ten new search regressions passed,
including actual forty-input recovery. Package-wide `cargo check -p korrekt
--all-targets`, formatting, and whitespace checks also passed. Other Halo2
backends were not tested in this step.

A three-repetition release measurement run under an equal 2000 ms/process budget
completed 16 cases and recorded 3 incomplete cases. The Poseidon publication
control and 16/32-bit packed cases stopped at the SMT-only reference's initial
SAT timeout, not a demonstrated recovery failure. No speedups were fabricated
for these cases. The local schema-v3 artifacts are
`/tmp/adaptive-private-recovery.tsv`, `.summary.tsv`, and `.incomplete.tsv`.
This is not a measured percentage of all practically recoverable secrets.

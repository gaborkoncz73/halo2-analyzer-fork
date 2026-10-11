# Optional Recovery Profile Measurements

## Purpose

The TDK abstract distinguishes uniqueness from practical value recovery and asks
for an empirical evaluation. This serial, opt-in suite measures the optional
recovery paths and the new original-SMT public-observation control together.
It does not change recovery defaults, UCP rules, SMT premises, or production APIs.

The existing [SMT-only comparison](private-recovery-measurements.md) remains a
separate experiment. This new experiment compares recovery configurations, not
an additional SMT-only algorithm. It reports precision and cost separately;
faster runs producing different claims do not receive a misleading speedup ratio.

## Profiles And Budgets

| Profile | Ordinary Cell Queries | Refinement Checks | Discovery Checks | Targeted Exclusions |
| --- | ---: | ---: | ---: | --- |
| `Baseline` | 32 | 0 | 0 | No |
| `Refinement` | 32 | 64 | 0 | No |
| `Discovery` | 32 | 0 | 32 | No |
| `TargetedDiscovery` | 32 | 0 | 32 | Yes |

Every profile uses the same explicitly supplied per-process solver timeout.
Longer retry budgets are disabled in both ordinary search and discovery. The
same selected cells and concrete public observations are used for all profiles
of a case. The independent validator and public-observation control run after
each recovery, including incomplete recovery attempts, with the same timeout.
The observation control has a separate hard allowance of 64 solver invocations.

These are separate allowances, not equal total budgets and not a global wall-clock
deadline. Ordinary cell-query counts are not solver-invocation counts. The suite
does not guess an aggregate solver total by doubling cell-query counts; constant
shortcuts and failure paths can differ. Initial SAT, refinement, discovery,
validation, and observation-control counters are exported separately. Discovery
and control subcounters must partition their actual invocation totals.

## Fixtures And Expected Projections

The suite reuses existing circuits rather than copying or replacing their gates.
The expected projections below are analytical facts about these small fixtures,
not answers supplied as recovery premises. Private advice assignments are never
used as inference facts.

| Case | Expected Marginal Values Under The Observations | Purpose |
| --- | --- | --- |
| `expanded_two_roots` | Secret `{3,7}`, derived cell `{0}` | Expanded `s^2 - 10s + 21 = 0` has no initial Delta seed. Discovery finds both roots, then UCP cancels the nonzero factor in `d(s-5)=0`. |
| `lookup_seeded_two_roots` | Secret `{3,7}`, derived cell `{0}` | Same equations with a 16-value lookup seed; refinement excludes infeasible candidates. Discovery alone intentionally does not enumerate an already-known domain. |
| `localized_expanded_singleton` | Secret `{21}`, derived cell `{23}` | Expanded square around the public value, with unrelated nonlinear gates; compares full and targeted discovery. |
| `intrinsic_singleton` | Secret `{1}`, derived cell `{3}` | Both exact claims hold even without concrete public values; control must say `AlreadyImplied`. |
| `mask_reused_composition` | Secret `{42}`, mask `{58}` | Two public observations jointly recover both; control must say `ObservationDependent`. |
| `masked_sum` | Both operands can independently take every field value | Ambiguity control. Partial discovery samples are not covering domains or evidence of cryptographic privacy. |
| `imported_lookup_projection` | Both balances `{1,...,15}` | Real imported four-bit range gadgets with total 16; tests finite projections and observation control. |

All but the last case are synthetic fixtures. The last is an
`external_gadget_harness`, not an unchanged external application. Cell exports
identify `private_input` versus `derived_witness`. Counts matching expected small
projections include the selected derived controls; they are not a percentage of
all practically recoverable secrets or an estimate of general detection recall.

A claimed domain must cover every analytically feasible value. False uniqueness,
false non-uniqueness, false domains, inconsistent valid fixtures, or rejected
independent checks fail the suite. An absent or broader domain is retained as a
less precise result. Equality with a fixture's expected finite projection is
counted separately from the recovery API's global `Analyzed` status.

For an exactly matched projection, a completed observation classification must
also match the fixture's expected public-data effect. A wider covering claim
can be intrinsic even if a narrower claim depends on publications; it is not
assigned the narrower claim's expected label.

## Protocol And Outputs

1. Run serially; the analyzer's SMT file paths are shared.
2. Record one warm-up for each case/profile, marked `repetition=0`.
3. Repeat each profile and rotate the profile execution order between rounds.
4. Check fixture correctness, then run fresh validation and observation control.
5. Preserve every attempt and compute completed-stage medians separately.

`SolverUnknown` and `QueryLimitReached` do not abort a case or erase earlier
attempts. Unknown validation errors are retained with their elapsed time and
diagnostic text. The validator currently returns no partial counter report on
that error path, so its check counts are `NA`, not invented zeros. Malformed
output, execution failures, refuted claims, and other correctness errors remain
fatal.

For output path `profiles.tsv`, three files are generated:

- `profiles.tsv`: raw attempts, including warm-ups; effective options, public
  values, recovery status/precision, search counters, full/subset discovery
  checks, validation/control results, and each stage's elapsed time.
- `profiles.cells.tsv`: every selected cell's domain, expected marginal values,
  role, uniqueness, UCP baseline, refinement/discovery evidence, limitations,
  observation effect, and unobserved counterexample.
- `profiles.summary.tsv`: attempt and completion counts per case/profile,
  expected-projection match range, and separate completed-stage medians.

The summary's `recovery_analyzed` count means the recovery API returned `Analyzed`,
not that every optional search exhausted its projection. A full-field ambiguity
control can establish `NonUnique` and finish with no covering domain while bounded
discovery remains partial. Raw rows therefore also record models found, partial
cell counts, exhausted budgets, and `optional_search_incomplete`; the summary
counts such attempts separately. `workflow_checks_completed` means the returned
claims were checked, not that all target values were enumerated. The expected
projection match counters remain the separate precision metric.
Historical partial search evidence is retained even if later UCP or an ordinary
SMT query independently recovers the cell exactly; the flag does not revoke that
separately checked exact claim.

Warm-ups and globally inconclusive stages are excluded from their stage medians,
but remain in raw output. A missing median is `NA`. The total workflow median
uses each completed trial's recovery + validation + control time, not a sum of
three independently calculated medians. It excludes compilation and measurement
assertions, while each analysis stage includes its own frontend setup and solver
process/file overhead. Completion counts must be read beside conditional medians:
a profile with many timeouts is not better merely because its successful runs
are fast. `NoDomainClaims` completes a check with nothing to certify; it is not a
privacy guarantee.

Metadata records schema `private-recovery-profiles-v1`, timestamp, profile,
platform, Rust/CVC5 versions, git revision and dirty-worktree flag, field modulus,
representation limits, all policy identifiers, effective budgets, and schedule.

## Running

Normal regression checks:

```sh
cargo test --offline -p korrekt privacy_profile -- --test-threads=1
```

Repeated release measurements:

```sh
PRIVACY_PROFILE_REPETITIONS=3 \
PRIVACY_PROFILE_TIMEOUT_MS=2000 \
PRIVACY_PROFILE_OUTPUT=/tmp/private-recovery-profiles.tsv \
cargo test --offline -p korrekt --lib --release privacy_profile_measurement_suite \
  -- --ignored --nocapture --test-threads=1
```

Repetitions default to 3 and accept 1 through 100. The timeout must be explicit
and positive. Output is optional; its parent directory must exist. Ordinary test
runs skip the full measurement suite. No new dependency is required.

These are local profile ablations, not a formal correctness proof, protocol-ZK
verification, statistically established speedups, or a large public benchmark
corpus. Broader external circuits and repeated independent environments remain
part of the TDK evaluation work.

## Local Release Snapshot

On 2026-10-11, the default Zcash/Pasta backend ran all 7 cases and 4 profiles
serially, with 3 measured repetitions plus 1 recorded warm-up per profile and
2000 ms per solver invocation. This produced 84 measured attempts, 28 warm-ups,
224 cell-evidence rows, and 28 case/profile summaries. The explicit suite passed
in 25.52 seconds, excluding Rust compilation. Platform: Linux x86_64; rustc
1.97.0-nightly; CVC5 1.3.5.dev+main@1e05d08b9. The dirty-worktree flag is recorded.

Selected medians (milliseconds):

| Case | Profile | Expected Small Projections Matched | Recovery | Validation | Observation Control | Workflow |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Expanded two roots | Baseline | 1/2 | 36.09 | 12.78 | 17.11 | 65.97 |
| Expanded two roots | Discovery | 2/2 | 40.40 | 17.09 | 27.73 | 85.22 |
| Lookup-seeded roots | Baseline | 1/2 | 40.51 | 23.32 | 36.04 | 99.91 |
| Lookup-seeded roots | Refinement | 2/2 | 79.21 | 29.54 | 44.26 | 153.20 |
| Reused mask | Baseline | 2/2 | 4.48 | 13.01 | 21.66 | 39.14 |
| Intrinsic singleton | Baseline | 2/2 | 17.17 | 23.54 | 23.61 | 64.30 |
| Imported lookup projection | Baseline | 2/2 | 486.10 | 249.14 | 194.83 | 932.20 |

The root cases show increased precision at an additional cost: the baseline
recovers the derived zero but does not report the exact `{3,7}` secret projection.
Discovery or refinement supplies that projection in its appropriate case.
Targeted discovery was not uniformly faster on these small examples. Validation
and full original observation control can cost more than recovery itself.

All 84 recovery reports returned `Analyzed`; 72 observation controls returned
`Analyzed`, and 12 returned `NoDomainClaims` for the full-field masked sum. There
were no solver-unknown stages or refuted domains in this run. Eighteen measured
attempts retained partial optional-search evidence: full-field enumeration cannot
finish under these caps, and some previously sampled cells were subsequently
resolved by other inference. Their partial evidence is not converted to a Delta
domain. This illustrates why API status, projection precision, and optional-search
evidence must remain separate metrics.

The generated raw, cell, and summary files for this run are at
`/tmp/private-recovery-profiles.tsv`, `/tmp/private-recovery-profiles.cells.tsv`,
and `/tmp/private-recovery-profiles.summary.tsv`. They can be regenerated with
the command above. These local results are illustrative, not statistically
established speedups or general recovery-rate estimates.

Verification on the default backend: full serial debug suite, 369 passed,
0 failed, 3 ignored, 58.42 seconds; the new profile suite was run separately in
release as recorded above. Eight new non-ignored regressions cover profile
options, projection correctness, public effects, warm-up exclusion, TSV alignment,
partial budgets, typed-unknown reporting, and historical partial enumeration.
`cargo check --offline -p korrekt --all-targets`, touched-file rustfmt checks, and
`git diff --check` passed. Existing unrelated compiler warnings remain. Other
Halo2 backend feature combinations were not tested in this step.

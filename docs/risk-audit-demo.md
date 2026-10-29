# Synthetic Risk Audit

The Zcash-backend fixture lives in
`korrekt/src/circuit_analyzer/ucp/tests/demos/risk_audit_demo_tests.rs`, a child module of
`demo_tests.rs`. It is a synthetic example, not an application or a claim that
the published outputs are safe to disclose individually.

## Constraints And Public Observations

The private score `x` has ten Boolean digits and is reconstructed from them.
Its public disclosures are a correlated tier lookup `T[x / 64]`, the Boolean
comparison `x > 600`, `x % 7`, its population count, and `(x % 64) % 9`.
The tier table is `[0,0,0,1,1,1,1,2,2,2,2,2,3,3,3,3]`.

Quotients and remainders have independent range lookups. The comparison uses
ten Boolean digits for a nonnegative difference: `x-601` in the true branch
and `600-x` in the false branch. These bounds prevent the field equations
from accepting a noncanonical integer division or the wrong comparison branch.

The calibration equation is deliberately expanded:

```text
s*s - 10*s + p = 0       public p = 21
h*(s - fixed_bias) = 0   fixed_bias = 5
t = copied_x + h
u = 2*t + 1
```

The first row computes the disclosures. The second row contains calibration,
a copy-constrained score, and the fixed bias. The third and fourth rows use
previous-row queries to compute `t` and `u`. Separate selectors activate the
four gate groups. All selected targets are advice cells, not public outputs.

For `x=713`, the disclosures are `(2,1,6,5,0)`. A separate exhaustive integer
oracle gives the following score-projection cardinalities as publications are
added: `1024, 320, 167, 24, 4, 1`. These are not entropy measurements.

| Publications | Feasible x and t | Feasible s | h | Feasible u |
| --- | --- | --- | --- | --- |
| First four | 601, 678, 692, 713 | 3, 7 | 0 | 1203, 1357, 1385, 1427 |
| All five | 713 | 3, 7 | 0 | 1427 |

The seeded variant adds `s in 0..15`. Under `p=21` it has the same solutions,
but supplies a covering domain for refinement. The unseeded variant supplies
no calibration domain, making domain discovery applicable.

## Tests And Evidence Boundaries

Run the regular tests serially:

```bash
cargo test --offline -p korrekt --lib demo_risk_audit -- --nocapture --test-threads=1
```

They check valid witnesses for both roots and every four-publication score
candidate, boundary scores, disclosure counterexamples, non-Boolean digits,
incorrect quotients/remainders, invalid tier pairs, and incorrect derived values.
Kernel results are compared with the analytical projections and with a different
valid witness. No oracle candidate list is supplied to the recovery API.

The conditional feedback unit test supplies the analytically proved domain
`s in {3,7}` to the kernel and checks that it derives `h=0` and propagates domains
through the copy/rotated dependencies. This is explicitly **not** a measurement
of successful SMT discovery in the full circuit.

The bounded end-to-end test checks every actual claim against the reference
projections, including completeness and uniqueness. It permits a typed
inconclusive solver outcome, but never promotes it to successful recovery.

## Experiments

The separate large-budget test enables all recovery operations for the complete
five-publication, unseeded circuit:

```bash
cargo test --offline -p korrekt --lib demo_risk_audit_large_limits -- --ignored --nocapture --test-threads=1
```

| Control | Large-budget allowance |
| --- | --- |
| Solver timeout per invocation | 120,000 ms |
| Semantic attempts | 32 |
| Refinement solver invocations | 512 |
| Refinement candidates per cell | 256 |
| Discovery solver invocations | 128 |
| Discovery retained values per cell | 16 |
| Optional bridge work | 32 shared allowance units |
| Optional work without knowledge progress | 64 |

`UCP_RISK_TIMEOUT_MS` can override the large test's timeout, for example to
`300000`. Optional validation inherits the recovery timeout unless
`UCP_RISK_VALIDATION_TIMEOUT_MS` is supplied. These are per-invocation limits,
not a two-minute total deadline: a successful initial SAT check may be followed
by many additional checks. Larger allowances do not guarantee solver completion.
The regular bounded test retains its 2,000 ms default, and the analyzer's global
defaults and 256-value representation bound are unchanged.

The larger opt-in matrix compares propagation-only recovery allowances with
refinement, discovery, fast probes, a combined configuration, and optional
non-target bridge work. The initial SAT check is still mandatory in every case.

```bash
UCP_RISK_TIMEOUT_MS=30000 cargo test --offline -p korrekt --lib demo_risk_audit_measurement_matrix -- --ignored --nocapture --test-threads=1
```

Each run prints its effective allowances, outcomes, elapsed recovery time,
propagation count, and separate solver counters, plus a `RISK_AUDIT_RESULT`
summary line. Semantic attempts are not necessarily individual solver
invocations and must not be added to domain solver checks as an invocation total.
These are ablations of the combined pipeline, not an SMT-only speedup benchmark.
Repeated controlled runs would be required for performance conclusions.

Optional fresh positive and deliberately false-domain validations can be enabled
with `UCP_RISK_VALIDATE=1`. `UCP_RISK_VALIDATION_TIMEOUT_MS` overrides only their
per-invocation timeout. Validation is skipped when there is no domain claim;
inconclusive validation is reported, not counted as a proof. Validation costs
are separate from recovery measurements. The fresh validator checks covering
claims, not feasibility of every candidate or the completeness flag itself.

### Original Limitation Before Relational Propagation

On the implementation run, the first-four/unseeded and all-five/seeded API cases
both timed out in their initial SAT check with per-invocation budgets of 2 seconds
and then 30 seconds. They produced no recovery claims. The standalone UCP kernel
retained a 147-value covering domain for `x`, not the four/one-value exact
projection; seeded calibration retained its initial 16-value covering domain.

That run demonstrated a harder analysis boundary,
not successful full-circuit recovery or an established speedup. The reference
oracle, MockProver checks, and conditional feedback test must not be confused
with a completed end-to-end solver analysis. The original field constraints and
representation limits are unchanged; no witness or recovered target equality
was added to make the solver pass.

### After General UCP Strengthening

The generic tuple-membership and finite-radix candidate rules described in
[ucp-relational-propagation.md](ucp-relational-propagation.md) change this result
without changing the circuit constraints or supplying the oracle to recovery.
The standalone kernel derives exactly `{601,678,692,713}` with four publications
and `Exact(713)` with all five.

A full five-publication, unseeded large-budget run with
`UCP_RISK_TIMEOUT_MS=5000` completed in approximately 6.29 seconds: one initial
SAT check, zero semantic attempts, eight discovery checks, and three recovery
propagation runs. It recovered `x=713`, `h=0`, `t=713`, `u=1427`, and the complete
non-unique domain `s in {3,7}`. This is a single run, not a statistical speedup
measurement; the larger search allowances did not all get consumed.

In a repeat with optional independent validation, recovery completed in about
6.27 seconds with the same results and counters, but the fresh positive and
negative validation queries remained inconclusive at a 5,000 ms invocation
limit. Do not report these validation attempts as verified or refuted claims.

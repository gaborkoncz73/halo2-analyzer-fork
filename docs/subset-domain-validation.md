# Original-Subset Domain Validation

## Two Separate Obligations

Domain validation still rebuilds the original Halo2-to-SMT model. Let C denote
its constraints and P the concrete public observations. For a claim x in D:

```text
1. Establish SAT(C AND P).
2. Establish UNSAT(C AND P AND NOT(x IN D)).
```

The first prevents vacuous conclusions on an inconsistent circuit. The second
proves coverage of all full-circuit solutions, not feasibility of every candidate.
No other reported domain or uniqueness claim is assumed.

## Safe Acceleration

For existence only, the fresh validator can compute untrusted UCP candidates H
from C and P. `SAT(C AND P AND H)` proves original SAT even if H was guessed
incorrectly. UNSAT/unknown does not prove original UNSAT and triggers fallback.
All hint scopes are popped. The report's claimed domains never seed H.

For exclusion, use a subset S of literal assertions already emitted into C:

```text
UNSAT(S AND P AND NOT(x IN D)) implies UNSAT(C AND P AND NOT(x IN D)).
```

Every full solution must satisfy S, so if even the weaker conjunction admits no
alternative, neither does C. Conversely, subset SAT may describe a solution
forbidden by an omitted constraint. Subset SAT/typed unknown therefore triggers
the full original exclusion query. Only a full-C SAT model is a counterexample;
only subset/full UNSAT proves exclusion. Malformed responses and execution errors
are never treated as proof or ordinary unknown.

Existential hints are not used in either exclusion formula. A SAT result with a
candidate x=v is not a uniqueness proof. The two opposite monotonicity arguments
must not be interchanged.

## Implementation And Limits

The original gate encoder retains up to 256 literal affine gate/permutation
equalities as it writes them into C. Fixed/selector columns are treated as
coefficients for this selection heuristic; advice/instance expressions have
degree one. Retaining a polynomial by mistake would affect efficiency, not the
subset implication: the formula is still an actual original assertion. The cap
can omit useful equations, but never adds a new constraint or truncates a domain.

The separate `src/output/private_domain_subset.smt2` file contains declarations,
the retained original equalities, normalized public observations, and only the
current negated membership claim. It contains no UCP assignments or earlier
domain claims. The full original file is kept for fallback.

Original satisfiability is established once and reused across validation queries.
Every full-query exclusion is scoped and popped, including on error. An internal
after-SAT entry point requires the same fresh, unchanged circuit/public context;
the public validator establishes that precondition before any query. Both paths
reject analyzers strengthened with inferred K/Delta facts.

The validator reports actual `solver_checks` and `subset_checks`: one or two
initial SAT attempts, then at most one subset and one full check per claim. Every
process has its own resource budget; synthesis and UCP have no total deadline.
The analyzer still uses shared output files, so tests/measurements remain serial.

## Evidence

The full upstream Poseidon publication control now validates both recovered
message words without assuming their values in the exclusion checks. One debug
run returned `VerifiedDomains`, two domain queries, three solver checks and two
subset checks, in about 1.63 seconds including frontend/candidate work. This is
a local observation, not a repeated performance ratio or universal bound.

Regression tests cover literal original-assertion provenance and hint isolation;
subset SAT/unknown fallback; nonlinear constraints omitted by the subset;
actual full-model refutation of a fabricated value; original inconsistency despite
an apparently sufficient affine subset; and existing domain, lookup, copied
constant, public-observation and scope-isolation cases.

The SMT-only measurement reference remains unchanged. Its timeout on a full hash
case cannot be used as a numeric speedup. Current measurements use schema v3 and
record the validation/search policies and per-trial subset/search counts.

This is per-instance SMT evidence, not a machine-checked proof of the Rust code,
the UCP rules, the shared frontend, or cryptographic zero knowledge. The original
digest-only Poseidon case remains resource-relative; no privacy conclusion follows
from an unknown answer. Multiple independent application circuits and the formal
correctness argument promised by the TDK abstract are still required.

## Running

```sh
cargo test -p korrekt --lib validation_ -- --nocapture --test-threads=1
cargo test -p korrekt --lib external_poseidon_publication_control_recovers -- --nocapture --test-threads=1
```

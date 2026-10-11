# Positive-Only SAT Hint Acceleration

## Motivation

Recovery used to ask SMT to establish original satisfiability before doing any
UCP value inference. Full cryptographic circuits could time out at this stage
even when public observations made their private inputs readily recoverable.

The recovery SAT stage now computes candidate exact values from the original UCP
problem and public instance observations. It never reads synthesized advice
assignments. These candidates are not reported until satisfiability succeeds.

## Logical Boundary

Let C be all original encoded constraints, P the concrete public equalities, and
H arbitrary candidate equalities. The only shortcut used is:

```text
SAT(C AND P AND H) implies SAT(C AND P).
```

This implication holds even if H contains a bad inference: a satisfying model of
the stronger conjunction also satisfies the original conjunction. In contrast,
UNSAT(C AND P AND H) does not imply UNSAT(C AND P). A rejected candidate might
simply be wrong. Unknown likewise establishes neither SAT nor UNSAT.

This establishes existence only. SAT with a candidate x=0 does not prove that x=0
is the unique solution. Ordinary UCP/SMT recovery still carries that separate
correctness obligation; the candidate model is never returned as recovered data.

## Implementation

1. Run UCP internally with original facts and concrete public observations.
2. Attempt hints only if at least one selected private target has a candidate
   exact value. Otherwise skip the extra solver attempt. Select exact advice-cell
   candidates that map to existing SMT variables.
   Finite sets are not expanded. Alias equalities are deduplicated.
3. Require an analyzer with no inferred K/Delta assertions. Prepare original
   public constraints, push a temporary scope and assert candidate equalities.
4. Request SAT only, without requesting any model values. All original gates,
   permutation constraints and inline lookup memberships remain active.
5. Pop the scope on SAT, UNSAT or solver error.
6. Accept only SAT. With no candidates, UNSAT or a typed solver unknown, perform
   the original unstrengthened SAT check. Malformed output/execution failures
   remain errors, not fallback success.
7. Continue the existing recovery driver only after satisfiability is established.
   It does not receive the temporary SMT candidates as premises or model values.

The per-process budget applies independently to both attempts. No hard total
deadline for UCP, synthesis or analysis is promised. The report's initial
`satisfiability_checks` records actual SAT-stage solver invocations (one or two).

The subsequent [subset validation step](subset-domain-validation.md) also uses
this existential shortcut on a fresh analyzer, with no report-domain premises.
Its domain-exclusion checks use literal original constraints only. The SMT-only
measurement reference remains unchanged. Poseidon control validation now succeeds,
but no speedup is inferred from the reference's unknown result.

## Copy Extraction Fix

The experiment exposed a separate completeness bug. Halo2's permutation assembly
updates cycle sizes at distinguished representatives, not every member. A member
can retain `size=1` while its mapping points to another cell. Filtering by that
size omitted genuine copy equalities.

The extractor now visits all mapping entries, skips self-edges and deduplicates
undirected equalities. Every emitted equality is a real permutation edge; no
extra constraint or synthesized witness value is added. Traversal remains linear
in the size of the permutation mapping rather than restarting full cycles.

## Evidence And Remaining Work

Regression tests cover multi-member cycles in both insertion orders, propagation
to every copied advice cell, rejected-candidate fallback, scoped candidate
removal, non-uniqueness after a successful candidate SAT check, and typed unknown
versus malformed solver failures. The full Poseidon publication control now
recovers both private message words with zero semantic cell queries.

The original digest-only Poseidon case is not declared secure by a timeout.
Independent domain validation now completes on the publication control using
the original-subset UNSAT rule. SMT-only queries on the large hash remain a
scalability task. This local SAT implication is not a formal
verification of the implementation, inference rules or circuit-to-SMT frontend.

The final default-feature serial package test run passed 245 tests with zero
failures and two opt-in tests ignored. Run the new cases with:

```sh
cargo test -p korrekt --lib sat_ -- --nocapture --test-threads=1
cargo test -p korrekt --lib copy_cycles_include -- --test-threads=1
cargo test -p korrekt --lib external_poseidon_publication_control_recovers -- --nocapture --test-threads=1
cargo test -p korrekt --lib external_poseidon_records_bounded -- --ignored --nocapture --test-threads=1
```

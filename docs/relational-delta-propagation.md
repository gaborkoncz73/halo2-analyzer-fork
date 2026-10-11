# Relational Delta Propagation

## Missing Information And Minimal Changes

The imported strict range gadgets constrain a running sum through two expressions:

```text
z0 - 4*z1 in {0,1,2,3}
z1 - 4*z2 in {0,1,2,3}
z2 = 0
```

Previously, three gaps prevented the analyzer from learning the input range:

1. The polynomial Root rule only recognized factors with one remaining cell.
   The imported gadget instead uses factors of an affine expression, and writes
   them with opposite signs: `word*(1-word)*(2-word)*(3-word)`.
2. Lookup extraction immediately tried to project each input membership into
   cell domains. A failed projection was discarded, even if a later equation
   could reveal the other operand's value.
3. Copy constraints retained references to assigned fixed constants, but their
   concrete values were not seeded into Delta. Thus the strict final-zero copy
   could establish uniqueness without revealing zero to value inference.

The existing finite-domain representation remains unchanged. In `value.rs`, Root
now identifies a common affine expression across equally or oppositely signed
factors and passes its finite root domain to the existing affine projection solver.
In `extractor.rs`, `UcpProblem.expression_domains` retains necessary unary lookup
projections, and referenced assigned fixed cells supply normalized constants.
Unknown or poisoned fixed cells supply no concrete values.

`UcpProblem::analyze_with_values` is the shared entry point used by privacy analysis
and the UCP/SMT pipeline. Its engine evaluates the zero equations and retained
memberships in one fixpoint, including after new concrete values arrive from SMT.
Existing expression-only engine entry points remain available without memberships.
The choose-variable lookahead remains an expression-only heuristic; omitting
memberships there affects query ranking, not the facts accepted by real propagation.

## Local Correctness Argument

Over the circuit's prime field, a zero product has a zero factor. If all factors
have affine parts equal to `L` or `-L`, each zero factor implies that the first
factor's expression takes one of the calculated constant offsets. Thus its root
domain includes every satisfying value. Different affine parts, unknown scales,
or an explicit zero factor are not treated as this Root pattern.

For an affine membership `a*x + rest in Omega`, the existing projector enumerates
the Cartesian product of the other operands' proven domains. This loses
correlations, but includes every actual combination. It solves for `x` using a
field inverse and includes every satisfying value. Unary projections of a tuple
lookup are necessary conditions only; the original SMT model keeps tuple
correlations and never replaces a table with its Cartesian product.

Every inferred cell domain is intersected with the existing domain. A singleton
intersection establishes uniqueness, even if neither operand domain was a
singleton. Failed or unrepresentable inferences preserve prior information.
Projections and retained table domains are bounded by 256 distinct values;
cross-product exploration also remains bounded. Oversized domains are not
truncated. Values now use signed BigInt representatives with a 4096-bit magnitude
limit, rather than the original i64 limit; see [full-width recovery](full-field-recovery.md).

This is a local mathematical argument for the new propagation paths, not a
machine-checked proof of the complete analyzer or its Halo2 frontend. Privacy
analysis still checks original satisfiability before reporting inferred domains.
Independent validation checks claims against the original circuit and observations,
without assuming the learned K or Delta facts.

## Demonstrated Outcomes

Two imported strict four-bit range checks and a public aggregate now give:

| Public Aggregate | Each Input Domain | Uniqueness Evidence |
| --- | --- | --- |
| 15 | `{0,...,15}` | SMT finds different valid inputs |
| 16 | `{1,...,15}` | Zero-query test leaves uniqueness unresolved |
| 30 | `Exact(15)` | Delta alone establishes uniqueness |
| 31 | No reported domains | Original constraints are inconsistent |

For 15 the range is structural, not a newly learned consequence of the concrete
public aggregate. For 16 and 30 the domains refine that structural baseline.
The 30 case needs zero semantic cell queries, but still has the initial SAT check.
None of these domain sizes or cell counts is a cryptographic security score.

Tests cover signed factors, all satisfying assignments of a small prime-field
example, missing final-zero information, holes in domains, singleton intersections,
zero factors, unknown scales, domain-size limits, and unassigned/poisoned fixed
constants. External gadget tests independently validate exact and non-singleton
domains, and refute both fabricated exact values and unjustified tighter sets.

```sh
cargo test --offline -p korrekt --lib -- --test-threads=1
cargo test --offline -p korrekt --lib external_range -- --nocapture --test-threads=1
```

## Performance Scope

More precise domains do not guarantee faster SMT solving. Recovery can avoid
cell queries when a domain becomes exact, but redundant finite-set assertions can
increase solver work in ambiguous cases. The privacy driver now omits unchanged
structural finite domains from its SMT assertions, while retaining exact and
new/refined facts. Full Delta and reported domains remain unchanged; see
[selective SMT export](selective-smt-domain-export.md). This is a performance
heuristic, not a universal speed guarantee. The existing same-target measurement
suite measures both effects and times independent validation separately. See
[imported gadget evaluation](imported-range-gadget-evaluation.md) for before/after
measurements and the distinction between local harnesses and external applications.

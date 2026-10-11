# Private Recovery Validation

## Scope

`analyze_private_recoverability` computes candidate domains for explicitly selected
private advice cells under concrete public observations. The optional
`validate_private_recovery_report` independently checks the domains on a fresh SMT
encoding of the supplied circuit. It never assumes recovered Delta facts or the
supplied advice assignments to justify a domain claim. Fresh UCP candidates may
guide a positive-only original-SAT check; they are untrusted search hints, popped
before checking exclusions. Reported domains do not seed those candidates.

Recovery and validation have separate timings and query counts. The ordinary
recovery API does not pay for this optional validation pass. Both currently use the
analyzer's shared SMT output file, so these analyses and their tests must run
serially.

## Checked Property

Let `C` be the constraints encoded by the Halo2 analyzer and `P` the supplied public
equalities. For a reported domain `D` of cell `s`, validation checks:

```text
SAT(C AND P)
UNSAT(C AND P AND NOT(s IN D))
```

The first check prevents vacuous claims on an inconsistent context. It may be
established by `SAT(C AND P AND H)` with temporary candidates H, which also proves
`SAT(C AND P)`. Rejected or unknown candidates require the original check.

For the second check, the validator may first use a literal original-constraint
subset S. `UNSAT(S AND P AND NOT(s IN D))` implies the displayed full-C UNSAT
property because every full solution also satisfies S. Subset SAT/unknown is
inconclusive and triggers a full-C exclusion query; its model is never accepted
as a full-circuit counterexample. See [Subset Domain Validation](subset-domain-validation.md).

If both properties
succeed, every satisfying assignment under these public observations has its `s`
value in `D`. For an exact domain `{v}`, this establishes that the reported value
`v` is the only possible value of `s` in this context. For a finite set it certifies
coverage, not feasibility of every candidate or independence between cells.

The argument depends on faithful circuit-to-SMT encoding and correct solver results.
This is per-instance validation, not a machine-checked proof of the Rust code, the
UCP inference rules, the frontend, or the cryptographic protocol.

## Procedure And Outcomes

1. Rebuild the analyzer from the original circuit with inline concrete lookup
   tables, validating the same private-cell selection and public interface as recovery.
2. Require the report's public observations to match the validation input.
3. Establish original satisfiability once before considering any domain claim.
4. For each domain, first try the bounded literal affine/permutation subset.
   Only UNSAT certifies exclusion. Otherwise search the full original circuit
   for a value outside the domain with a scoped assertion. Remove that assertion
   before checking another cell, including on solver failure.
5. Return `Entailed` or `Refuted` per claimed domain. A refutation includes the
   counterexample cell value, which is not a recovered secret value.

`VerifiedDomains` means all reported domains were entailed. Cells without a domain
remain `NoDomainClaim`; if no domains exist, the overall result is `NoDomainClaims`,
not a privacy guarantee. An inconsistent context is reported as `Inconsistent`.
Unknown subset attempts fall back to the full circuit; a full-check unknown is
an error, never a successful validation. Execution/encoding failures remain errors.
Fresh validation inherits the recovery report's effective per-check solver budget;
see [bounded recovery](bounded-private-recovery.md).

The validation pass deliberately does not certify `Unique`/`NonUnique` labels for
cells lacking concrete domains, refinement relative to the baseline, practical
inversion hardness, entropy, or the zero-knowledge property. Changes to the circuit
are checked against the newly supplied circuit; the report has no circuit fingerprint.

The separate [Public Observation Control](public-observation-control.md) additionally
compares a verified domain claim with original constraints before fixing public
values. It distinguishes observation-dependent coverage from intrinsic coverage;
neither its classifications nor ordinary validation certify cryptographic privacy.

## Usage

After obtaining `report` with the recovery API:

```rust
let validation = validate_private_recovery_report::<Fr, _>(
    &circuit,
    k,
    &analyzer_input,
    &report,
)?;
println!("{validation}");
```

From the workspace root, run the illustrative positive and negative cases with:

```sh
cargo test --offline -p korrekt demo_privacy_report -- --nocapture --test-threads=1
cargo test --offline -p korrekt demo_independent_validation -- --nocapture --test-threads=1
```

## Regression Evidence

Tests cover UCP and SMT recovery, deliberately fabricated exact values, finite-set
coverage, omitted feasible candidates, empty domains, field-equivalent signed
values, public instance bindings, copied constants, inline lookup ranges, query
scope isolation, absent claims, inconsistent contexts, and mismatched inputs.

Mutation tests are important: assuming the recovered value during validation could
make a false claim appear valid. The tests require an actual counterexample for a
false value, including when the rest of the report is correct.

Additional tests verify literal subset provenance, no SAT-hint contamination,
nonlinear full-check fallback when the subset admits a spurious alternative, an
actual full-model refutation, and original nonvacuity even when a subset could
prove the claimed value. The Poseidon publication control now validates both
message words; the independent SMT-only performance reference remains separate.

## Remaining Work For The TDK

Adapt the uniqueness and domain-inference correctness argument to the supported
PLONKish semantics, review the frontend assumptions, and evaluate recovery and
validation separately on externally sourced circuits. Successful validation of
the selected examples does not establish universal analyzer soundness or complete
privacy protection.

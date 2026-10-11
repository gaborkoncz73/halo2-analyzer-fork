# Soundness Regression Checks

This change addresses concrete counterexamples found during the privacy analysis
review. It does not claim a formal proof of the complete Rust implementation or
its circuit-to-SMT translation.

## Field Reasoning

The field-aware assignment path uses modular inversion and checks that the
coefficient is invertible before recovering a value. Integer nonzeroness is no
longer used to cancel a field-valued factor. Domains are normalized before the
zero/nonzero test, including noncanonical representatives supplied to the UCP API.
Field-aware APIs require the actual prime modulus of the circuit's field;
modulus-free helpers retain their integer interpretation and cannot justify
arbitrary finite-field arithmetic.

Raw `Known(0)` scalars are not nonzero. Root, Base-Conv and All-But-One parsing
retain zero factors rather than deleting them and accidentally strengthening a
tautology. All-But-One uses the modulus to compare exact representatives and
requires its roots `0..n` to remain distinct in the field.

The production-field regression constructs `p*a` through repeated scaling by
two and addition, with only canonical small leaf constants. Every field value
of `a` satisfies the gate. Recovery must report ambiguity, never `Exact(0)`.

## Constraint Coverage

Gate extraction and SMT gate encoding visit every usable Halo2 row, not only
regions or rows with an enabled selector. Region metadata is not a gate-activity
predicate. Known fixed values can establish that a polynomial is identically
zero; an unrelated selector cannot disable a fixed-activated gate.

The supported inline SMT lookup path also visits every usable row. Every input
coordinate stays in its original tuple position. An all-zero input is omitted
only when the complete zero tuple appears in the actual table. Table membership
uses usable rows and deduplicates tuples, so unassigned blinding rows cannot
silently introduce an extra zero entry. Legacy interpreted/uninterpreted lookup
modes are not part of the private-recovery API or this exact-membership guarantee.

Fixed, advice and instance rotations use the evaluation-domain period. UCP
extraction canonicalizes rotated cell identities using `2^k`, and SMT uses the
same domain size. Tests include two distinct rotations referring to one cell.

## Evidence

`ucp/soundness_regression_tests.rs` contains thirteen regression tests, including
exhaustive solution checks for linear equations and products of affine factors
over `F_2`, `F_3`, `F_5` and `F_7`. Every inferred domain must contain every actual
solution, and a uniqueness claim must not admit two distinct solutions.

Real Halo2 circuits are checked with MockProver and the recovery API. Selected
domains are additionally checked through fresh SMT validation. This validation
does not assume inferred facts, but still shares the frontend with recovery;
it is not an independent proof of faithful Halo2 translation.

Two old tests were corrected explicitly: a gate intended for one public-input
row now has a selector, and the ungated multiplication example acknowledges free
advice cells outside its assigned region while checking that its actual first-row
computation remains unique.

Run serially because the analyzer still uses a shared SMT output file:

```sh
cargo test -p korrekt --lib soundness_regression_tests -- --test-threads=1
cargo test -p korrekt -- --test-threads=1
```

The default Zcash-backend suite passed 214 tests, with no failures and one ignored
opt-in measurement test. The new regression tests passed separately. This is
regression evidence, not a guarantee that no additional counterexamples exist.

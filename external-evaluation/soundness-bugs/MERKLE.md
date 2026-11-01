# Unchanged External Merkle NoHash4

This suite includes the original `MerkleCircuitNoHash4` from
[teddav/halo2-soundness-bugs](https://github.com/teddav/halo2-soundness-bugs/blob/4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4/src/merkle/merkle_nohash4.rs),
commit `4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4`.
Its source is downloaded under `target/` and included without edits.
`prepare.sh` verifies SHA-256
`25b673dbcc8013af289bb76e7039b40934c1ceedceee982ef0e050dfd6a58afe`.

The harness instantiates the original variable-length circuit at depth three.
Its seven selected private inputs are one leaf, three sibling values, and three
direction bits. Targets are identified by the original regions and column roles;
intermediate hashes and advice copies are not counted as additional inputs.
The original Pasta `Fp` field is preserved, unlike the BN256 square-root tests.

## Compatibility Boundaries

The same instrumented PSE backend and `ErrorFront` import alias described in
[README.md](README.md) are used. The upstream Halo2 v0.4.0 dependency stack is
therefore not reproduced exactly.

The source also imports `halo2_poseidon::utilities::FieldValue`, solely to obtain
a reference to a `Value<Fp>`. A local compatibility facade provides the same
`Value::as_ref()` accessor as the upstream implementation in
[`teddav/poseidon-gadget`, commit `dfeb9bf3318fbbbb77e113e732dd01d6f503749b`](https://github.com/teddav/poseidon-gadget/blob/dfeb9bf3318fbbbb77e113e732dd01d6f503749b/src/utilities.rs).
This accessor creates no gates or assertions. No Poseidon hash is used by this
NoHash circuit. The circuit equations, constants, selectors, field, copy bindings,
and public root binding are unchanged; no analyzer inference rules are modified.

## Run

From the repository root:

```bash
bash external-evaluation/soundness-bugs/prepare.sh
cargo test --release --locked \
  --manifest-path external-evaluation/soundness-bugs/Cargo.toml \
  external_merkle_nohash_standard_recovery \
  -- --nocapture --test-threads=1
```

To include the native positive and negative controls, use
`external_merkle_nohash` as the test filter instead.
The tests require `cvc5` on `PATH` and serial execution because solver files use
shared names. `UCP_MERKLE_TIMEOUT_MS` overrides the positive per-call timeout,
whose default is 3000 ms.

Recovery uses Standard options with all search strategies enabled and unchanged
default search budgets. Like the invoice examples, it sets a 3000 ms search
timeout, a 60000 ms initial-SAT fallback timeout, and disables a longer retry
timeout floor. These are matching default settings, not a call to the invoice
test helper: this isolated workspace uses its own timeout environment variable.
Initial existence is established with MockProver. Private witness values are
not supplied as recovery premises, and there is no separate post-recovery SMT
validation in this measurement.

## Constraints and Reference Result

The original educational circuit doubles the leaf and adds each sibling after
conditionally swapping the two inputs. It constrains each direction bit to
`{0,1}`, copies the previous digest between levels, and publishes the final root.
Because its hash is addition, the resulting relation is

```text
root = 2 * leaf + sibling_0 + sibling_1 + sibling_2
direction_i in {0, 1}
```

The supplied witness has leaf `4`, siblings `[3,5,7]`, directions `[0,1,0]`,
and public root `23`. The native controls check alternative witnesses varying
every input under this same root. They also reject a changed public root and
a non-boolean direction value.

Mathematically, each field-valued input can take any element of `Fp`, compensated
by another input. Each direction can independently take either boolean value.
These reference facts are test expectations, not extra solver premises.

One observed release run produced:

| Phase | Time (s) | Solver calls | New exact targets | New/refined target domains |
| --- | ---: | ---: | ---: | ---: |
| UCP | <0.01 | 0 | 0 | 3 |
| SMT | 5.63 | 68 | 0 | 0 |

Total recovery time was 5.82 s, including 0.19 s outside the displayed phases.
The result had seven proven non-unique targets, zero unresolved uniqueness
classifications, and three complete domains `{0,1}`. The SMT phase used 64
discovery calls and four candidate-feasibility calls. Discovery exhausted its
global budget while collecting samples for the four unrestricted field-valued
inputs; these samples were not published as covering domains. Thus, complete
domain recovery was not achieved for those four targets, even though their
non-uniqueness was proved. Timings and model choices are not test invariants.

SMT added feasibility evidence, non-uniqueness, and completeness metadata, but
did not change uniqueness facts in `K` or domain contents in `Delta`. No second
propagation phase was therefore needed.

## Interpretation

This is an unchanged external educational circuit with multiple private inputs,
boolean-domain inference, and successful non-uniqueness proofs. It is not a
cryptographically secure Merkle commitment: the upstream source deliberately
uses addition instead of a collision-resistant hash. Neither these tests nor
`NonUnique` establish general privacy or production security.

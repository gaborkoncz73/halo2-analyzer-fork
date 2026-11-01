# Imported Five-Element Permutation Circuit

This isolated workspace imports the original public `PermutationCircuit` type
from [LibeccioLabs/Halo2-Playground](https://github.com/LibeccioLabs/Halo2-Playground),
pinned to commit `78c193ef92bb82312f871b74dfe5871cb00b2263`.
No circuit source is copied, edited, or reimplemented.

## Run

From the repository root:

```bash
cargo test --release --locked \
  --manifest-path external-evaluation/permutation/Cargo.toml \
  imported_permutation -- --nocapture --test-threads=1
```

For just the recovery trace, use `imported_permutation_standard_recovery` as
the filter. `cvc5` must be on `PATH`. The first build needs network access to
fetch the pinned circuit and its dependencies. The workspace lockfile records
transitive Git dependencies as well.

## Original Circuit and Compatibility

Relevant upstream files:

- [`src/permutation_circuit.rs`](https://github.com/LibeccioLabs/Halo2-Playground/blob/78c193ef92bb82312f871b74dfe5871cb00b2263/src/permutation_circuit.rs)
- [`src/permutation_chip/gate_implementation.rs`](https://github.com/LibeccioLabs/Halo2-Playground/blob/78c193ef92bb82312f871b74dfe5871cb00b2263/src/permutation_chip/gate_implementation.rs)
- [`src/permutation_chip/chip_setup_api.rs`](https://github.com/LibeccioLabs/Halo2-Playground/blob/78c193ef92bb82312f871b74dfe5871cb00b2263/src/permutation_chip/chip_setup_api.rs)

The author's own tests instantiate five- and seven-element versions. This harness
uses the original five-element type and its constructors, not a locally extended
variant. Input values and swap decisions are private; the resulting ordered list
is public. The circuit uses ten conditional adjacent swaps. Each swap has one
boolean equation and two value-transfer equations. Including input copies and
public output bindings, extraction yields 40 equations and 40 advice cells at
`k=4`. Only the five original input cells are targets, not their copies or the
ten auxiliary swap bits.

The manifest redirects the upstream Zcash Halo2 Git dependency to the analyzer's
existing instrumented Zcash backend, revision
`7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb`. This is a backend compatibility
adaptation, not an unchanged upstream dependency stack. Both crates compile
against the same backend; the circuit and its original helper crate remain
unmodified. The original Pasta `Fp` field is retained. The main workspace's
dependencies and analyzer inference rules are unchanged.

## Tests and Reference Result

`imported_permutation_accepts_all_120_private_orders` verifies all `5!` private
input permutations with MockProver under the same public output `[0,1,2,3,4]`.
The structural target layout must remain unchanged. Replacing each public entry
with `99` in turn must fail native verification. These native witnesses are
reference controls, not recovery premises or a candidate-value oracle.

`imported_permutation_ucp_infers_boolean_switch_domains` runs propagation without
SMT and checks the ten auxiliary domains `{0,1}`.

`imported_permutation_standard_recovery` invokes the full private-recovery API
with Standard options and requires all five targets to be non-unique. Every
reported covering domain must contain `{0,1,2,3,4}`; domains certified complete
must equal that set. A missing domain is permitted and is not a coverage proof.
The API verifies initial
existence through MockProver without inserting private assignments into the
recovery state. Independent post-recovery SMT validation is not part of this run.

The Standard configuration retains all default search budgets and enables all
search strategies. Like the invoice experiments, it sets a 3000 ms search
timeout, a 60000 ms initial-SAT fallback timeout, and no longer retry timeout
floor. `UCP_PERMUTATION_TIMEOUT_MS` overrides the positive search timeout.
The per-call timeout is not an overall wall-time limit. Solver-backed tests
must run serially because the analyzer uses shared query-file names.

The mathematical reference domain of every input position is exactly
`{0,1,2,3,4}`: boolean-controlled swaps preserve the multiset of values, and
every permutation can produce the fixed public output. The positions are
correlated, not independent choices. This circuit intentionally reveals the
multiset while leaving the original order ambiguous. Recovery results do not
constitute a general privacy or cryptographic security proof.

## Observed Recovery Run

A representative release run with the default 3000 ms search timeout produced:

| Phase | Time (s) | Solver calls | New target information |
| --- | ---: | ---: | --- |
| First UCP | <0.01 | 0 | Two covering domains |
| First SMT | 23.17 | 18 | Three non-unique inputs; one complete domain |
| Second UCP | <0.01 | 0 | No new target facts |
| Second SMT | 47.91 | 35 | Remaining two inputs non-unique; two further complete domains |
| Third UCP | <0.01 | 0 | No new target facts |
| Third SMT | 5.44 | 10 | Auxiliary-cell analysis; no new target facts |

Total: 78.27 seconds, including preparation and scheduling; 63 solver calls;
zero exact inputs, five non-unique inputs, and three complete input domains.
The other two inputs have feasible samples but no recorded covering domain:
their discovery exclusion queries timed out. These are representative timings,
not benchmark averages. The separate UCP-only test also confirms ten boolean
auxiliary domains without SMT.

The serial suite passes three tests and skips one stronger measurement.
`imported_permutation_complete_domain_recovery` additionally requires complete
domains for all five inputs. That stronger condition was not met by the default
run; it is deliberately separate from the non-uniqueness regression test.
To attempt it with a longer per-call timeout:

```bash
UCP_PERMUTATION_TIMEOUT_MS=10000 cargo test --release --locked \
  --manifest-path external-evaluation/permutation/Cargo.toml \
  imported_permutation_complete_domain_recovery \
  -- --ignored --nocapture --test-threads=1
```

This longer measurement has not been verified to pass. Increasing the timeout
does not guarantee that every completeness proof will finish.

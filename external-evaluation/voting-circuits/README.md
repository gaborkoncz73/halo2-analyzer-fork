# Imported Voting Circuit Evaluation

This isolated evaluation imports `voting_circuits::share_reveal::Circuit`
directly from the published **voting-circuits 0.9.0** crate. It does not copy
the circuit, implement a replacement `Circuit`, or add constraints to it.
Its public `build_share_reveal` builder supplies the complete circuit instance.

Sources:

- [Published crate](https://crates.io/crates/voting-circuits/0.9.0)
- [Upstream circuit](https://github.com/valargroup/voting-circuits/blob/v0.9.0/src/share_reveal/circuit.rs)
- [Upstream builder](https://github.com/valargroup/voting-circuits/blob/v0.9.0/src/share_reveal/builder.rs)

## Backend Compatibility

The main analyzer uses an instrumented older Zcash Halo2 fork. The imported
circuit's resolved Orchard/gadget dependencies require newer Halo2 APIs.
This package therefore has its **own workspace and dependency resolution**:

- Published `halo2_proofs 0.3.5`, verified against a pinned SHA-256 checksum.
- A reviewable `halo2-analyzer-visibility.patch` exposes the same structural
  information used by the analyzer's existing backend. It changes visibility,
  adds documentation, and derives `Hash` for `Rotation`. It does not change
  any function body, gate, witness computation, or proof verification rule.
- Both `korrekt` and the external crate resolve to that one backend instance.
- The main workspace's manifests and backend are unchanged.
- `Cargo.lock` is retained for this evaluation, including the published
  voting crate's checksum. The generated backend is under ignored `target/`.

The patch is analyzer instrumentation, not a claim that the external circuit
runs on an entirely unmodified cryptographic dependency. This harness does
not generate or verify production proofs.

## Run

From the repository root, prepare the backend once:

```bash
bash external-evaluation/voting-circuits/prepare.sh
```

The script uses the Cargo download cache when available, otherwise downloads
the pinned published Halo2 archive. It does not modify Cargo's cache.

Fast compatibility, valid-witness, extraction, and negative-control checks:

```bash
cargo test --release --locked \
  --manifest-path external-evaluation/voting-circuits/Cargo.toml \
  -- --nocapture --test-threads=1
```

Explicit, bounded Standard recovery measurement:

```bash
cargo test --release --locked \
  --manifest-path external-evaluation/voting-circuits/Cargo.toml \
  imported_share_reveal_standard_recovery \
  -- --ignored --nocapture --test-threads=1
```

`cvc5` must be on `PATH` for recovery. The test prints its options and the
analyzer's UCP/SMT phase report. Solver timeouts do not bound synthesis,
propagation, scheduling, or total wall time. The measurement is ignored by
default because it is much more expensive than the compatibility tests.

All three Standard search strategies remain enabled. Pilot defaults are:

| Resource | Pilot allowance |
| --- | ---: |
| Per-solver timeout | 1000 ms |
| Semantic attempts | 4 |
| Refinement solver checks | 4 |
| Discovery solver checks | 4 |
| Bridge work | 2 |
| No-progress allowance | 4 |
| Semantic retries per target | 0 |

Positive environment overrides are `UCP_VOTING_TIMEOUT_MS`,
`UCP_VOTING_SEMANTIC_QUERIES`, `UCP_VOTING_REFINEMENT_CHECKS`, and
`UCP_VOTING_DISCOVERY_CHECKS`. These are pilot budgets, not the analyzer's
general default configuration or budgets directly comparable to invoice runs.

## What Is Measured

ShareReveal checks a vote commitment's Merkle membership, Poseidon commitment
relations, selection of one of 16 encrypted-share commitments, and a share
nullifier. This version uses `k = 11`: 2048 available rows, not 2048 constraints.
Extraction gives **32 configured gate polynomials, 6269 instantiated equations,
6194 advice cells, and no lookup arguments**. The extracted equations include
copy constraints; they should not be confused with the configured gate count.

The 18 selected private cells are the share index, primary blind, and 16
share commitments. Targets are identified from the pinned circuit's synthesis
order and single-cell regions, with explicit layout assertions. They are not
located by matching private values, and physical row numbers are not hardcoded.
The already-public vote decision is used only as a public-to-advice propagation
control, outside the private-target count. Merkle siblings, position bits, the
derived vote commitment, and hash intermediate values are not selected targets.

Fixture generation uses native curve arithmetic and Poseidon to construct
consistent commitments, then calls the original builder. It is deterministic
test data for a valid **standalone ShareReveal statement**, not a complete run
of delegation, vote generation, on-chain registration, or the upstream protocol.
The keys, blindings, and share values are not production randomness.

Initial existence is checked by MockProver under the same nine public inputs.
Private fixture values are used only to build that witness and, after recovery,
check that a reported covering domain does not exclude its true value. They
are not supplied as recovery premises or candidate domains.

A timeout, unresolved private cell, or lack of recovered values is **not a
proof of confidentiality**. This experiment measures analyzer behavior on an
imported cryptographic circuit; it does not establish a voting-system privacy
vulnerability or prove that all protocol implementations are secure.

## Observed Pilot Run

One release run with the printed pilot defaults completed as follows:

| Phase | Time | Outcome |
| --- | ---: | --- |
| Initial existence | Included below | VerifiedWitness; zero initial SMT calls |
| UCP | 0.13 s | No exact or finite-domain private targets |
| SMT | 8.24 s | 4 enumeration calls and 4 fast-probe calls; all timed out |
| Other work | 18.23 s | Preparation, initial check, scheduling |
| Total recovery | 26.61 s | QueryLimitReached; 18 unresolved private targets |

Both valid-fixture extraction checks and the invalid-public-input control
passed separately. The recovery test also checked propagation of the public
vote decision to its advice copy. No separate post-recovery SMT validation ran.
The reported total excludes the separate layout inspection used to select
targets, and excludes compilation. These are single-run observations, not
averages, worst-case bounds, or a comparison under the invoice budgets.

The negative control changes each of the nine public inputs independently,
keeping the witness fixed, and requires every altered instance to fail.
After `cargo clean`, rerun `prepare.sh` before invoking Cargo again because
the generated compatibility backend is intentionally stored under `target/`.

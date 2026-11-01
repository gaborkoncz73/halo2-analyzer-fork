# External Soundness Circuit Evaluation

The square-root suite is described below. The additional multi-input casino
suite, including unchanged upstream and separately patched local controls,
is documented in [CASINO.md](CASINO.md).
The unchanged seven-input Merkle NoHash4 suite is documented in
[MERKLE.md](MERKLE.md).

This package evaluates the two square-root circuits from
[teddav/halo2-soundness-bugs](https://github.com/teddav/halo2-soundness-bugs),
pinned to commit `4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4`.
The upstream circuit source files are fetched, checksum-verified, and included
**without changing their contents**. The harness instantiates their original
public `SquareRootCircuit` types, rather than reimplementing their constraints.

## Provenance and Compatibility

- [Original unrestricted circuit](https://github.com/teddav/halo2-soundness-bugs/blob/4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4/src/square_root/sroot0.rs)
- [Original lookup-bounded circuit](https://github.com/teddav/halo2-soundness-bugs/blob/4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4/src/square_root/sroot1.rs)
- [Original dependency manifest](https://github.com/teddav/halo2-soundness-bugs/blob/4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4/Cargo.toml)

The original project is a binary with private modules, not a library exporting
these circuits. Consequently this is **unchanged external source inclusion**,
not a direct public-crate API import like the voting-circuits evaluation.
The upstream sources are generated under ignored `target/`, not vendored as
locally maintained circuit implementations.

The upstream project uses PSE Halo2 v0.4.0. This evaluation uses the analyzer's
existing instrumented PSE backend at
`c23f6b74d621da4ca9b5526256a7b5b5cf72dece` (package version 0.3.0).
A local import facade aliases the original `ErrorFront` name to the backend's
`Error` type. The circuits retain their BN256 scalar field, gates, row
rotations, equality constraints, public bindings, and lookup table contents.
This is an API-compatible backend adaptation, not an execution on an entirely
unchanged upstream dependency stack. No production proofs are generated.

Two existing analyzer compatibility problems were repaired to enable the PSE
build: PSE MockProver's `FromUniformBytes<64>` field bound, and the distinction
between region-cell map keys `(column, row)` and assignment counts. The
unconstrained-cell scan also matches PSE's phase-carrying `Any::Advice(_)`.
These changes do not add or specialize recovery inference rules.

## Run

From the repository root:

```bash
bash external-evaluation/soundness-bugs/prepare.sh
cargo test --release --locked \
  --manifest-path external-evaluation/soundness-bugs/Cargo.toml \
  -- --nocapture --test-threads=1
```

`prepare.sh` downloads a pinned GitHub archive when absent and verifies both
the archive and the two original `.rs` files. It does not install the old
Rust toolchain requested by the upstream binary project. After `cargo clean`,
rerun preparation before compiling this package.

`cvc5` must be on `PATH`. SMT-based tests run serially because the analyzer's
query files use shared names within the package. The isolated workspace and
lockfile preserve the PSE dependency selection without changing the main
workspace's dependency configuration.

Each recovery uses `PrivacyAnalysisOptions::default()` (Standard, all search
strategies enabled), with a 3000 ms solver timeout and no longer retry-timeout
floor. `UCP_SROOT_TIMEOUT_MS` overrides the positive per-solver timeout.
The timeout is not an overall analysis wall-time bound. The tests assert the
expected recovery facts: insufficient solver resources can make a test fail,
but an inconclusive solver result is never accepted as a successful proof.

## Cases and Results

Both original circuits have one private root `x`, one public square `s`, two
advice cells, and two extracted equations (the square relation and its public
copy binding). Both are evaluated at `k=5` (32 rows). The unrestricted circuit
uses one advice column; the bounded circuit uses two and one lookup argument.

| Test case | Expected result | Observed Standard strategy | SMT calls |
| --- | --- | --- | ---: |
| Unrestricted, `s=9` | Complete domain `{3, p-3}`; NonUnique | Discovery: two SAT models, then UNSAT exclusion | 3 |
| Unrestricted, `s=0` | Exact `x=0`; complete singleton | Discovery: one SAT model, then UNSAT exclusion | 2 |
| Lookup-bounded, `s=9` | Exact `x=3`; complete singleton | Refinement's internal fast probe | 2 |

The actual lookup table is **`0..=10`**, despite the upstream README's prose
describing `1..10`. The harness checks that this exact initial covering domain
is extracted. In the bounded run UCP retains that domain, then the fast probe
finds `3` and excludes every different value. Discovery and refinement results
trigger another UCP phase when domain contents change. The source files and
search policy are not changed to obtain these particular strategy choices.

The report prints signed field representatives, so `p-3` appears as `-3`.
That is the same BN256 field element, not an integer-arithmetic interpretation
of the circuit.

One observed release run took approximately 0.02 s for the unrestricted
two-root case, 0.01 s for the zero case, and 1.14 s for the bounded case.
These are illustrative single-run recovery timings, not benchmark averages.
They exclude compilation and the separate structural inspection used to select
targets. Initial satisfiability is checked with MockProver (zero initial SMT
calls); no separate post-recovery SMT validation is included.

## Checks and Interpretation

The six tests also cover:

- Both `3` and `-3` are valid witnesses for the unrestricted public square `9`.
- Recovery returns the same domain, uniqueness, and completeness with either
  supplied witness. Witness values are not search premises.
- A changed public square rejects the unchanged witness.
- The bounded circuit rejects the `-3` witness for public square `9`.
- The PSE unconstrained-cell scanner accepts the correctly constrained original
  square circuit, including its public copy constraint.
- A separately identified local scanner regression control distinguishes a
  constrained row from an unconstrained row when assignment counts are equal.
  This local control is not part of the external recovery benchmarks.

Targets are selected structurally from the original `main region`, not by
matching witness values. Mathematical reference domains appear only in test
assertions after recovery, not in the analyzer's input.

For a prime field of odd characteristic, `x*x=9` has exactly the two roots
`3` and `-3`; `x*x=0` has only `0`. The lookup removes `-3` for `s=9`, since
the BN256 modulus is far larger than the small lookup range. These provide
clear ground truth for domain coverage, completeness, and exact recovery.
They do not constitute a new vulnerability discovery: revealing a square on
this small input range naturally determines its root. A functional soundness
repair and a privacy guarantee are different claims.

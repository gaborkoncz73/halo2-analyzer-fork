# Upstream Halo2 Book Fixture

`halo2_simple_example.rs` is a byte-for-byte copy of:

- Original project: https://github.com/zcash/halo2
- Retrieved compatibility fork: https://github.com/Analyzable-Halo2/zcash-halo2
- Revision: `7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb`
- Path: `halo2_proofs/examples/simple-example.rs`
- Pinned source: https://github.com/Analyzable-Halo2/zcash-halo2/blob/7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb/halo2_proofs/examples/simple-example.rs
- Documentation: https://zcash.github.io/halo2/user/simple-example.html
- SHA-256: `d3b3733144e3acf0efbd4e786db2d2fa87dca424f23b326e334723f94bf08b38`
- License chosen for this copy: MIT; the upstream copyright and permission notice
  is retained in the adjacent `LICENSE-MIT` file.

The copy was taken from the locally cached checkout of the project's locked Halo2
dependency. Keeping it here makes offline tests reproducible without depending
on the location of another developer's Cargo cache.

`external_circuit_tests.rs` supplies the dependency import alias, constructors,
and the analysis harness outside the unchanged file. Its additional-publication
control is a local modification, not an upstream vulnerability or a second
independent external circuit. The example is educational, not a production
privacy protocol, and non-uniqueness is not a proof of cryptographic privacy.

## Poseidon Benchmark Circuit

`halo2_poseidon_benchmark_circuit.rs` is the unchanged contiguous circuit/spec
excerpt from `halo2_gadgets/benches/poseidon.rs`, starting at the first
`#[derive(Clone, Copy)]` and ending before `const K: u32`. Imports and benchmark
driver functions are omitted; the adapter provides imports, and trailing blank
lines were removed. Circuit logic and parameters are unchanged.

- Original project: `zcash/halo2`
- Compatibility fork/revision: `Analyzable-Halo2/zcash-halo2`,
  `7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb`
- Source: https://github.com/Analyzable-Halo2/zcash-halo2/blob/7fc5e14d53c19cc4e09f0af2ed4b87440e1bb4fb/halo2_gadgets/benches/poseidon.rs
- Full source SHA-256: `7c6dd87a157add3fb2ff96693cfca464563a0103bb8dbe06ca44d1d140726e14`
- Excerpt SHA-256: `746b7bad6ea1c9dbe32c5216ce9279385b832baccfe67c1189bd4373a12dcf22`
- License: MIT, with the same adjacent `LICENSE-MIT` notice.

`external_poseidon_tests.rs` instantiates the original width-3/rate-2, two-word
benchmark circuit, and defines a separately identified local publication control.
This is a real cryptographic benchmark fixture, not a production application or
an independent new author/project relative to the Halo2 Book fixture.

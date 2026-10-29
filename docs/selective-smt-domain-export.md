# Selective SMT Domain Export

## Scope And Policy

Private recoverability starts propagation with the concrete public observations.
It does not compute an unobserved UCP baseline for solver export. Its inexpensive
reference is `UcpProblem::initial_value_facts`: domains extracted from lookups and
known fixed values, without running the propagation engine. An unchanged
extracted membership can be redundant in SMT because the original constraints
already encode it.

The privacy query driver now constructs a separate, filtered set of solver facts:

| Current Domain | Exported To SMT? |
| --- | --- |
| Exact value, including unchanged constants | Yes |
| Finite set with no extracted input domain | Yes |
| Finite set different from its extracted input domain | Yes |
| Finite set identical to its extracted input domain | No |

`smt_query_value_facts` copies eligible facts without mutating Delta. The full
learned domains and recovery statuses remain in the report and available to
further UCP propagation. Gate-derived intrinsic domains may now be exported:
the driver does not spend a full UCP run merely to recognize their redundancy.
Independent validation still checks every reported domain, including those not
asserted during recovery.

This is a fixed privacy-driver export policy, named
`exact-and-domains-beyond-extracted-inputs` in the report and measurement metadata.
An optional `compute_structural_baseline` report control defaults to false and
runs only after recovery. `structural_baseline_computed` distinguishes an absent
comparison from a computed baseline with no recorded domain. It has no influence
on this export policy. The ordinary UCP/SMT
constrainedness pipeline and `Analyzer::set_ucp_value_facts` still export all
supplied domains; their contracts and behavior did not change.

## Local Correctness Argument

Let `C` be the original constraints, `P` the concrete public observations, and `B`
an unchanged extracted membership. Sound extraction gives `C => B`, so
`C AND P` and `C AND P AND B` have the same satisfying assignments. Removing the
explicit assertion of `B` therefore does not remove the original range constraint
or admit additional circuit-valid values. It changes solver syntax, not the
property queried. All original gates, copies, and tuple lookups remain encoded.

The argument depends on the correctness of domain extraction and the frontend,
just as the existing recovery analysis does. It is not a machine-checked proof
of the complete analyzer. Tests compare the real solver and state machine with
selective and full export on the same lookup circuits. They also check that a
newly narrowed `{1,...,15}` domain still reaches the solver and that an omitted
extracted domain remains present and independently validated in the report.

This is a performance heuristic, not a completeness guarantee. Explicit domains
can help some solver searches and hurt others. Unknown results and timeouts retain
their existing meaning; omission never reclassifies them as safe secrets.

## Local Measurement Snapshot

The following measurements are historical: they used the older
`exact-and-new-or-refined-domains` policy with a mandatory unobserved UCP
baseline. They are not measurements of the current extracted-input policy.

Release run on 2026-10-08, same CVC5 build as the earlier measurements,
one warmup and three serial trials per case with alternating recovery/reference
order, and a 2000 ms solver-managed per-check budget:

| Case | Selective Recovery (ms) | SMT Only (ms) | Fresh Validation (ms) |
| --- | ---: | ---: | ---: |
| Polynomial, total 15 | 134.12 | 128.10 | 488.98 |
| Lookup, total 15 | 68.06 | 62.22 | 190.42 |
| Polynomial, total 30 | 26.09 | 127.19 | 126.57 |
| Lookup, total 30 | 89.83 | 435.00 | 432.57 |

The previous full-export lookup interior median was 474.41 ms; the new median is
68.06 ms, about seven times faster than that earlier recovery run. This is a
historical before/after comparison, not a paired policy benchmark or a universal
speed guarantee. It remains slightly slower than the SMT-only reference, while
also producing the finite domains that the reference does not infer.

Both interior cases still report two finite domains and two non-unique inputs;
both boundary cases still recover two exact values with zero semantic cell queries.
Validation is separate and is not cheaper because recovery omits an assertion.
Including validation removes the boundary speed advantage over unvalidated
SMT-only recovery in these examples.

The full suite completed 16 cases; the packed 16/32-bit cases again returned
`TIMEOUT` and were excluded as incomplete. Artifacts are
`/tmp/selective-domain-export-measurements.tsv`,
`/tmp/selective-domain-export-measurements.summary.tsv`, and
`/tmp/selective-domain-export-measurements.incomplete.tsv`.

```sh
cargo test --offline -p korrekt --lib circuit_analyzer::ucp::privacy::tests -- --test-threads=1
```

Use the [measurement protocol](private-recovery-measurements.md) for repeated
release runs. No ordinary test asserts a speed ratio.

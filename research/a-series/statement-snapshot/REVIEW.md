# Statement-snapshot baseline: policy and semantic scope

This is the current, tracked review record pinned by `golden.json` for the KLS statement
baseline. It states what the baseline binds, what counts as a change, and how a change is
reviewed. It carries no runtime logs.

## What the baseline captures

`research/statement_snapshot.py` elaborates `research/StatementSnapshot.lean` on top of
`FunctionalInequalities.KLS.Statement` and prints, with `pp.all`, `pp.proofs` and a fixed width,
the closure of seven roots:

- `KLS.Conjecture` and `KLS.LogConcave`;
- `Energy.LocalSlope.apply`, `Energy.LocalSlope.energy`, `Energy.LocalSlope.Admissible`;
- `Poincare.LocalSlope.Holds` and `Poincare.LocalSlope.Intrinsic.constant`.

The payload records, for each local declaration reached from these roots, its elaborated type,
its definition body where it is a definition, its universe parameters and its dependencies;
declarations outside the project are recorded as external leaves and are not expanded. The
current golden holds 26 local declarations and 221 external leaves, together with the toolchain
(`leanprover/lean4:v4.33.0`), the `lake-manifest.json` hash and the printing options. Theorem
proof bodies are not part of the payload.

## What the gate does

The full local verifier compares a fresh snapshot with the golden and fails on any difference:
a changed type, definition, universe, dependency, root list, toolchain, manifest or printing
option. It never refreshes the golden. The golden also pins this review record by path and
SHA-256, so a changed baseline requires a reviewed, re-pinned record rather than a silent update.
The checker verifies hashes and payload equality; it cannot judge whether a change is acceptable.

## Review policy for a change

A baseline change is accepted only when this record states, for the exact diff of the payload:

1. which roots or local definitions changed and the old versus new mathematical scope
   (hypotheses, normalization, dimension, test class, carrier), and whether the original KLS
   goal is still covered; or
2. that the change is toolchain- or printing-only, with the semantic comparison empty.

This maintenance changes only the review provenance binding, preserving the seven roots and
the complete 26-declaration semantic payload. For a later baseline change, write a newly named
review in an approved snapshot owner and re-pin explicitly:

```bash
python3 research/statement_snapshot.py update --decision research/a-series/statement-snapshot/NEW-REVIEW.md
```

## Trust boundary

The baseline detects drift inside its explicit closure. It is not a proof of source fidelity
or semantic equivalence with the papers, which the literature register and the target-scope
reviews own, and it is not a ledger certificate.

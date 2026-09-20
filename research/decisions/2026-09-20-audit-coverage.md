# Repair research audit coverage (2026-09-20)

The independent review after structural cleanup compiled all 84 research audit clients:
83 passed; `BakryEmeryBochnerAudit.boundary_one_dim_value` failed to simplify the second
derivative of `4*x^2`. Lean's error recovery reported `sorryAx` for it and the dependent
`boundary_one_dim_hessianSq`. This was a failed audit proof, not a successful library theorem
using an added axiom. The existing 10-gate receipt excluded research audit compilation.

## Repair and ownership

The missing `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas` import belongs directly in the
Bochner audit, where the independent numerical normalization check uses those rules. Its
statement, proof body, factor 1/2 and diffusion sign remain unchanged. No broad measure or
integration imports are restored to the pointwise library modules.

`research/verify.py` now discovers every live `.lean` source under `research/audits/` from the
same Git-aware source snapshot used for the receipt. This includes nonignored new files and
nested directories and excludes deleted files. It compiles each client independently with
warnings as errors, records a separate gate and log, and rejects nonstandard printed axiom
reports. Three bounded workers run independent clients. The report lists the successfully
checked audit paths; any compile or axiom-report failure makes verification fail.

This closes LD-010. A research `#check` remains a candidate statement, not a proof certificate.
The new audit gate is strict elaboration, not additional `leanchecker` replay; replay still
covers the existing library, solutions and examples. A complete run now has 84 audit gates in
addition to the prior 10 gates for the current inventory. The count is derived from current
sources, not a fixed whitelist.

## Validation

Regression tests use real Lean processes to check independent clients with colliding declaration
names, nested/new sources and deleted/out-of-scope entries. They also require failure for an
unsolved goal, a `sorry` warning, and a reported nonstandard axiom. All eight verifier tests pass.
The full verifier is run after source, evidence hashes and documentation are finalized; its
snapshot-bound receipt is written under `build/verification/`. Historical cleanup decisions and
receipts are preserved. This change makes no mathematical progress claim and does not authorize
commit or push.

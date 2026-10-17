# BKL independent target checks

This pilot checks BKL arXiv:2610.05474v1 Theorem 3.1 and Proposition 7.1 against a separately
written Mathlib-only specification. It preserves all source hypotheses, factorials, tensor
norms and constants. The source PDF is pinned by SHA-256 in [config.json](config.json).
The [source review](../../../decisions/2026-10-12-bkl-independent-target-checks.md) records the
exact scope, definition correspondences and deliberately reused foundation interfaces.

[Specification.lean.in](Specification.lean.in) imports only Mathlib. Poincaré and log-concavity
are explicit parameters. [Checks.lean.in](Checks.lean.in) specializes them to the reviewed
library boundary, proves definition bridges and applies the existing certificates. These
are audit templates, compiled into isolated runtime modules by [run.py](run.py); they are
not production modules or new ledger certificates.

From the repository root, with the pinned v1 PDF available:

```bash
python3 research/audits/BKL/IndependentTargets/run.py check --paper /absolute/path/2610.05474v1.pdf --mutations
```

The checked [golden.json](golden.json) snapshots both actual target types and key local definition
closures, including the existing Poincaré/log-concavity boundaries. A missing or changed baseline,
a changed review record, source drift, unregistered axiom or failed link fails the check.
`baseline` is an explicit initial-establishment action and refuses an existing golden file.
It is never invoked automatically by `check`.

Receipts and failing logs remain under `build/reviews/2026-10-12-bkl-independent-targets/runs/`.
`latest.json` there identifies the latest attempt, including a failed one. The receipt binds
source identity, compiler, dependency manifest, built artifacts and the snapshot baseline.
The driver builds the certificate import closure, independently compiles the specification,
strictly compiles/axiom-audits the link and replays the two certificates and two new audit
modules. Pinned third-party compiled imports remain trusted. This is not a full-library run,
an external comparator or a second-kernel result. Source-fidelity review is recorded separately.

Mutation checks remove the factorial, change 2b to b and restrict the universal input to one
dimension. All three specifications must compile, and all three links must be rejected.
The source-review notes explain normalization and the existing zero-dimensional API extension.
This audit leaves Proposition 7.1 conditional and does not cover Theorem 4.1, Theorem 1.1 or KLS; those are
registered separately (`thm:bkl-cumulant-bound`, `thm:bkl-poincare`).

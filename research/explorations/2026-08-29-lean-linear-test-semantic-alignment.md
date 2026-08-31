# Lean linear-test semantic alignment and ledger transition

**Date:** 2026-08-29 (Asia/Shanghai)

**Ledger node:** `lem:linear-test-lower`

**Scope:** Term-by-term comparison of the manuscript, ledger, analytic dossier, reusable Lean API,
and node certificate, followed by the sole-orchestrator certification metadata transition. No
mathematical statement or graph edge is changed.

## Sources compared

- `modules/01-definitions.tex`, `def:poincare`;
- `modules/02-results-toolkit.tex`, `rem:rayleigh-lower-only`;
- `research/a-series/ledger.yaml`, `lem:linear-test-lower`;
- `solutions/glm-linear-baselines.tex`, `lem:sol-linear-test-lower`;
- `formalization/FunctionalInequalities/Basic.lean`;
- `formalization/FunctionalInequalities/Poincare.lean`;
- `formalization/FunctionalInequalities/Project/LinearTestLower.lean`; and
- `solutions/LemLinearTestLower.lean`.

The full comparison is persisted as
`research/reviews/2026-08-29-lean-linear-test-semantic-alignment.md`.

## Result

The certificate exposes exactly the dossier's probability and finite-covariance hypotheses as
`IsProbabilityMeasure μ` and `MemLp id 2 μ`. It uses the same factor-one Poincaré normalization,
the centered covariance bilinear form, the canonical gradient energy, and an `ENNReal` optimal
constant. It handles positive variance over zero energy as $+\infty$, $0/0$ as $0$, absence of a
finite valid constant as $C_P=+\infty$, singular covariance, and dimension zero.

No semantic mismatch was found. In particular, the machine theorem includes all admissible tests,
so its inclusion of constants is stronger than the dossier's nonconstant phrasing. The only
remaining boundary is deliberately outside this node: no equality with a closed Sobolev-domain
constant or separately defined spectral gap has been proved.

## Ledger action

The current session is the single ledger writer. The node retains
`solution: solutions/glm-linear-baselines.tex`, changes from `checked_by: agent` to
`checked_by: lean`, removes the agent-only active `review:` field, and adds
`lean_solution: solutions/LemLinearTestLower.lean`. The historical natural-language proof review
remains unchanged under `research/reviews/`.

## Numerical and rejected routes

No numerical experiment was run or used. No alternative covariance operator was introduced:
Mathlib's uncentered `covarianceOperator` would not match the manuscript, so the already
implemented centered `covarianceBilin` Riesz operator remains essential. No attempt was made to
claim the unproved smooth-core/Sobolev-closure equivalence.

## Validation

The required post-transition checks passed:

```text
cd formalization && lake build
Build completed successfully (2946 jobs).

python3 research/check_ledger.py
2 ledger(s), 195 nodes, 675 labels. 0 error(s).

python3 research/check_ledger.py node lem:linear-test-lower
status: proved
solution: solutions/glm-linear-baselines.tex
lean_solution: solutions/LemLinearTestLower.lean
checked_by: lean

python3 -m unittest discover -s research/tests -p 'test_*.py'
Ran 44 tests ... OK

git diff --check
passed
```

A source scan found no `sorry`, `admit`, or custom `axiom` in `formalization/` or the Lean
certificate. The Python checks used the host's Python 3.14 with the installed PyYAML package made
visible through `PYTHONPATH`; this changes no repository or global environment state.

## Independent HOLD and repair

The first independent audit did not accept the initial blanket alignment conclusion. Although the
Lean proof chain was sound, it found that the manuscript and ledger omitted the finite-second-
moment and exact zero-energy conventions, did not state the zero-dimensional covariance Rayleigh
value, and that the shared dossier header obscured the two nodes' different active certification
modes. The immutable HOLD report is
`research/reviews/2026-08-29-lean-linear-test-independent-semantic-audit.md`.

The manuscript definition and toolkit remark, ledger sentence, analytic lemma and proof, knowledge
index, and shared dossier header were then aligned explicitly. The new per-node header convention
is recorded in `research/decisions/2026-08-29-shared-dossier-per-node-certification.md`. No Lean
definition or theorem changed: the repair makes the natural-language surfaces state the semantics
the certificate already implemented. A new independent follow-up audit is required before the
ledger transition is treated as complete.

## Final independent resolution

The cold follow-up audit is
`research/reviews/2026-08-29-lean-linear-test-semantic-followup.md`. It returned scoped `PASS` and
found every prior blocker discharged. Independently repeated validation produced a 2-page
standalone dossier, a 161-page complete manuscript, a 2,946-job successful Lake build, 195 ledger
nodes with 0 errors, 44 passing regression tests, and a clean `git diff --check`.

The final scope remains exact: the Lean binding certifies `lem:linear-test-lower` for
finite-dimensional probability measures with finite second moment on the globally smooth
$L^2$ finite-energy core, including all stated extended-value and dimension-zero conventions. It
does not certify a closed Sobolev-domain equivalence, a separately defined spectral-gap identity,
`thm:glm-fi`, Gaussian exactness, mode-indicator approximations, or infinite-second-moment laws.

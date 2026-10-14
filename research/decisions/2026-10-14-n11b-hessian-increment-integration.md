# N11b integrated Hessian-increment energy: canonical integration

Date: 2026-10-14. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)). Codex froze six small contracts N11b.1-N11b.6 and accepted
each candidate independently (`build/reviews/2026-10-14-codex-claude-n11-controller/independent/N11b1`,
`build/reviews/2026-10-14-letwin-constant-eight-goal/independent/N11b2..6`); the complete package passed Codex's layout preflight
(`full-placement-preflight/RESULT.json`, CODEX_COMPLETE_N11B_LAYOUT_PREFLIGHT_PASS) and placement acceptance
(`integration/PLACEMENT-ACCEPTANCE.json`, CODEX_PLACEMENT_ACCEPT). Claude integrated as sole canonical writer. No commit, push, tag,
remote CI or publication is authorized.

## Target and scope

The original frozen N11b statement `FunctionalInequalities.Analysis.integral_mul_hessian_increment_le` (task L-N11b, weak Letwin route
toward Theorem 2.5) is proved unchanged: C1 convex u with G-Lipschitz gradient, C1 convex V, Lipschitz exponent -u + V(gradient u),
K > 0, almost everywhere positive definite Hessian with log det = -u + V(gradient u) and the cap Hess u <= K, nonnegative compactly
supported C2 test eta, every shift h with u(x+h) + u(x-h) - 2u(x) <= D|h|^2, every finite dimension, exact coefficient 2K^2(D|h|^2).
It is a supporting estimate; weak third derivatives (N11d), the trace estimate and Letwin Theorems 2.5/1.2 remain open, and no paper
coverage or certificate changes.

## Placement (extend/create, all proof bodies verbatim)

| Accepted part | Declarations | Owner |
| --- | --- | --- |
| N11b.1, N11b.2 | `Analysis.centeredDifference_contDiff_lipschitz_gradient`, `Analysis.centeredDifference_nonneg_le` (+ private `increment_fderiv`, `increment_gradient`) | `Analysis/Convex/SecondDifference.lean` (extended, section `CenteredDifference`) |
| N11b.3 | `Probability.Stein.measurable_hessianMatrix_entry`, `Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient` (+ private `n10_matrix`, `n10_hessian`, `n11b_continuous_hessian_entry`) | `Probability/Stein/HessianKernel.lean` (extended, section `HessianEntryBounds`) |
| N11b.5 | `Analysis.integrable_weak_generator_densities` (+ private `weak_generator_compact_hessian_entry`, `weak_generator_compact_apply`) | `Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean` (extended, section `GeneratorIntegrability`) |
| N11b.4, N11b.6 | `Analysis.integrable_hessian_increment_energy`, `Analysis.integral_mul_hessian_increment_le` (no helpers) | `Analysis/Convex/HessianIncrement.lean` (new; imports SecondDifference, WeakInverseHessian, Viscosity, LocallyIntegrable) |

The two N11b.3 public names move namespace `Analysis` -> `Probability.Stein` (explicit map; no aliases, old names absent); every other
public name is unchanged. Module placement and namespace migration are recorded separately in
`build/reviews/2026-10-14-letwin-constant-eight-goal/integration/`. The three extended files are append-only (each old file is an exact
byte prefix); the root aggregate gains one import. Private helpers keep their accepted bodies (the N11b.3 copies of Piola's private
`n10_matrix`/`n10_hessian` and N11b.1's copies of Viscosity's private increment lemmas are module-local).

## Validation

`lake build` (9512 jobs); strict compilation of the four owners and of the new audit `research/audits/BKL/HessianIncrementAudit.lean`
(Codex Client1-6 proofs verbatim, audit-only namespace `HessianIncrementAudit.<subject>`); all seven complete types equal the accepted
hashes (265072094, 3239914189, 298734493, 1711842242, 615525409, 1222551683, 211311595); standard axioms only; local kernel replay of the
four modules. Blueprint gains five supporting lemmas in `45-shared-analytic-bridges.tex` (old chapter an exact prefix; pinned evidence
hashes refreshed with a record); Letwin T25, `remaining`, `local_results`, the proof-path boundary and the priority next step are
synchronized. At this documentation freeze a fresh full verification is required and pending; its exact report and result will be recorded in the
Goal control directory's ignored `CLAUDE-N11b-INTEGRATION-REPORT.md` and `STATE.json`. Codex's independent canonical acceptance is
pending and will be recorded in `canonical-independent/ACCEPTANCE.json`.

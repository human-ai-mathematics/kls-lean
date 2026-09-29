# Area-formula route A1: continuity of the volume factor and measurability of the integrand

2026-09-16. This round **proves new lemmas**, completing obligation **A1** from the preceding route investigation.
No holes migrated, no commit or push. Direct holes remain **8 (1/2/5)**; certificates remain **24**.
**Neither the area formula nor any coarea formula was proved.**

Starting point: `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; starting passed receipt
`build/verification/20260916T134934.350358Z/report.json`: 10 gates, kernel replay of 202 local modules,
521 entries.

## Boundary

The log-concave Cheeger–Buser line belongs to collaborator **Haocheng Wang** and was untouched in this round.

## Why A1 is a substantive obligation

Mathlib has a complete algebraic theory of `LinearMap.normDet`, but **not its continuity as a function of the operator**.
Without that result, even measurability of the integrand on the area formula's right-hand side,
`∫⁻ y in s, ofReal (normDet (fderiv ℝ g y))`, is unavailable, before addressing equality.
The preceding route investigation listed this as A1, with medium risk and an estimated 60–120 lines.

## Exact results

`Analysis/NormDetContinuity.lean` (local import closure of 2 modules, **no WIP**):

* `normDet_eq_sqrt_det`: `normDet A = √det (Aᵀ ∘L A)`, in continuous-linear-map form.
* `continuous_adjoint_comp`: `A ↦ Aᵀ ∘L A` is continuous (the adjoint is a linear isometry, and composition is bounded bilinear).
* **`continuous_normDet`**: `A ↦ normDet A` is continuous. The chain is
  continuity of adjoint → continuity of composition → `ContinuousLinearMap.continuous_det` → `Real.continuous_sqrt`.
* **`measurable_normDet_fderiv`**: `y ↦ normDet (fderiv ℝ g y)` is measurable.
* `continuous_coareaJacobian`, `measurable_coareaJacobian_fderiv`: analogous results on the coarea side.

## Stronger than the route requirement: no differentiability hypothesis

A1's measurability statement in the route is `ContDiff ℝ 1 g → Measurable (...)`. The actual proof needs **no hypothesis**:
`measurable_fderiv` holds for arbitrary functions (`fderiv` is zero at nondifferentiable points), so
`measurable_normDet_fderiv (g : H → V)` holds for **any** `g`; the route statement is a corollary with an unused hypothesis.
The client records this even for an everywhere nondifferentiable function.

## Agreement with the proved scalar theory

The client `scalar_integrand_measurable` uses `measurable_coareaJacobian_fderiv` and the earlier
`coareaJacobian_fderiv` to deduce measurability of `x ↦ ‖gradient u x‖`, exactly the integrand in the proved L11/L12/L13 results.
The new measurability layer agrees with the scalar layer, rather than creating a separate theory.

## Route progress

Obligation A1 is **complete**. The two A1 `#check` statements in `research/audits/AreaFormulaRouteStatements.lean`
are restated verbatim and proved in `research/audits/NormDetContinuityAudit.lean`.
The route-statement file itself is **preserved byte-for-byte** as dated evidence from the preceding round.

Still open: **A2** (countable additivity on the image side), **A3** (two-sided bounds for injective linear models, the general route's high-risk gap),
**A4** (nullity of the degenerate part), **A5** (local-to-global), **B1** (codimension-m graph area formula, recommended focus,
estimated 600–1000 lines over 2–3 rounds), and **B2** (B1's normalized version). The recommendation is to start **B1** next.

## Work not done in this round

* **No area formula** or coarea formula was proved.
* A2–A5, B1, and B2 were untouched; no holes migrated; sharp Sard, the two Cheeger comparisons, and Energy's five holes were untouched.
* No certificate or Blueprint `leanok` scope was expanded.
* **No commit or push**; the real Git index was unchanged.

## Verification

* The new module and client compiled with `-DwarningAsError=true`, without `sorry`.
* The 13 axiom reports in `research/audits/NormDetContinuityAudit.lean` use only
  `propext`, `Classical.choice`, and `Quot.sound`.
* All 30 audit clients were rerun (23 in `research/audits`, 7 in `build/audit`) and passed strictly.
* Each of the three WIP files was compiled: direct holes remain **1/2/5, totaling 8**.
* The default `lake build` and root `python3 research/verify.py` passed; evidence JSON is
  `research/explorations/2026-09-16-normdet-continuity.json`, with the final check separately saved in
  `build/audit/normdet-continuity/final-snapshot.json`.

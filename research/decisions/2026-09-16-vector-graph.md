# B1, first part: C¹ infrastructure for vector-valued graphs

2026-09-16. This round **proves new lemmas**, following the codimension-one file's structure to implement
**stages two and three** of the codimension-m graph area formula (obligation **B1**). **The area formula itself remains unproved.** No holes migrated, no commit or push.
Direct holes remain **8 (1/2/5)**; certificates remain **24**.

Starting point: `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; starting passed receipt
`build/verification/20260916T140115.179862Z/report.json`: 10 gates, kernel replay of 203 local modules,
525 entries.

## Boundary

The log-concave Cheeger–Buser line belongs to collaborator **Haocheng Wang** and was untouched in this round.

## Structure followed

`Analysis/AreaFormula.lean` (codimension one, 957 lines) has five stages: linear model → C¹ graph map →
linear approximation → two-sided estimates → area formula. This round implements the codimension-m versions of **stages two and three**.

## Exact results

`Analysis/VectorGraph.lean` (local import closure of 8 modules, **no WIP**):

* `vectorGraphMap ι κ γ = fun y => ι y + κ (γ y)`: the graph map for a `K`-valued graphing function.
* `graphProj_apply_of_perp`, **`graphProj_vectorGraphMap`**: the parameter contraction `ιᵀ` recovers the parameter from any graph point.
  **This is precisely the explicit left inverse missing in general route A3**, and it holds for **any** graphing function.
* **`vectorGraphMap_injective`**: injective, with **no assumptions on `γ`**,
  so no `InjOn` premise or multiplicity handling is needed.
* **`hasFDerivAt_vectorGraphMap`**: the derivative is the preceding round's `graphMapLinear ι κ (fderiv ℝ γ y)`,
  so the previously computed volume factor is the correct pointwise factor.
* **`approximatesLinearOn_vectorGraphMap`**: if the derivative varies by at most ε on a ball, the graph map is ε-close to the
  linear graph map at the center. The codimension-m estimate is **cleaner than in codimension one**: the second factor is an isometry, so its norm cancels directly,
  without the codimension-one detour through `innerSL`/gradients.
* `image_vectorGraphMap_eq`, `measurableSet_image_vectorGraphMap`: the image is the intersection of a closed condition and a contraction preimage,
  hence measurable.
* **`hausdorffMeasure_image_graphMapLinear`**: **the linear case of B1**.
  It follows directly from Mathlib's linear area formula and the preceding round's `normDet_graphMapLinear`,
  **without** the shear/dilate argument from the codimension-one file (about 160 lines).
* `measurable_vectorGraphJacobian`: the volume factor along a `C¹` graphing function is measurable, **using A1 from the preceding round**,
  so B1's right-hand side is indeed a lintegral.

## Work not done in this round

* **No area formula was proved**: stages four and five of the codimension-one file (two-sided estimates and the limit, about 450 lines)
  remain for B1 and were not done here.
* Route obligations A2–A5 and B2 were untouched.
* No holes migrated; sharp Sard, the two Cheeger comparisons, and Energy's five holes were untouched.
* No certificate or Blueprint `leanok` scope was expanded.
* **No commit or push**; the real Git index was unchanged.

## Next round

Stages four and five of B1: use `approximatesLinearOn_vectorGraphMap` to obtain two-sided Hausdorff estimates
(the upper bound from the Lipschitz image bound, the lower bound from the antilipschitz bound given by the left inverse `ιᵀ`,
where the explicit left inverse becomes useful). Then follow the codimension-one file to take ε → 0 and assemble countably many pieces. Estimated 1–2 rounds.

## Verification

* The new module and client compiled with `-DwarningAsError=true`, without `sorry`.
* The 20 axiom reports in `research/audits/VectorGraphAudit.lean` use only
  `propext`, `Classical.choice`, and `Quot.sound`; cases include codimension zero, a flat graph with constant graphing function, and zero-dimensional parameter space.
* All 31 audit clients were rerun (24 in `research/audits`, 7 in `build/audit`) and passed strictly.
* Each of the three WIP files was compiled: direct holes remain **1/2/5, totaling 8**.
* The default `lake build` and root `python3 research/verify.py` passed; evidence JSON is
  `research/explorations/2026-09-16-vector-graph.json`, with the final check separately saved in
  `build/audit/vector-graph/final-snapshot.json`.

# m-Codimensional Program Step 1: Normalization of Linear Area Formula and Affine Fibers

2026-09-16. This round proves a new lemma, transferring the linear area formula from Mathlib to the normalized convention of this repository, and thereby identifying the measure on fibers of linear mappings. This round does **not** prove any coarea formula, nor does it prove the C¹ area formula; there is no filling of holes, no commit, no push. Direct proof holes remain **8 (1/2/5)**, and certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`;
Start verification receipt `build/verification/20260916T122340.295044Z/report.json`: 10 gates,
200 local module kernel replay, 510 entries, snapshot
`c0e5cd2924db9e48eb1746067c434f410556f4907d36622c3c8664b4ac86c570`.

## Boundary

Log-concave Cheeger–Buser inequality (alignment of several definitions of isoperimetric constants with bidirectional comparison to Poincaré constants, containing `KLS/WIP/CheegerInfimum.lean` two remaining holes) belongs to collaborator **Haocheng Wang**, intentionally not touched in this round.

## Why is this step needed?

Mathlib's `LinearMap.hausdorffMeasure_image` uses **raw** `μH`; in this repository all measures are
`KLS.hausdorffNormalized`, i.e., classical `ω_d (diam/2)^d` normalization. The two differ by a constant factor,
and the fiber integral on the right-hand side of the coarea formula in dimension m must be **without residual constants**, otherwise the entire formula would carry an erroneous factor depending on dimension. This round aims to make this clear.

## Exact Results

`KLS/Geometry/LinearAreaFormula.lean` (local import closure 8 modules, **no WIP**):

* `hausdorffNormalized_image_linearMap`:
  `hausdorffNormalized V k (L '' s) = ofReal (normDet L) * hausdorffNormalized H k s`,
  `k = finrank ℝ H`. Multiplying both sides by the same normalization constant eliminates the constant, so the **norm determinant is exactly the volume factor**.
* `adjoint_apply_linearIsometry`: The adjoint of a linear isometry is a left inverse.
* `normDet_linearIsometry`: The norm determinant of a linear isometry is **1**.
* `hausdorffNormalized_image_linearIsometry`: The isometric image preserves the normalized k-dimensional measure.
* **`hausdorffNormalized_image_affine`**: After translation, the normalized k-dimensional Hausdorff measure of the isometric slice is **exactly equal** to the Lebesgue measure on the parameter space, with no residual constants.
* **`hausdorffNormalized_fiber`**: The fibers of a linear map are translations of the kernel, measured by the dimension of the kernel, and exactly correspond to the Lebesgue measure on the kernel.

The last two are fiber accounting for the coarea formula of codimension m: `L` the dimension of the kernel is `n - m`, when surjective,
The inner integral on the right-hand side is exactly taken over these fibers.

## Reuse rather than recreation

Translation invariance `Analysis.hausdorffNormalized_image_add_left` and the top-dimensional identity `KLS.hausdorffNormalized_finrank_eq_volume` are both repository **proven** results, directly used in this round, without reproof. Mathlib's `LinearMap.hausdorffMeasure_image` is also used directly. `normDet_linearIsometry` is derived from `normDet_sq` together with the adjoint left inverse property of isometries, without going through matrices.

## What was not done in this round

* **No proof of any coarea formula**; the vector-valued coarea identity has not been proven.
* **No proof of C¹ area formula**: This round covers only linear maps and affine subspaces. The local area formula for nonlinear maps (Federer area formula) has not been proven and is not considered achieved.
* No filling of holes: direct holes remain **8 (1/2/5)**; no resolution of sharp Sard, two Cheeger comparisons, or five energy holes.
* No expansion of certification or Blueprint `leanok` scope.
* **No commit, no push**, the real Git index has not been modified.

## The Next Step of the Program Outline

1. **Nonlinear local area formula**: The k-dimensional measure of the image of a C¹ parametrization equals the integral of `normDet (fderiv)`.
   repository already has a version for C¹ **graphs** (`Analysis.hausdorffNormalized_image_graphMap`) and
   `RegularChart`/[`ImplicitGraph`]/`LocalInverse`; in the general case it should be reduced locally to this.
2. Regularity of codimension m (analogue of L9): construct a family of fiber graphs over an open set of `coareaJacobian ≠ 0`.
3. Critical part of codimension m (analogue of L10) and gluing.

## Verification

* The new module and new client both compile successfully with `-DwarningAsError=true`, without `sorry`.
* The `research/audits/LinearAreaFormulaAudit.lean` 14 axiom reports only use `propext`, `Classical.choice`, and `Quot.sound`; include top-dimensional consistency (reverting the previously proven `hausdorffNormalized_finrank_eq_volume`), zero-dimensional parameter space, degenerate zero maps, and dimension accounting when surjective `finrank (ker L) = n - m`.
* Re-run all 27 audit clients (`research/audits` 20 of them, `build/audit` 7 of them), all pass strictly.
* Each of the three WIPs compiles individually, with direct proof holes **1/2/5, total count 8**, unchanged.
* Default `lake build` and root directory `python3 research/verify.py` pass; JSON evidence is `research/explorations/2026-09-16-linear-area-formula.json`, final verification saved separately in `build/audit/linear-area-formula/final-snapshot.json`.

# Jacobian identity for fibers in the m-codimensional coarea regular case

2026-09-16. This round of **proving a new theorem** delivers an **auditable subblock** in the case of regularity of coarea dimension m:
**Matching of densities** (linear forms and C¹ forms) and **measure-preserving orthogonality splitting**.
**No proof of any coarea formula**. No filling of holes, no commit, no push-forward.
Direct proof holes remain **8 (1/2/5)**, certificates remain **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260916T150413.981186Z/report.json`: 10 gates, 206 local module kernel replay,
537 entries, snapshot
`95ebf9f762031e9b1d6eb46b0d239bc4ea979b0c3d8a8fc7ef87cfe18a8ea756`.

## Boundary

Log-concave Cheeger–Buser lines (isoperimetric constants defined in alignment with Poincaré constants via bidirectional comparison, with `KLS/WIP/CheegerInfimum.lean` two remaining holes) consolidated by author **Haocheng Wang**, untouched in this round. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Why this round is not the complete regular case

The proof chain for scalar `L9` (`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`) has four segments:

1. **Graphification**: `ImplicitGraph.lean` (row 859) + `RegularChart.lean` (row 164), parametrizing the level sets near `u` simultaneously as a family of graphs, with the level value itself as coordinate;
2. **Measure-preserving splitting**: `SubgraphDivergence.lean` (row 859)'s `splitHomeomorph` and `measurePreserving_splitHomeomorph`, replacing `V` with `H × ℝ`;
3. **Fiber direction change of variables**: `FiberIntegral.lean` + the one-dimensional Jacobian theorem in Mathlib;
4. **Pointwise density matching**: `abs_deriv_mul_norm_gradient`, replacing `|∂ψ/∂t| · ‖∇u‖` with graph area density; then a countable cover and non-overlapping gluing.

The m-codimensional version of section 1 requires the **parametrized implicit function theorem taking values in m-dimensional space**, section 3 requires an m-dimensional change of variables, neither of which can be completed in a single pass; according to the row count anchor above, sections 1 and 2 themselves are on the order of one thousand seven hundred lines.
Thus, this round **does not attempt half a chain**, but instead completes the only segment that is purely new mathematics and unrelated to graphical machinery—
section 4's pointwise density matching—along with section 2's **linear/measure skeleton**.
Neither of these components depends on a yet-nonexistent graphical machine; any subsequent implementation must use them.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/CoareaGraphJacobian.lean`
(Local import closure of 9 modules, **no WIP**).

### Linear algebra

* **`det_id_add_comp_comm`**: Linear mapping form of the Weinstein–Aronszajn identity
  `det (1 + X ∘ Y) = det (1 + Y ∘ X)`, the `1` on both sides live in different spaces.
  Mathlib only has the matrix version `Matrix.det_one_add_mul_comm`.
  This step precisely corresponds to "replacing the Gram determinant on the target space with the Gram determinant on the parameter space",
  i.e., replacing the coarea Jacobian with the area Jacobian.
* **`normDet_adjoint`**: When dimensions are equal, `normDet Aᵀ = normDet A`, degenerate cases are included.
* **`coareaJacobian_eq_normDet`**: When dimensions are equal, the coarea Jacobian is equal to the area Jacobian.

### Splitting

* **`IsVectorGraphSplitting`**: `IsGraphSplitting`'s m-codimension analogy, the normal direction is the entire space `K`
  rather than a unit vector; the two axioms are orthogonality and spanning.
* **`isVectorGraphSplitting_orthogonal`**: Any subspace together with its orthogonal complement gives a splitting.
* **`finrank_orthogonal_ker_eq`**: When `L` is surjective, `finrank (ker L)ᗮ = finrank W`,
  i.e., the **regular point codimension assumption holds automatically**.
* **`IsVectorGraphSplitting.comp_adjoint`**: `L ∘ Lᵀ = P ∘ Pᵀ + Q ∘ Qᵀ` (the spanning assumption is used here).
* **`splitVectorIsometry`, `measurePreserving_split`**:
  `(y, z) ↦ ι y + κ z` is a **Lebesgue measure-preserving** map from `H × K` to `V`,
  realized via a linear isometry of `WithLp 2`, with no constant residue. This is the skeleton for subsequent Tonelli.

### Fiber Jacobian identity

* **`coareaJacobian_eq_normDet_mul_normDet_graphMapLinear`** (linear form):
  Under splitting, if the slope `A` causes the graph to lie within `ker L` (equation `(L ∘ κ) ∘ A = -(L ∘ ι)`), and
  `finrank K = finrank W`, then
  `coareaJacobian L = normDet (L ∘ κ) * normDet (graphMapLinear ι κ A)`.
* **`normDet_fderiv_mul_coareaJacobian`** (C¹ form, scalar `abs_deriv_mul_norm_gradient` analogy):
  Along the C¹ level-set family `u (ι y + κ (ψ (y, t))) = t`,
  `normDet (Dₜψ) * coareaJacobian (fderiv ℝ u x) = normDet (graphMapLinear ι κ (D_yψ))`.
  Implicit function differentiation simultaneously provides the slope equation and `(L ∘ κ) ∘ Dₜψ = 1`.
  `u` only requires differentiability at that point; no finiteness, no boundedness, no regular value assumption.

### m = 1 revert proven result

* **`graphMapLinear_eq_graphLinear`**, **`normDet_graphMapLinear_eq_graphJacobian`**:
  The new graphical model under the one-dimensional direction is the original repository `graphLinear`, with the volume factor being the previously established `graphJacobian`.
* **`abs_deriv_mul_norm_gradient_of_vectorGraphSplitting`**:
  When `m = 1`, the above C¹ identity is literally the scalar `|∂ψ/∂t| · ‖∇u‖ = graphJacobian (∇_y ψ)`.
  Together with `Analysis.coareaJacobian_fderiv`, it confirms that the new density recedes to `‖gradient u x‖` when `m = 1`.

## The co-dimension assumption `finrank K = finrank W` is necessary, not convenient

The audit client does not assert but rather provides a counterexample:
`fails_without_codimension` proves that as long as `finrank W < finrank K` and `L` are surjective,
the right-hand side is always `0` (deficiency in the rank of the normal volume factor) while the left-hand side is not `0`;
`necessity` implements this on concrete data—taking the zero subspace of `ℝ²` as the parameter space, its orthogonal complement (the entire plane) as the normal direction,
`ℝ` as the target space—orthogonality, span, and slope equations all hold, yet the codimension assumption fails, rendering the identity invalid.

## Second error in route statement file: `A0` is literally false, reported accurately and corrected

The normalization mismatch discovered in the previous round on `B1` is **exactly the same** in `A0`:
`research/audits/AreaFormulaRouteStatements.lean`'s `A0` (the goal of the route, Federer's area formula)
pairs the left-hand **original** `μH[finrank H]` with the right-hand Lebesgue measure.
The audit client's `route_A0_false` **refutes this statement**: take the identity map on the plane and the closed unit ball,
the left-hand side is the original `μH[2]`, the right-hand side is Lebesgue measure, their difference is `2² / ω₂ = 4 / π`
(`unitBallVolume_two` proves `ω₂ = π`, `normalization_constant_ne_one` proves `4/π ≠ 1`).
The correct pairing remains original to original, or `hausdorffNormalized` paired with Lebesgue, consistent with the correction in `B1`.

`A5` wrote the same mismatch, but **assuming the hypothesis and conclusion sides are consistent**, constants cancel out,
so `A5` is not thereby false; its assumption is not actually a true local area formula,
and literally cannot be connected to the intended meaning of `A0`. `A1`, `A2`, `A3`, `A4`, `B2` have consistent measure pairings, unaffected.

By convention not altering historical evidence, `research/audits/AreaFormulaRouteStatements.lean` **preserve original bytes**,
corrections are recorded in this decision and `research/audits/CoareaGraphJacobianAudit.lean`.

## What was not done in this round

* **No proof of any coarea formula**, the regular case of codimension m is **incomplete**.
* No parametric implicit function graphing (codimension m `ImplicitGraph`/`RegularChart`),
  no m-dimensional change of variables in the fiber direction, no patching from local to global.
* No handling of critical parts, sharp Sard, two Cheeger comparisons, five holes in Energy.
* No migration of holes; no expansion of certificate or Blueprint `leanok` scope; no new compatible alias added.
* **No commit, no push**, the real Git index unchanged.

## Remaining work (regular case of codimension m)

1. Local graphization of codimension m: the parametric implicit function theorem gives `ψ : H × W → K` together with its open domain of definition,
   Let `u (ι y + κ ψ(y,t)) = t`; the scalar counterpart is `exists_regularChart` and `levelChart_inverse`.
2. The m-dimensional change of variables in the fiber direction: for fixed `y`, apply Mathlib’s change-of-variables theorem on the image of `t ↦ ψ(y,t)`,
   `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, this round's `measurePreserving_split` provides
   The Tonelli skeleton of `V ≅ H × K`.
3. The 1, 2, and the current `normDet_fderiv_mul_coareaJacobian` along with the previously proven `B2`
   connect `hausdorffNormalized_image_vectorGraphMap` to obtain the local form;
4. Countable cover + disjoint gluing yields `coarea_of_contDiffOn_of_coareaJacobian_ne_zero`;
   Still needs the m-dimensional weighted slice measurability (scalar counterpart `OpenSliceMeasurable.lean`).

## Verification

* The new module and new client both compile successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **30 Axiom Report** for `research/audits/CoareaGraphJacobianAudit.lean` only uses `propext`, `Classical.choice`, and `Quot.sound`; it includes counterexamples with a zero-dimensional parameter space, a full space level-set family (without finiteness), regular point data, and a codimension assumption, as well as the falsification of the route statement `A0`.
* All **34 audit clients** are rerun (`research/audits` 27 and `build/audit` 7), all passing strictly.
* Each of the three WIPs is compiled in practice, with direct proof holes **1/2/5, total count 8**, unchanged; `research/check_ledger.py` reports 24 certificates.
* The default `lake build` and root directory `python3 research/verify.py` pass; the JSON evidence is
  `research/explorations/2026-09-16-coarea-graph-jacobian.json`, and the final verification is saved separately as
  `build/audit/coarea-graph-jacobian/final-snapshot.json`.

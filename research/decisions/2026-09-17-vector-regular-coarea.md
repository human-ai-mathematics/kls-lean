# m-dimensional coarea formula for weighted slice measurability

2026-09-17. This round of **proving a new theorem**: the requested **m-codimensional m-weighted slice measurability**, and its immediate derivation of the **m-codimensional regular case coarea formula**—analogous to `L9`. No hole-filling, no commit, no push. The direct proof hole remains **8 (1/2/5)**, the certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260916T170802.272750Z/report.json`: 10 gates, 211 local module kernel replay,
554 entries, snapshot
`90d7047331fbb80fe9b65b48b4eeaee61329c47dd97dcb372a0089ea6ccf8ad4`.
The start workspace drift is empty, and concurrent session has not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Not taking the scalar path, must clarify

Slice measurability in the scalar case (`KLS/Geometry/OpenSliceMeasurable.lean`) holds for any Borel `S ⊆ O`, without the need for regular point assumptions, via `KLS/Geometry/SurfaceSlicing.lean`'s Eilenberg slice inequality. The Eilenberg inequality of codimension m is not present repository, and Mathlib does not provide it.

So this round's "change of chart": on a family of level charts, the slice integral is simply the Tonelli section of some measurable function over the parameter–level product,
so measurability is immediate, **no slice inequalities are needed at all**.
The cost is that the slice measurability of this round **holds only at differential surjective points**.
This suffices for the regular case, but **fails to cover the critical part**—see "Things not done".

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/VectorRegularCoarea.lean`
 (211 line, local import closure 21 modules, **no WIP**).

* **`measurable_setLIntegral_inter_levelSet_levelGraphFamily`**:
  Weighted slice measurability on a graph. Using the slice description from the previous round and the weighted area formula to
  `t ↦ ∫⁻ over (Ψ''A) ∩ {u = t}, g` written as `t ↦ ∫⁻ y, (A.indicator F) (y, t)`,
  `F` is measurable on `H × W`, so `Measurable.lintegral_prod_left'` directly yields measurability.
* **`exists_vector_coarea_neighborhood_measurable`**: neighborhood form, given together with the equality and measurability.
* **`coarea_of_contDiffOn_of_coareaJacobian_ne_zero`**: **The coarea formula in the regularity case of codimension m**.
  On an open set `O` where the differential is everywhere surjective, for **any** Borel `S ⊆ O` and **any** measurable `ℝ≥0∞` weight:
  The level function is measurable, and
  `∫⁻_S coareaJacobian(Du)·g dx = ∫⁻_t ∫⁻_{S ∩ {u = t}} g dℋ^{n-m} dt`,
  The fiber measure is the normalization of the Hausdorff measure with respect to the codimension. `hausdorffNormalized V (finrank V − finrank W)`
  Assemble as in scalar `L9`: a countable cover, disjointification with `disjointed`, the neighborhood formula on each piece, and interchange via `lintegral_tsum`.

  The conclusion provided is **`Measurable`**, which is stronger than the scalar `L9`'s `AEMeasurable`;
this is a byproduct of the path-following approach.

Assume only: `u` is C¹ on the open set `O`, and `O` is everywhere `coareaJacobian (fderiv ℝ u x) ≠ 0` (i.e. a differential surjection).
**No finiteness, boundedness, integrability, regular value, SFinite**, no regularity outside `O`.

## m = 1 literal rollback of proven scalar L9

The audit client's `scalar_L9` **verbatim rewrite**repository of proven statements—gradient norm, `KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`,
`surfaceMeasure V`, `AEMeasurable`—and **fulfills the theorem of codimension m**. All three bridges are proven:
`coareaJacobian_fderiv` (density reverts to `‖gradient u x‖ₑ`),
`finrank ℝ V − finrank ℝ ℝ = finrank ℝ V − 1` makes fiber measure equal to `surfaceMeasure V`,
and `coareaJacobian_ne_zero_of_fderiv_ne_zero` (real-valued nonzero differential is surjective).

## What was not done in this round

* **No proof of the general coarea formula of codimension m** (analogous to scalar `L11`–`L13`).
  It requires handling the **critical set**, which would require a codimension m Sard or critical slice argument, neither of which is available.
* **No proof of slice measurability without regularity assumptions**.
  The scalar case uses the Eilenberg slice inequality to achieve this; **the Eilenberg inequality for codimension m has not been proven**.
  Without it, the critical part cannot be included.
* No attention to the critical part, sharp finite regular Sard, two Cheeger comparisons, five holes in energy.
* No migration of holes; no extension of certificates or Blueprint `leanok`; no new compatible aliases; no weakening of already proven conclusions.
* **No commit, no push**, the real Git index has not been modified.

## Route statement verification

This round of re-execution found no new route statement errors. The two recorded issues remain `B1` and the falsified `A0`.
`research/audits/AreaFormulaRouteStatements.lean` continues to preserve the original bytes.

## Current status of the m-codimensional program

Proved: coarea Jacobian and regular set characterization, linear area formula and affine fiber, A1, B1/B2 graph area formula, fiber Jacobian identity, measure-preserving splitting, parametrized implicit function graphization, fiber direction m-dimensional change of variables, weighted graph area formula, local coarea equation, and the regular case coarea formula in this round.

Still open: the Eilenberg slice inequality for codimension m; measurability of slices without regularity;
the Sard/critical slice for codimension m; hence the general codimension m coarea formula.
Federer's area formula `A0` (its route statement has been falsified) and `A2`–`A5` are also still open.

## Verification

* The new module and new client have been compiled successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **11 Axiom Report** of `research/audits/VectorRegularCoareaAudit.lean` only uses
  `propext`, `Classical.choice`, `Quot.sound`; including the empty set, the full space (without finiteness), and weights that are constantly `∞`;
  Zero-dimensional target space (in this case, each point is regular), and m = 1 character-by-character retreat scalar `L9`
  (The last report is for the repository’s proved scalar `L9` itself, for comparison).
* Reran all **38 audit clients** (31 in `research/audits`, 7 in `build/audit`); all passed strict compilation.
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports 24 certificates.
* Default `lake build` and root directory `python3 research/verify.py` are connected; evidence JSON is
  `research/explorations/2026-09-17-vector-regular-coarea.json`, final verification and save
  `build/audit/vector-regular-coarea/final-snapshot.json`.

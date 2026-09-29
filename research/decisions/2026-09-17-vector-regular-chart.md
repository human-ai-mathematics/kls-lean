# Parametric implicit graph representation in codimension m

2026-09-17. This round **proves a new theorem**, completing the **second subblock** in the case of m-codimensional coarea regularity:
**Parametric implicit graph representation**: represent the **entire family** of fibers of `u : V → W` near a regular point simultaneously as graphs of one C¹ map,
The level value itself is a parameter. *No coarea formula has been proven yet.*
No migration, no commit, no push. Direct proof holes remain **8 (1/2/5)**, certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260916T160637.697547Z/report.json`: 10 gates, 207 local module kernel replay,
541 entries, snapshot
`3310e7e26c2c35e83d9cbb93b0bc21c51f65adf4279d8af3fd5f275fd7868dfc`.
The start workspace drift is empty, and concurrent session has not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/VectorRegularChart.lean`
 (355 line, local import closure of 16 modules, **no WIP**). It is an m-codimensional analogy of `RegularChart.lean`.

### One True Difference from the Scalar Case

The chart of a scalar is `x ↦ graphRetract ι x + u x • e`, still mapping to `V`, because the normal direction is a straight line in `V`,
`u x ∈ ℝ` can be multiplied onto it. The `u x ∈ W` of codimension m is **not in `V`**, so the current chart is changed to map to a **product**.

`Φ x = (ιᵀ x, u x) : H × W`,

Thus, there is no need at all to identify the direction space `K` with the target space `W`, nor to select a copy of `V` inside `W`.
repository's `exists_contDiffOn_localInverse` was originally formulated as a narrative for two distinct spaces and can be used directly.

* **`flattenVectorEquiv`**: `Φ` is continuously linearly equivalent at regular points.
  Assume that "the parameter factor is the nuclear direction" `L ∘ ι = 0` and "the normal factor is bijectively sent to the target space by `Q = L ∘ κ`."
  **The inverse is explicitly written out**: `(y, w) ↦ ι y + κ (Q⁻¹ w)`, not relying on dimension counting,
  So degenerate cases do not need separate discussion.
* **`exists_vectorRegularChart`**: `O` on C¹ of `u` gives a local homeomorphism of `D : V ≃ H × W` near regular points,
  Both sides are C¹, `D.source ⊆ O`; **`O` does not require nor assert any regularity outside**.
* **`vectorLevelChart_inverse`**: The inverse chart is exactly the graph over each level, and that graph achieves the level:
  `D.symm (y, t) = ι y + κ (ψ (y, t))` and `u (D.symm (y, t)) = t`, both defined on the **same jointly open domain**.
* **`exists_levelGraphFamily`**: Package the above into a concrete consumable form——
  Open set `Ω ⊆ H × W`, **global C¹** `ψ : H × W → K`, open neighborhood `N ⊆ O` contains `x₀`, satisfies
  `∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2`, the graph map is a bijection from `Ω` to `N`.
  The global C¹ property of `ψ` is obtained by taking local representatives on small balls within the chart target, as done by `exists_contDiff_one_eqOn_ball`.
  In the same manner as scalar files.
* **`comp_ker_subtypeₗᵢ_eq_zero`, `bijective_comp_orthogonal_subtypeₗᵢ`,
  `exists_levelGraphFamily_of_coareaJacobian_ne_zero`**:
  The regularity assumption holds automatically—the parameter space takes the kernel of the differential, and the normal factor takes its orthogonal complement,
  The codimension `finrank Pᗮ = finrank W` is given by the previous round's `finrank_orthogonal_ker_eq`.
  The entry assumption is only `coareaJacobian (fderiv ℝ u x₀) ≠ 0`.

### Two interfaces with existing certificates

* **`slice_eq_image_vectorGraphMap`**: `N ∩ {u = t}` is exactly the graph of `y ↦ ψ (y, t)` over the parameter slice.
* **`hausdorffNormalized_slice_of_levelGraphFamily`**: Thus the previously proven `B2`
   (`hausdorffNormalized_image_vectorGraphMap`)directly compute the normalized `(n-m)`-dimensional measure of this fiber,
  Equal to the Lebesgue integral of the graph area density over the parameter slice. **This is the case with weight one**;
  The general coarea requiring a *weighted* version (m-codimensional analogy of `setLIntegral_image_graphMap`) has not been proven.
* **`normDet_fderiv_mul_coareaJacobian_of_levelGraphFamily`**: This clan literally satisfies the previous round
  The assumption of `normDet_fderiv_mul_coareaJacobian`, so density matching is achieved on both sides of the entire chart.

## m = 1 revert proven scalar shapes

In the audit client: `lineIsometry` makes the straight line spanned by the unit vector `e` into `ℝ →ₗᵢ[ℝ] V`,
`graphProj_lineIsometry` Proof `graphProj = ⟪e, ·⟫`,
`isVectorGraphSplitting_of_isGraphSplitting` The certification of scalar `IsGraphSplitting` is the one-dimensional factorizer's
`IsVectorGraphSplitting`**. Thus `codimension_one_levelGraphFamily` from the original scalar hypothesis**
( `IsGraphSplitting ι e` and `gradient u x₀ = c • e`, `c ≠ 0` ) start,
The family producing `u (ι p.1 + ψ p • e) = p.2` ——
This is exactly the `Analysis.setLIntegral_coarea_graph_family` already proven that consumes the `hlevel` shape.

## What was not done in this round

* No proof of any coarea formula; the case of regularity in codimension m is still incomplete.
* No fiber-directional m-dimensional change of variables (on the ambient side),
  no weighted codimension m area formula (on the fiber side),
  no local-to-global countable gluing, no measurability of weighted slices in codimension m.
* No migration of holes; no expansion of certification or Blueprint `leanok` scope; no new compatible alias added; no weakening of previously proven statements.
* No addition of unnecessary assumptions: no boundedness, finite volume, integrability, regular value, SFinite.
* No commit, no push; the real Git index remains unchanged.

## Route statement verification

This round of rerun did not reveal any new route statement errors. The two recorded cases still only have
the previous round's `B1` (decided by 2026-09-16 `vector-graph-area`) and
the previous round's `A0` (decided by 2026-09-16 `coarea-graph-jacobian`), `route_A0_false` has been refuted;
`A5` is consistent on both sides thus not false, `A1`–`A4` and `B2` are unaffected.
`research/audits/AreaFormulaRouteStatements.lean` continues to **retain the original bytes**.

## Remaining work (regular case of codimension m)

1. **Ambient side**: For a fixed `y`, perform an m-dimensional change of variables on the image of `t ↦ ψ (y, t)`
   (The `lintegral_image_eq_lintegral_abs_det_fderiv_mul` of Mathlib,)
   The skeleton is the `measurePreserving_split` of the previous round (`V ≅ H × K` preserves Lebesgue measure);
2. **Fiber side**: Weighted co-dimension m coarea formula, analogy to `setLIntegral_image_graphMap`;
3. Use the current round's `normDet_fderiv_mul_coareaJacobian_of_levelGraphFamily` to align the densities on both sides, then assemble via Tonelli
   Local coarea formula (scalar counterpart `setLIntegral_coarea_graph_family`);
4. Countable cover + disjoint gluing, together with the measurability of weighted slices of codimension m (scalar counterpart `OpenSliceMeasurable.lean`),
   Get `coarea_of_contDiffOn_of_coareaJacobian_ne_zero`.

## Verification

* The new module and new client both compile successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **25 Axiom Report** for `research/audits/VectorRegularChartAudit.lean` only uses `propext`, `Classical.choice`, and `Quot.sound`; it includes the zero-dimensional parameter space, a **zero-dimensional target space** (in this case, every point is regular), the full space (without finiteness), and the case m = 1 returning to scalar shape with the complete chain.
* All **35 audit clients** are rerun (`research/audits` 28 and `build/audit` 7), all passing strictly.
* Three WIPs are compiled in practice one by one, with direct proof holes **1/2/5, total 8**, unchanged; `research/check_ledger.py` issues 24 certificates.
* Default `lake build` and root directory `python3 research/verify.py` pass; the JSON evidence is `research/explorations/2026-09-17-vector-regular-chart.json`, and the final verification is saved as `build/audit/vector-regular-chart/final-snapshot.json`.

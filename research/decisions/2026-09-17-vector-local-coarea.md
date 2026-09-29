# Weighted m-Codimensional Graph Area Formula, and a Local Coarea Formula on a Graph

2026-09-17. This round's **proof of a new theorem**: the requested **weighted co-dimension m graph area formula**,
and its direct consequence when combined with the results from the previous two rounds—the **local coarea identity on a graph**,
and then the **coarea identity on a neighborhood of each regular point**.
**This is not the regular coarea formula of co-dimension m**; the gap is explicitly stated at the end.
No hole-filling, no commit, no push. The direct proof hole remains **8 (1/2/5)**, and the certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260916T165144.989890Z/report.json`: 10 gates, 209 local module kernel replay,
549 entries, snapshot
`b2c11a93ec5bfe245ad6791cd300eeebae4e1e1d74fb979909db61c7f11505f6`.
The start workspace drift is empty, and concurrent session has not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Exact Results

### 1. Weighted m-Codimensional Graph Area Formula

New module `formalization/FunctionalInequalities/Analysis/VectorGraphIntegral.lean`
 (92 line, local import closure 11 modules, **no WIP**),
`OpenGraphIntegral.lean` / `GraphIntegral.lean` co-dimension m analogy.

* **`map_vectorGraphMap_withDensity`**: Upgrade `B2` (the equality for set measures) to an **equality of measures**—
  The parametrization maps the Jacobian-weighted Lebesgue measure to the normalized surface measure restricted to the graph.
  Two properties repository used here have already been proven: the graph map is **constructively injective**, and its image is measurable.
* **`setLIntegral_image_vectorGraphMap`**: **Weighted (m-codimensional) graph area formula**.
  The surface integral of any measurable `ℝ≥0∞` weight over a C¹ graph equals the Lebesgue integral of that weight against the graph area density.
  `B2` is the case of `f = 1`; in the audit, the word-by-word recovery is performed.
  **No integrability, no finiteness, no boundedness**; the parameter set only needs to be measurable.

### II. Local coarea formula on a single graph

New module `formalization/FunctionalInequalities/Analysis/VectorLocalCoarea.lean`
(158 line, local import closure 20 modules, **no WIP**). Each of the three inputs originates from one round:

* Environment side `setLIntegral_coareaJacobian_levelGraphFamily` (previous round);
* Fiber side `setLIntegral_image_vectorGraphMap` (first part of this round);
* Slice description `slice_eq_image_vectorGraphMap` (visualized in the previous round).

The Tonelli on the level variable ties the three together:

* **`setLIntegral_coarea_levelGraphFamily`**: m-dimensional co-dimension analog of a scalar `setLIntegral_coarea_graph_family`.
* **`exists_vector_coarea_neighborhood`**: *Every point of a differential surjection has an open neighborhood,*
  *on any Borel subset of which, for any measurable `ℝ≥0∞` weight, the coarea formula holds*,
  *with surface measure of dimension `finrank V - finrank W` (i.e., `n - m`).*
  *The neighborhood is independent of the weight.* This is the m-dimensional co-dimension analog of a scalar `KLS.exists_regular_coarea_neighborhood`.

Assume only: `u` is C¹ on the open set `O`, and the differential is surjective at that point. `O` has no regularity requirements; no finiteness, boundedness, integrability, regular value, SFinite.

## m = 1 revert proven result

* `codimension_one_graphArea`: Retrieve repository from the weighted formula of co-dimension m, which is already established `Analysis.setLIntegral_image_graphMap`.
* `codimension_one_coarea_density`: The ambient density in the local coarea equation becomes `‖gradient u x‖ₑ` when `m = 1` (as established in `coareaJacobian_fderiv`), i.e., the integrand of the scalar `L9`.

## What was not done in this round

This is not the regular coarea formula for codimension m. Two more items are missing:

1. **Measurability of weighted slices of codimension m**: `t ↦ ∫⁻ over S ∩ {u = t}`'s `AEMeasurable`,
   the scalar counterpart is `KLS/Geometry/OpenSliceMeasurable.lean`.
   Without it, the sum and outer integral cannot be interchanged during gluing (`lintegral_tsum` requires measurability).

2. **Countable cover + non-overlapping gluing**: Assembling the above neighborhood forms into an equation over the entire regular open set,
   the scalar counterpart is the patch in `KLS/Geometry/RegularCoarea.lean`.

Moreover: no encounter with critical parts, no sharp Sard, no two Cheeger comparisons, five holes in the energy;
no migration holes; no expansion of certification or Blueprint `leanok` scope; no new compatible alias; no weakening of already proven conclusions.
**No commit, no push**, the real Git index remains unchanged.

## Route statement verification

This round of re-execution found no new route statement errors. The two recorded issues remain `B1` and the falsified `A0`.
`research/audits/AreaFormulaRouteStatements.lean` continues to preserve the original bytes.

## Verification

* Two new modules and new clients compile successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **15 Axiom Report** for `research/audits/VectorLocalCoareaAudit.lean` uses only `propext`, `Classical.choice`, and `Quot.sound`; includes retrieval of `B2`, full space, weight always equal to `∞`, zero-dimensional parameter space, zero-dimensional target space (in this case, every point is regular), and two backsteps for m = 1.
* All 37 audit clients are rerun (`research/audits` 30 and `build/audit` 7), all passing strictly.
* Three WIPs are compiled in practice, each with direct proof hole 1/2/5, total count 8, unchanged; `research/check_ledger.py` reports 24 certificates.
* Default `lake build` and root directory `python3 research/verify.py` pass; JSON evidence is `research/explorations/2026-09-17-vector-local-coarea.json`, final verification saved as `build/audit/vector-local-coarea/final-snapshot.json`.

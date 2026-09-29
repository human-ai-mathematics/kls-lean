# Measurability of m-codimensional compact slices, and weighted slice measurability without regularity

2026-09-17. This round's **proof of a new theorem**: the requested **measurability of m-codimensional compact slices**, connecting to the previous round's Eilenberg inequality to obtain **weighted slice measurability without any regularity assumptions** (Borel set form and open C¹ domain form).
**This is not the coarea formula**—what is removed is **half of the regularity assumption concerning measurability**, not the coarea **equation** itself.
No hole-filling, no commit, no push-forward. The direct proof hole remains **8 (1/2/5)**, and the certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260916T180259.203752Z/report.json`: 10 gates, 213 local module kernel replay,
562 entries, snapshot
`cfc6a0899b7ac59cf4524e972a36aa6a71d8ec4f4449b100d7ce0fd6122ffab1`.
The start workspace drift is empty, and concurrent session has not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Only half needs to be redone

`Analysis/HausdorffContent.lean` has two things: the scale limit of the cost of a scaled-open cover is `μH[d]`,
and the cost of an open cover of a slice of a compact set at a fixed scale with respect to a real level upper semicontinuous.
The former concerns only the ambient space and is independent of the target space, and is reused unchanged in this round; only the latter refers to the target space, and thus a new treatment is performed for the metric target space.
The argument is unchanged: an open set containing a slice also contains nearby slices,
because the compact remainder outside the open set keeps the map at a positive distance from that level—
in the real-valued case, that distance is `|u x − t|`, the codimension m is `dist (u x) t`, and the rest is identical.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/VectorSliceMeasurable.lean`
 (294 line, local import closure 13 modules, **no WIP**).

* **`isOpen_setOf_slice_subset_vector`, `upperSemicontinuous_openCoverCost_slice_vector`**:
  The previous step holds for any metric target space.
* **`measurable_hausdorffMeasure_inter_levelSet_vector`**: **Measurability of compact slices of codimension m**——
  `S` compact, `u` continuous with respect to a metric space, `t ↦ μH[d] (S ∩ {u = t})` is Borel measurable.
  No requirement for `u` Lipschitz, no requirement for `S` finite measure in any dimension, `d = 0` allowed.
* **`measurable_hausdorffNormalized_inter_levelSet_vector`**: The same conclusion under the normalization convention.
* **`aemeasurable_hausdorffNormalized_inter_levelSet_vector`**: Borel set form.
  By the structure of `KLS/Geometry/SurfaceSlicing.lean`: inner regularity expresses Borel sets as exhaustion by compact sets, differing by at most one.
  Lebesgue null remainder, compact pieces handled by upper semicontinuous, the remainder handled by the previous round's **Eilenberg null slice**.
  Both raw materials are necessary; neither alone is sufficient.
* **`aemeasurable_setLIntegral_inter_levelSet_vector`**: Weighted form, via monotone simple functions.
  Weights are arbitrarily measurable `ℝ≥0∞`, possibly unbounded, and possibly constantly `∞`.
* **`aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector`**:
  Localizing to a map that is only C¹ on an open set and its any measurable subset,
  The scalar counterpart is `KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn`.

**No differential surjections are required.** Unlike the paths in `Analysis/VectorRegularCoarea.lean`, these statements **cover the critical parts of the domain**—audit evidence uses constant maps (with differential nowhere surjective when the fiber dimension is positive) to witness.

Assume only: `u` on the set is Lipschitz (or C¹ on an open set), the set is measurable, and the fiber dimension plus the codimension equals the ambient dimension.

## m = 1 revert the proven scalar result and accurately note one difference

* `scalar_compact_slices`: retrieve character by character `Analysis.measurable_hausdorffMeasure_inter_levelSet`.
* `scalar_open_slices`: retrieve character by character `KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn`,
  **but require an additional `1 ≤ finrank V`**. This is the **difference as faithfully recorded**:
  the statement of codimension m assumes `k + finrank W = finrank V`,
  so the zero-dimensional ambient space (scalar statements are also covered, via natural subtraction and subpoint branching) falls outside its range.

## What was not done in this round

* No proof of any coarea formula. The measurability half of the regularity assumption is removed;
  the coarea *equation* still holds only at differential surjections.
* The critical part of the coarea equation requires a Sard or critical slice argument of codimension m, *not proven*.
* No modification to `Analysis/HausdorffContent.lean`, `Analysis/HausdorffSlicing.lean`,
  `KLS/Geometry/SurfaceSlicing.lean`, or `KLS/Geometry/OpenSliceMeasurable.lean`—
  the codimension m version is a parallel new module.
* No touch to sharp finite regular Sard, two Cheeger comparisons, five holes of Energy;
  no hole migration; no expansion of certificate or Blueprint `leanok` scope; no new compatible alias added; no weakening of already proven conclusions.
* **No commit, no push**, the real Git index is unchanged.

## Route statement verification

This round of re-execution found no new route statement errors. The two recorded issues remain `B1` and the falsified `A0`.
`research/audits/AreaFormulaRouteStatements.lean` continues to preserve the original bytes.

## Remaining work

1. **Sard or critical slice of codimension m**: The coarea contribution on the critical set is zero,
the scalar counterpart in repository is `Analysis/Sard.lean` one-dimensional and the critical slice has zero measure;
2. Combining it with the measurability of this round and the regularity equation from the previous round, we obtain the **generalized coarea formula of codimension m**
(the scalar analogues `L11`–`L13`).

## Verification

* The new module and new client have been compiled successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **18 Axiom Report** of `research/audits/VectorSliceMeasurableAudit.lean` only uses
  `propext`, `Classical.choice`, `Quot.sound`; including constant maps (critical case), weights constantly equal to `∞`,
  Zero-dimensional target space, and two backtracks for m = 1
  (The last two reports are the two scalar statements itself proven by repository, for comparison.)
* Reran all **40 audit clients** (33 in `research/audits`, 7 in `build/audit`); all passed strict compilation.
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports 24 certificates.
* Default `lake build` and root directory `python3 research/verify.py` are connected; evidence JSON is
  `research/explorations/2026-09-17-vector-slice-measurable.json`, final verification and save
  `build/audit/vector-slice-measurable/final-snapshot.json`.

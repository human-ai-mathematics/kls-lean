# Lipschitz level slices of the zero measure set

2026-09-15. This round **proves L2 of the weighted coarea route**: the level sets of volume zero sets under Lipschitz maps almost everywhere have zero surface measure. No commit, no push, no alteration of historical decisions. The starting HEAD is
`2965b32bc79bdb24921c633df12102450eaedcc4`; the starting verification receipt is
`build/verification/20260914T194849.197366Z/report.json` (byte-for-byte identical to `build/verification/latest.json`, SHA256 `cc265566fc376ff989c601791ca62964f9240578b7f6a439e49de20569738aaa`), and the recomputed full snapshot matches the receipt: 410 files, SHA256 `0fb70f2270d6c2f6c52ba89931a3ffcf80b8c5d9a4eea3ef671a99157283c53b`. The byte-for-byte comparison refers to consistent file-level SHA256 (including deleted items) and full snapshot structure, not merely the HEAD.

## Content of this round of proof

Add two modules, together with two main conclusions and two auxiliary lemmas, all relying only on the standard three axioms, no `sorry`, no new axioms, no placeholder definitions.

### `formalization/FunctionalInequalities/Analysis/HausdorffSlicing.lean`

Only depends on Mathlib (`Mathlib.MeasureTheory.Measure.Hausdorff`, `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`, `Mathlib.MeasureTheory.Integral.Lebesgue.Add`),
holds for any `EMetricSpace`, no need for vector space, inner product, finite dimension, or Haar measure:

```lean
theorem FunctionalInequalities.Analysis.exists_cover_of_hausdorffMeasure_eq_zero
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} {N : Set X} (hN : μH[d] N = 0) {r c : ℝ≥0∞} (hr : 0 < r) (hc : 0 < c) :
    ∃ T : ℕ → Set X, N ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧
      ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d < c

theorem FunctionalInequalities.Analysis.exists_levelSlab
    {X : Type*} [EMetricSpace X]
    {u : X → ℝ} {K : ℝ≥0} {N : Set X} (hu : LipschitzOnWith K u N)
    (T : ℕ → Set X) (hT : ∀ i, Metric.ediam (T i) ≠ ∞) :
    ∃ J : ℕ → Set ℝ, (∀ i, MeasurableSet (J i)) ∧
      (∀ i, volume (J i) ≤ 2 * (K : ℝ≥0∞) * Metric.ediam (T i)) ∧
      (∀ i, ∀ x ∈ T i ∩ N, u x ∈ J i)

theorem FunctionalInequalities.Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {u : X → ℝ} {K : ℝ≥0} {N : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u N) (hN : μH[d + 1] N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), μH[d] (N ∩ {x | u x = t}) = 0
```

### `formalization/FunctionalInequalities/KLS/Geometry/SurfaceSlicing.lean`

Normalized packaging given by the existing `KLS.surfaceMeasure` definition. No replacement of measures or conclusions:

```lean
theorem FunctionalInequalities.KLS.ae_surfaceMeasure_inter_levelSet_eq_zero
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {N : Set V}
    (hu : LipschitzOnWith K u N) (hN : (volume : Measure V) N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (N ∩ {x | u x = t}) = 0
```

Compared to the L2 statement in the route record, only `[CompleteSpace V]` was removed (the proof never used it, and finite-dimensional inner product spaces are already complete), with no additional assumptions: `N` does not require measurability, boundedness, non-emptiness, or non-zero measure beyond these properties, `u` is only Lipschitz on `N`, `K` is arbitrary (including `K = 0`), and `V` allows zero-dimensional cases. The `build/audit/NullSlicingAudit.lean` `target` is proven by verbatim restatement and proof of the original statement with `[CompleteSpace V]`, so the L2 statement in the route record is now closed.

## Proof design

**Not Rademacher.** Rademacher only gives "the volume of the set of non-differentiable points is zero," regarding the co-dimension one measure of a single level set.
No conclusions; the current statement holds for any Lipschitz `u` on `N`, even without requiring `u` to be measurable.

**Covering + measurable dominating function + Fatou.** For each scale `k`:

1. From the infimum expression of `Measure.hausdorffMeasure_apply`, extract a countable cover from `μH[d+1] N = 0`
   `T k : ℕ → Set X`, diameter `≤ (k+1)⁻¹`, total `(d+1)`-dimensional covering cost `< (k+1)⁻¹`.
   The cost of Mathlib includes built-in `⨆ _ : (T i).Nonempty` protection, so the cost of an empty block is `0`,
   The pathological cases of `d + 1 = 0` do not occur (in this round `0 ≤ d`).
2. For each covering block intersecting `N`, pick a point `p` in `N` within the block, and set the interval on the horizontal axis to
   `Metric.closedBall (u p) (K · diam)`; Lipschitz estimate used only on `N`,
   The image under `u` of the piece intersected with `N` lies in this interval, whose length is `≤ 2 K · diam`.
   Blocks disjoint from `N` take the empty interval.
3. Dominating function `F k t := ∑' i, (J k i).indicator (fun _ => ediam (T k i) ^ d) t`
   **Pointwise measurable** (constant × indicator of measurable set), hence `F k` is measurable; this step uses
   `ENNReal.tsum_eq_iSup_sum` The measurability of a finite sum does not introduce new imports.
4. Pointwise bound: for fixed `t`, use the subtype `{i // t ∈ J k i}` as the index when applying
   `Measure.hausdorffMeasure_le_liminf_tsum`, get
   `μH[d] (N ∩ {u = t}) ≤ liminf (F · t)`. Using subtypes instead of the entire `ℕ` is necessary:
   `d = 0` spacetime blocks contribute `0 ^ (0 : ℝ) = 1`, and summing over the entire set yields `⊤`.
5. Integral bound: `lintegral_tsum` and `lintegral_indicator_const` give
   `∫⁻ F k ≤ 2 K (k+1)⁻¹`. At `K = 0`, each interval is a single point with right endpoint `0`, no branching is needed.
6. Fatou (`lintegral_liminf_le'`)acts on **proven measurable** `F k`s,
   `∫⁻ liminf (F · t) = 0`, and then by `lintegral_eq_zero_iff` (provided that `liminf` is measurable,
   (By `Measurable.liminf`) we obtain `liminf (F · t) = 0` almost everywhere, pointwise upper bound closeout.

**No circular reasoning.** The entire process never assumes the section function.
`fun t => μH[d] (N ∩ {u = t})` measurable, and also does not derive a.e from its `lintegral = 0`. Zero:
`lintegral_eq_zero_iff` Only applied to the measurable dominating functions constructed. The measurability of the sections of L3–L5 has not yet been proven.

**Handle zero-dimensional case separately, not treating zero-dimensional surface measure as zero measure.** `finrank ℝ V = 0` when natural number subtraction gives
`surfaceMeasure V = hausdorffNormalized V 0 = hausdorffNormalized V (finrank ℝ V)`,
by existing `KLS.hausdorffNormalized_finrank_eq_volume` equals Lebesgue measure; the section is a subset of `N`,
monotonicity gives zero for **each** `t`. The audit client separately computes
`surfaceMeasure (EuclideanSpace ℝ (Fin 0)) univ = 1`, i.e., the zero-dimensional fiber measure is unit mass at a point,
`ℋ⁰` is not zero measure. In positive dimensions `((finrank - 1 : ℕ) : ℝ) + 1 = (finrank : ℝ)` requires `1 ≤ finrank`,
so the dimension branching is necessary, not decorative.

**One-dimensional `ℋ⁰` preserves counting effects.** The client computes
`surfaceMeasure ℝ ({0} ∩ {x | id x = 0}) = 1`: `N = {0}` and `u = id` when the horizontal `t = 0`
has a cross-sectional measure of `1`, so "almost everywhere" is substantive, and cannot be strengthened to "everywhere".
In the plane `surfaceMeasure (EuclideanSpace ℝ (Fin 2)) (segment ℝ 0 e) ≠ 0` (`e ≠ 0`)
demonstrates that the fiber measure is non-zero in the positive codimension case.

## Placement Determines

Original Hausdorff lemma placed `Analysis/HausdorffSlicing.lean`, **local import closure is empty**, relying only on Mathlib, consistent with the suggestion in Section 6 of the route record "the underlying cover of L1/L2/L3 can be expressed in `Analysis/HausdorffSlicing.lean` using raw `μH`" (filename taken according to implemented content `HausdorffSlicing`). Normalization packaging placed `KLS/Geometry/SurfaceSlicing.lean`, importing `Analysis/HausdorffSlicing.lean` and `KLS/Geometry/SmoothDomain.lean` (the latter providing agreement checking `hausdorffNormalized_finrank_eq_volume`).

No migration of existing declarations, no modification of any existing public signatures, no changes to the current content of any `.lean` library files,
no expansion of certificate or Blueprint `leanok` scope, no addition of new modules to `FunctionalInequalities.lean`
Certification aggregation import (consistent with WIP and existing non-aggregated module practices; the two new modules are still fully replayed by `verify.py`'s
`lake build +Module` and `leanchecker`).

## What was not done in this round

* **Section measurability bridge for L3–L5** remains unproven: Borel measurability of fiber of compact sets (L3), fiber of Borel sets
  a.e. measurability (L4), and the version with measurable weights (L5) are still missing. L2 itself does not provide measurability.
* **Three original coarea holes** unchanged: `Analysis.aemeasurable_lintegral_levelSet`,[, ]
  `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`,
  `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`.
* Sharp `C^(finrank)` `Analysis.sard` (now without downstream consumers) and
  `Analysis.ae_forall_fderiv_ne_zero` still carries `sorryAx`.
* `smoothConstant_le_minkowskiConstant`,
  `smoothConstant_mul_lintegral_min_superlevel_le`, two Cheeger constants being equal has not been proven.
* The general L1 with a constant (Eilenberg measurable upper bound, right end `C K volume S`) has no proof: this round only handles the zero-measure special case,
  The proof uses "total coverage cost tending to zero," without providing any finite positive dimensional constant `C`.
* Whitney's extension without touching L6/L6a/L7 for C¹ piecewise, and without touching L8–L12.

## Verification

* `FunctionalInequalities/Analysis/HausdorffSlicing.lean` and
  `FunctionalInequalities/KLS/Geometry/SurfaceSlicing.lean` all with
  `-DwarningAsError=true` Compiles independently.
* `build/audit/NullSlicingAudit.lean` compiles with `-DwarningAsError=true`: 1 statements
  `#check` (verbatim record of route logs L2), 1 theorem `target` (with original statement `[CompleteSpace V]`),
  9 Theorem of l independent consumers/degenerate case (without usage of `N` measurable subsets, `K = 0`,
  Slice integral forms with arbitrary `ℝ≥0∞` weights, zero-dimensional, zero-dimensional unit mass, one-dimensional and exceptional level cases,
  Lipschitz on only `N`, discontinuous `u` (planar non-degenerate segments), and 14 conditions `#print axioms`.
  All  14 statements depend only on `propext`, `Classical.choice`, `Quot.sound`; **not on `sorryAx`**.
* Retrace `WeightedCoareaRouteStatements`, `WeightedCoareaInfrastructure`, `AreaFormulaAudit`,
  `CheegerInfimumAudit`, `MinkowskiConstantAudit`, `SuperlevelSardScope`, `SmoothSardAudit`,
  `SmoothSardRouteStatements`, all strictly compiled and passed with `-DwarningAsError=true`, with no modifications made.
* Three WIP files were successfully compiled in practice, with direct proof holes diagnosed as **3/3/5**, total count **11**——L2 leaves no original entries
  coarea hole, so this number remains as expected.
* Default `lake build` is connected to the root directory `python3 research/verify.py`. Final verification receipt is
  `build/verification/latest.json`, exactly equal to the final complete source code snapshot; evidence JSON is
  `research/explorations/2026-09-15-null-slicing.json`, ignore the final verification save in the directory
  `build/audit/nullslicing-final-snapshot.json`, avoid creating cyclic hashes for the verification receipt itself.
  `build/audit` Not present in regular source code snapshots, hence its hash is separately bound by evidence JSON.
* Certification still **24**, perimeter infrastructure still **missing** (gap list updated in this round:
  L2 changed from "missing" to "proven", L3–L5 remain as gaps).

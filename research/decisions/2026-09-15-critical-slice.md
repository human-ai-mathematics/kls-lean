# Null slices of the critical set of a C¹ function (L10)

2026-09-15. This round **proves L10 of the weighted coarea route**: the critical set of a real-valued `C¹` function has zero `surfaceMeasure` on almost every level set. This is the first true downstream consumer of L1. No commit, no push, no alteration of historical decisions.
The starting HEAD is `2965b32bc79bdb24921c633df12102450eaedcc4`; the starting verification receipt is
`build/verification/20260915T035117.865459Z/report.json` (bit-for-bit identical to `build/verification/latest.json`), and the recomputed full snapshot matches the receipt: 424 files, SHA256 `2fb5014b1bbfb1bbd8b05a41cbc7a5e45529fc97783da9305036597d7be7ce9d`. The bit-for-bit comparison here refers to per-file SHA256 (including deleted entries) and consistent full snapshot structure, not merely the HEAD.

## Content of this round of proof

New module `formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean`:


```lean
theorem FunctionalInequalities.KLS.isClosed_critical {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    IsClosed {x : V | fderiv ℝ u x = 0}

theorem FunctionalInequalities.KLS.exists_lipschitzOnWith_critical_cover
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ T : ℕ → Set V, Pairwise (Function.onFun Disjoint T) ∧ (∀ n, MeasurableSet (T n)) ∧
      {x : V | fderiv ℝ u x = 0} ⊆ ⋃ n, T n ∧
      ∀ n, LipschitzOnWith ε u ({x : V | fderiv ℝ u x = 0} ∩ T n)

theorem FunctionalInequalities.KLS.ae_surfaceMeasure_critical_ball_eq_zero
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) (R : ℕ) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure V ({x : V | fderiv ℝ u x = 0} ∩ Metric.closedBall 0 R ∩ {x | u x = t}) = 0

theorem FunctionalInequalities.KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure V ({x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0
```

Compared to the L10 route record, only removed `[CompleteSpace V]` that was never used, with no additional assumptions:
`u` Does not require Lipschitz, bounded, or compact support; the critical set does not require measurability (it is automatically a closed set);
`V` Allows zero-dimensional. Client `target` uses the primitive statement with `[CompleteSpace V]` verbatim and proves it.

## This is not the Sard theorem

**Must distinguish between two things**, this round only addressed the latter:

* **Sard**: The critical value set `u '' {fderiv = 0}` has Lebesgue measure zero in `ℝ`. General regularity is required `C^(finrank)`;
  in this repository, it remains a direct proof hole `Analysis.sard` (no changes made, no downstream consumers, still carries `sorryAx`).
* **L10**: For each level set, the codimension-one measure of the critical portion is zero, almost every level. It holds for any dimension for functions that are only `C¹`.

L10 **does not imply** Sard: a `C¹` function can entirely have a critical value set of positive measure, and L10 makes no assertion about this, only stating that the `ℋ^{n-1}` measure of the critical parts at each level is zero. The client's `constant_exceptional_level` makes the distinction through concrete computation: the critical set of a constant function is the entire space, so its section at that level is the entire line, `surfaceMeasure ℝ ≠ 0`. Thus, L10's "almost everywhere" cannot be strengthened to "everywhere," and the critical set itself carries no smallness.

## Proof design

**The first true downstream consumer of L1.** The derivative is zero on the critical set, and the approximating linear map from Mathlib's `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` takes the value of the derivative (the final conclusion of which yields `∃ y ∈ s, A n = f' y`), so these linear maps are **identically zero** on the critical set, and `ApproximatesLinearOn u 0 (C ∩ T n) ε` is directly `LipschitzOnWith ε u (C ∩ T n)`.
This lemma also provides a measurable, pairwise disjoint partition, so no further `disjointed` is needed.

Fix a ball radius `R` and scale `ε = (k+1)⁻¹`:

1. Take the above partition, and let `D n := C ∩ closedBall 0 R ∩ T n` (measurable, pairwise disjoint, and their union is `C ∩ ball`).
2. For each `D n` use **L1** (`KLS.exists_measurable_majorant`) to obtain a measurable dominating function `F n`,
   `∫⁻ F n ≤ eilenbergConstant V · ε · volume (D n)`.
3. `G k := fun t ↦ ∑' n, F n t` measurable (`ENNReal.tsum_eq_iSup_sum` plus finite sum measurability),
   A section measure dominated by countable additivity `C ∩ ball ∩ {u = t}`; by `lintegral_tsum`,
   `ENNReal.tsum_mul_left` and the `measure_iUnion` of pairwise disjoint measurable sets,
   `∫⁻ G k ≤ eilenbergConstant V · volume (closedBall 0 R) · (k+1)⁻¹`.
4. `H := fun t ↦ ⨅ k, G k t` is still measurable, still dominates the slice measure, and `∫⁻ H ≤ ∫⁻ G k` holds for each `k`;
   The right-hand side tends to `0` (`volume (closedBall 0 R) < ∞` is key, so **must** be localized to a ball first),
   By `ge_of_tendsto'` we get `∫⁻ H = 0`, and then by `lintegral_eq_zero_iff` we get `H = 0` almost everywhere.
5. Take the countable union of `R` (`Metric.iUnion_closedBall_nat`) and remove the ball: `ae_all_iff` plus
   `measure_iUnion_null`.

**No circular reasoning**: measurability is only used on the constructed dominating functions, and the measurability of the critical section function itself is never assumed.
(L3/L4) is also not used— the critical set is a closed set but not compact; the intersection within the ball is compact, but compactness is not required here.

## What was not done in this round

* **No proof of Sard**: Sharp `C^(finrank)` of `Analysis.sard` and
  `Analysis.ae_forall_fderiv_ne_zero` still carry `sorryAx`, remains a direct proof hole.
* **No proof of L8/L9/L11**: The C¹ coarea (L9) of the regular part, the weighted area of open domains (L8), and the general C¹ weighted coarea (L11) remain unchanged. L10 only handles the **critical** part, leaving the regular part to L9.
* **Weighted coarea equation remains a direct proof hole**: `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  and `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`.
  The direct proof hole remains as expected: **2/3/5, total count 10**.
* `smoothConstant_le_minkowskiConstant`,
  `smoothConstant_mul_lintegral_min_superlevel_le`, and equality of the two Cheeger constants remain unproven.
* Sharpness of the Eilenberg constant remains unproven.

## Verification

* `KLS/Geometry/CriticalSlice.lean` compiles successfully with `-DwarningAsError=true` alone.
* `build/audit/CriticalSliceAudit.lean` compiles with `-DwarningAsError=true`: 1 statements `#check`
  (The literal reproduction of the route record L10) and 7 theorem——`target`, `target_of_not_completeSpace`,
  `ae_slice_eq_regular` (L11: The form of consumption: almost every section can first discard the critical set before proceeding),
  `surfaceMeasure_real_singleton`, `constant_exceptional_level` (the measure of level sets is non-zero),
  `not_lipschitz` (`Real.exp`, `C¹` but not globally Lipschitz), a `preserved_*` named argument signature
  Check—along with 11 and `#print axioms`. All 11 statements depend only on `propext` and `Classical.choice`,
  `Quot.sound`, **no `sorryAx`**.
* Retrace `LevelSetMeasurableAudit`, `BorelSliceAudit`, `CompactSliceAudit`,
  `EilenbergMajorantAudit`, `NullSlicingAudit`, `WeightedCoareaRouteStatements`,
  `WeightedCoareaInfrastructure`, `AreaFormulaAudit`, `CheegerInfimumAudit`,
  `MinkowskiConstantAudit`, `SuperlevelSardScope`, `SmoothSardAudit`,
  `SmoothSardRouteStatements`, all strictly compiled successfully, no modifications made; `LevelSetMeasurableAudit`
  Again confirm the migration result has no `sorryAx` and the weighted coarea equation with `Analysis.sard` still carries `sorryAx`.
* Three WIP files were successfully compiled in practice, with direct proof holes respectively **2/3/5**, total **10**.
* Default `lake build` is connected to the root directory `python3 research/verify.py`. Final verification receipt is
  `build/verification/latest.json`, exactly equal to the final complete source code snapshot; evidence JSON is
  `research/explorations/2026-09-15-critical-slice.json`, final verification and save
  `build/audit/critical-final-snapshot.json`. `build/` is gitignored, hence `build/audit`
  The hash is bound solely by evidence JSON.
* Certification still **24**, perimeter infrastructure still **missing**.

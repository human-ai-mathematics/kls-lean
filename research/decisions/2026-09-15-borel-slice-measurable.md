# Borel set sections and measurable weights (L4, L5, and the statement of target T1)

2026-09-15. This round **proves the L4 and L5 weighted coarea path**, and thereby in the audit client **proves the complete statement of the first raw goal T1**—that is, the statement of the WIP direct proof hole `Analysis.aemeasurable_lintegral_levelSet`.
**No modifications were made to any WIP files**: removing this declaration from WIP was a separate decision, so the number of direct holes remains unchanged, and that hole remains a hole.
No commit, no push, no modification of historical decisions. The initial HEAD is
`2965b32bc79bdb24921c633df12102450eaedcc4`; the initial passed verification receipt is
`build/verification/20260915T024959.891644Z/report.json` (byte-for-byte identical to `build/verification/latest.json`), and the recomputed full snapshot matches the receipt: 419 files, SHA256 `812dd3511f20a8d7260ee89a56db0a2a2a2c4dff4cb21c595cba1a509b3bdff9`. The byte-for-byte comparison refers to
per-file SHA256 (including deleted items) and full snapshot structure consistency, not just the HEAD.

## Content of this round of proof

All added to the existing `formalization/FunctionalInequalities/KLS/Geometry/SurfaceSlicing.lean`,
no new modules created, no modifications to any other `.lean` file.

```lean
/-- Decomposition of inner regularity -/
theorem FunctionalInequalities.KLS.exists_isCompact_seq_volume_sdiff_eq_zero
    {S : Set V} (hS : MeasurableSet S) :
    ∃ C : ℕ → Set V, (∀ n, IsCompact (C n)) ∧ (∀ n, C n ⊆ S) ∧
      (volume : Measure V) (S \ ⋃ n, C n) = 0


/-- L4 -/
theorem FunctionalInequalities.KLS.aemeasurable_surfaceMeasure_inter_levelSet
    {u : V → ℝ} {K : ℝ≥0} {S : Set V}
    (hc : Continuous u) (hu : LipschitzOnWith K u S) (hS : MeasurableSet S) :
    AEMeasurable (fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t})) (volume : Measure ℝ)

/-- L5 -/
theorem FunctionalInequalities.KLS.aemeasurable_setLIntegral_inter_levelSet
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} {g : V → ℝ≥0∞}
    (hc : Continuous u) (hu : LipschitzOnWith K u S) (hS : MeasurableSet S)
    (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ)
```

Compared to the route record L4/L5: removed `[CompleteSpace V]` that was never used, and weakened the **global** `LipschitzWith K u` to `Continuous u` plus `LipschitzOnWith K u S` only on `S`, without introducing any additional assumptions.
`S` does not require boundedness, non-emptiness, or finite volume; `g` does not require finite values, integrability, or boundedness (allowing `g ≡ ⊤`).
Client `target_L4`, `target_L5` reproduce and prove the primitive statements with `[CompleteSpace V]` and global Lipschitz, while `target_L4_of_lipschitzOnWith`, `target_L5_of_lipschitzOnWith` prove the weakened version.

## Statement of target T1 has been proven, but the hole remains unfilled

Client `BorelSliceAudit.target_T1` verbatim repeats and proves

```lean
∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} (_ : LipschitzWith K u)
    {g : V → ℝ≥0∞} (_ : Measurable g) ,
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ)
```

This is the same as `KLS/WIP/AnalyticPrerequisites.lean`'s `Analysis.aemeasurable_lintegral_levelSet` statement (obtained by taking L5 and applying `S = univ`, then simplifying `Set.univ_inter`). **The WIP was not moved in this round**:
By the existing convention of this repository (see the superlevel exit decision in 2026-09-15), moving declarations out of WIP and connecting interfaces is a **separate round** decision. Therefore:

* Direct proof holes remain as **3/3/5**, total count **11**; `Analysis.aemeasurable_lintegral_levelSet` still carries `sorry`.
* One cannot say "the first coarea proof hole has been filled"; one can only say that **the statement has been proven on the hole-free module basis**, and can be discharged upon migration.

## Proof design

**L4 = L3 (compact set) + L2 (zero-measure remainder) + inner regularity, all three are indispensable.**

1. `exists_isCompact_seq_volume_sdiff_eq_zero`: for a measurable `S`, using the compact exhaustion of the space
   `compactCovering V m` cut `S` into finite volume pieces (Haar measure is finite on compact sets), and for each piece use
   `MeasurableSet.exists_isCompact_isClosed_sdiff_lt` extract error `< (k+1)⁻¹` from a compact subset,
   Use `Nat.unpair` to enumerate the double family as one sequence. Compact exhaustion handles infinite volume, without any finiteness assumption.
2. Let `A n := Set.accumulate C n` (a finite union, hence compact). By `measure_iUnion_eq_iSup_accumulate`
   (the lower continuity holds for sequences of sets that need not be measurable)
   `surfaceMeasure V ((⋃ n, C n) ∩ {u = t}) = ⨆ n, surfaceMeasure V (A n ∩ {u = t})`,
   Each term on the right is L3-measurable (`A n` compact, `u` continuous), so the supremum is measurable.
3. The remainder `N := S \ ⋃ n, C n` satisfies `volume N = 0` and `LipschitzOnWith K u N` (by
   (`hu.mono`), hence **L2** yields: almost every `t` has `surfaceMeasure V (N ∩ {u = t}) = 0`.
   On such a `t`, subadditivity and monotonicity squeeze `surfaceMeasure V (S ∩ {u = t})`
   `⨆ n, surfaceMeasure V (A n ∩ {u = t})`. Thus L4 holds, and the witnessing measurable function is **explicit**.

**L5 = L4 + simple function approximation, without any parameter integral theorems.**
`lintegral_eq_iSup_eapprox_lintegral` Write `∫⁻ y in S ∩ {u = t}, g` as the infimum of integrals of simple functions;
each integral of a simple function is expanded into a **finite sum** according to `SimpleFunc.lintegral`
`∑ c ∈ range, c * surfaceMeasure V ((S ∩ s ⁻¹' {c}) ∩ {u = t})`, and `S ∩ s ⁻¹' {c}` is measurable,
`u` remains Lipschitz on it, so each term is AEMeasurable by L4; the finite sum (`Finset.aemeasurable_sum`)
is preserved as AEMeasurable under countable supremum (`AEMeasurable.iSup`).

**There is no use of the parameter integral theorem requiring `SFinite`.** Route records indicate that
`Measurable.lintegral_prod_right'` requires the inner measure `SFinite`, while the (n-1)-dimensional Hausdorff measure in a positive-dimensional ambient space fails to satisfy this; the current argument completely bypasses it, relying only on finite sums over levels and monotone limits.

**No circular reasoning.** The witness function for L4 is constructed from a sequence of compact subsets, its measurability comes from L3, not assumed;
L2 is only used on the remainder of volume zero.

## What was not done in this round

* **No modification to WIP**, so `Analysis.aemeasurable_lintegral_levelSet` remains a direct proof hole,
  the direct proof hole count remains 11 (3/3/5). Migration and interface connection are decided separately in the next round.
* **The weighted coarea formula itself (L6–L12 and target T2/T3) remains unchanged**:
  `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` and
  `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` remain direct proof holes.
  L4/L5 only provides measurability, **no equation is given**.
* The sharpness of `C^(finrank)`'s `Analysis.sard` (with no downstream consumers) and
  `Analysis.ae_forall_fderiv_ne_zero` still carries `sorryAx`.
* `smoothConstant_le_minkowskiConstant`,
  `smoothConstant_mul_lintegral_min_superlevel_le`, and the equality of the two Cheeger constants remain unproven.
* The sharpness of the Eilenberg constant remains unproven.
* Neither the Whitney extension and C¹ piecewise for L6/L6a/L7 nor L8–L11 have been addressed.

## Verification

* `KLS/Geometry/SurfaceSlicing.lean` compiles successfully with `-DwarningAsError=true` alone.
* `build/audit/BorelSliceAudit.lean` compiles successfully with `-DwarningAsError=true`: 3 statements `#check`
  (verbatim reproduction of the route record's L4, L5, and target T1) and 12 theorems—`target_L4`, `target_L5`, `target_T1`, two weakened assumption versions, `eilenberg_borel` (merged form of L1 + L4), `weighted_one` (L5 returning to L4 at weight `1`), `infinite_volume` (measurable sets unbounded and of infinite volume), `top_weight` (`g ≡ ⊤`), three `preserved_*` named-argument signature checks—and 15 `#print axioms`.
  All 15 declarations only depend on `propext`, `Classical.choice`, `Quot.sound`, **no `sorryAx`**.
* Re-running `CompactSliceAudit`, `EilenbergMajorantAudit`, `NullSlicingAudit` (first three client rounds, unmodified), `WeightedCoareaRouteStatements`, `WeightedCoareaInfrastructure`, `AreaFormulaAudit`, `CheegerInfimumAudit`, `MinkowskiConstantAudit`, `SuperlevelSardScope`, `SmoothSardAudit`, `SmoothSardRouteStatements` all compile strictly successfully; their `preserved_*` are again confirmed via named arguments to remain unchanged from the first three rounds.
* Three WIP files compile successfully in practice, with direct proof holes respectively **3/3/5, total count 11**.
* Default `lake build` and root directory `python3 research/verify.py` pass. Final verification receipt is
  `build/verification/latest.json`, identical to the final full source snapshot; evidence JSON is
  `research/explorations/2026-09-15-borel-slice-measurable.json`, final reconciliation saved separately
  `build/audit/borelslice-final-snapshot.json`. `build/` is gitignored, so the hash of `build/audit` is bound solely by the evidence JSON.
* The certificate remains **24**, perimeter infrastructure remains **missing** (gap list updated this round:
  L1–L5 all marked as proven, and the statement for T1 proven while WIP holes remain unfilled).

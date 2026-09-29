# Eilenberg Measurable Upper Bound (with a Constant in L1)

2026-09-15. This round **proves the L1 bound for the weighted coarea route**: the Hausdorff measure of Lipschitz level sections has a measurable dominating function, whose Lebesgue integral is controlled by `C · K · volume S`, with a positive, explicit constant. The previous L2 case becomes its zero-measure special instance. No commit, no push, no alteration of historical decisions. The starting HEAD is
`2965b32bc79bdb24921c633df12102450eaedcc4`; the starting verification receipt is
`build/verification/20260914T211119.924157Z/report.json` (bit-for-bit identical to `build/verification/latest.json`), and the recomputed full snapshot matches the receipt: 414 files, SHA256 `ca32490215e2f001aadbd83b7d18110d74ef39b971c12818a91b635e2b40ec18`. The bit-for-bit comparison here refers to consistent file-level SHA256 (including deleted items) and full snapshot structure, not merely the HEAD.

## Content of this round of proof

### `Analysis/HausdorffSlicing.lean` (only relying on Mathlib, any `EMetricSpace`)

```lean
theorem FunctionalInequalities.Analysis.exists_measurable_majorant
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {u : X → ℝ} {K : ℝ≥0} {S : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u S) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, μH[d] (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ 2 * (K : ℝ≥0∞) * μH[d + 1] S
```

This is the Eilenberg inequality under the diameter convention of Mathlib, with constant `2`, **no dimension, no vector space structure, no `volume`**. Two new auxiliary lemmas:

```lean
theorem FunctionalInequalities.Analysis.exists_measurable_majorant_of_eqOn
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {u : Y → ℝ} {S : Set Y}
    (h : ∀ x ∈ S, ∀ y ∈ S, u x = u y) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧ (∀ t, μ (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) = 0

theorem FunctionalInequalities.Analysis.exists_cover_cost_lt
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} {S : Set X} {r c : ℝ≥0∞} (hr : 0 < r) (hc : μH[d] S < c) :
    ∃ T : ℕ → Set X, S ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧
      ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d < c
```

### `KLS/Geometry/SurfaceSlicing.lean` (Normalization packaging, constant explicit)

```lean
def FunctionalInequalities.KLS.eilenbergConstant (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] : ℝ≥0 :=
  Real.toNNReal (4 * unitBallVolume (Module.finrank ℝ V - 1) / unitBallVolume (Module.finrank ℝ V))

theorem FunctionalInequalities.KLS.coe_eilenbergConstant : (eilenbergConstant V : ℝ≥0∞) = …  -- rfl
theorem FunctionalInequalities.KLS.eilenbergConstant_pos : 0 < eilenbergConstant V

theorem FunctionalInequalities.KLS.exists_measurable_majorant
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} (hu : LipschitzOnWith K u S) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ))
        ≤ (eilenbergConstant V : ℝ≥0∞) * (K : ℝ≥0∞) * volume S
```

The constant `4 ω_{n-1} / ω_n` is the result of normalizing the Mathlib constant `2` first by fiber measure and then by ambient measure `ω_{n-1}/2^{n-1}` and `2^n/ω_n`, respectively. **No sharpness claimed**. The audit client computes it as a concrete number:
`eilenbergConstant ℝ = 2` (`4·ω₀/ω₁ = 4/2`, using `Γ(3/2) = √π/2`),
`eilenbergConstant (EuclideanSpace ℝ (Fin 0)) = 4`.

Compared to the L1 record of the route: `∃ C : ℝ≥0, 0 < C ∧ …` given by `eilenbergConstant` and `eilenbergConstant_pos`,
and **removing** `[CompleteSpace V]` (never used) and `[Nontrivial V]` (treated separately in dimension zero, see below),
no additional assumptions are introduced. The client's `target` is proven by verbatim reproduction and proof using the primitive with `[CompleteSpace V]` and `[Nontrivial V]`, and `target_of_trivial` proves the version without `[Nontrivial V]`.

## Proof design

With the same covering skeleton as the previous round, only replacing "total coverage cost tends to zero" with "total coverage cost approaches `μH[d+1] S`":
`Measure.mono_pre` says each scale's infimum is `≤ μH[d+1] S`, so by `exists_cover_cost_lt` a coverage with cost `< μH[d+1] S + (k+1)⁻¹` is attained at scale `(k+1)⁻¹`. The pointwise bound of the horizontal interval, the measurable dominating function, the sub-type index's `hausdorffMeasure_le_liminf_tsum`, the `lintegral_tsum` and `lintegral_indicator_const` integral bounds, and the Fatou lemma remain invariant; the limit is given by `Tendsto (fun k ↦ 2K(μH[d+1] S + (k+1)⁻¹)) → 2K·μH[d+1] S`.

**Degenerate cases use explicit branching, not exclusion.**

* `K = 0`: `u` is constant on `S`, and `exists_measurable_majorant_of_eqOn` provides concentration on a single level.
  `∞` dominating function, integral is `⊤ · 0 = 0`, exactly the value required on the right-hand side at this time. This simultaneously resolves
  The case of `μH[d+1] S = ⊤` and `K = 0`—there the covering argument simply cannot achieve finite cost coverings.
* `μH[d+1] S = ⊤` and `K ≠ 0`: the right-hand side is `⊤`, take `F ≡ ⊤`.
`d = 0`: Still only sums over blocks containing `t` (sub-type index), otherwise empty blocks will contribute `0^(0:ℝ) = 1`.
* 0-dimensional (KLS layer): natural number subtraction gives `surfaceMeasure V = hausdorffNormalized V 0`, the space is
  `Subsingleton`, so `u` is constant on `S`, along the same `exists_measurable_majorant_of_eqOn`
  Close out with `μ = surfaceMeasure V`. There is **no** treatment of the zero-dimensional `ℋ⁰` as having zero measure;
  The previous client has already computed `surfaceMeasure (EuclideanSpace ℝ (Fin 0)) univ = 1`.
* Positive dimension (KLS layer): `((n-1 : ℕ) : ℝ) + 1 = (n : ℝ)` requires `1 ≤ n`, so the dimension branching is necessary.

**No circular argument.** Measurability still holds only for **constructively obtained** dominating functions, and never assumes the section functions.
`fun t ↦ surfaceMeasure V (S ∩ {u = t})` measurable. The measurability of the cross sections of L3–L5 has not been proven.

## L2 and the handling of the previous statement

`ae_hausdorffMeasure_inter_levelSet_eq_zero` and
`KLS.ae_surfaceMeasure_inter_levelSet_eq_zero` statement literally unchanged, proof changed to a consequence of L1
(right-hand side is `2K·0 = 0`, dominating function is measurable, `lintegral_eq_zero_iff` applies).
`exists_cover_of_hausdorffMeasure_eq_zero` statement literally unchanged, changed to a consequence of `exists_cover_cost_lt`.
`exists_levelSlab` statement literally unchanged.

These four are checked by the client machine: `preserved_*` The four theorems verbatim reproduce the statements from the previous round's decision record and invoke library declarations using **named arguments** (`(u := u) (K := K) (N := N) (d := d)`), so renaming bound variables or changing the order of assumptions would cause a compilation failure here. During rewriting, we indeed once wrote `exists_levelSlab`'s `N` as `S`, and it was precisely this check that reported `Invalid argument name N`, after which it was corrected back to `N`, with no signature change remaining.

## What was not done in this round

* **Section measurability bridging of L3–L5** remains unproven: Borel measurability of fiber compact sets (L3, including open cover content of
  Scale limit and connection to `mkMetric'`, Borel set fiber a.e. measurability (L4), version with measurable weights (L5).
* **Three original coarea holes** unchanged: `Analysis.aemeasurable_lintegral_levelSet`,[, ]
  `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`,
  `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`.
* Sharp `C^(finrank)` `Analysis.sard` (now without downstream consumers) and
  `Analysis.ae_forall_fderiv_ne_zero` still carries `sorryAx`.
* `smoothConstant_le_minkowskiConstant`,
  `smoothConstant_mul_lintegral_min_superlevel_le`, two Cheeger constants being equal has not been proven.
Constants do not claim sharpness; no proof `C = 1` or lower bound is given.
* Whitney's extension touching neither L6/L6a/L7 nor C¹ piecewise, nor L8–L12.
* L1 does not fill any existing coarea holes: direct proof holes remain as 3/3/5, total count 11.

## Verification

* Both library modules are compiled separately and pass `-DwarningAsError=true`.
* `build/audit/EilenbergMajorantAudit.lean` compiles successfully with `-DwarningAsError=true`:
  1 statements `#check` (verbatim reproduction of the L1 route record) and 12 theorems—`target` (the original statement with `[CompleteSpace V]` and `[Nontrivial V]`), `target_of_trivial`, 6 independent consumers
  (`null_slicing` independently rederived from L1 to L2, `ae_ne_top` i.e. `volume S` finite measure on each section almost surely (a conclusion not provided by L2), `constant_on_set` i.e. `K = 0` forces the integral to zero, `univ_without_finiteness` i.e. `S = univ` with no finite assumption, `eilenbergConstant_real = 2`, `eilenbergConstant_euclidean_zero = 4`, 4 statements `preserved_*` with named argument signature checks—and 23 statements `#print axioms` (11 library declarations + 12 client declarations).
  All 23 declarations only depend on `propext`, `Classical.choice`, `Quot.sound`, **without `sorryAx`**.
* Re-running `NullSlicingAudit` (previous client, unmodified), `WeightedCoareaRouteStatements`, `WeightedCoareaInfrastructure`, `AreaFormulaAudit`, `CheegerInfimumAudit`, `MinkowskiConstantAudit`, `SuperlevelSardScope`, `SmoothSardAudit`, `SmoothSardRouteStatements` all compile strictly successfully.
* Three WIP files compile successfully in practice, with direct proof holes respectively **3/3/5, total 11**.
* Default `lake build` and root directory `python3 research/verify.py` pass. Final verification receipt is `build/verification/latest.json`, identical to the final full source snapshot; evidence JSON is `research/explorations/2026-09-15-eilenberg-majorant.json`, and final reconciliation is saved separately as `build/audit/eilenberg-final-snapshot.json`. `build/` is gitignored, so the hash of `build/audit` is bound solely by the evidence JSON.
* The certificate remains **24**, perimeter infrastructure remains **missing** (gap list updated in this round: L1 and L2 are now proven, L3–L5 remain listed as gaps).

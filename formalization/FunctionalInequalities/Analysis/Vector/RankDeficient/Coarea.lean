import FunctionalInequalities.Analysis.Vector.RankDeficient.StratumSlicing

/-! # The rank-deficient critical set, and the codimension-`m` coarea formula

Critical-set localization gives almost-everywhere nullity of rank-deficient fibres and the codimension-`m` coarea formula without a critical-set hypothesis.

**What this closes.**  `Analysis/Vector/Coarea/Regular.lean` proved the coarea formula where the
differential is surjective, and `Analysis/Vector/Slice/Critical.lean` extended it under the hypothesis
that the derivative *vanishes* wherever it fails to be surjective — a genuine restriction for
`m ≥ 2`, exhibited there by a rank-one map of the plane.  `coarea_of_contDiff` below removes that
hypothesis entirely.

**What it is not.**  It is **not a Sard theorem**: nothing whatever is claimed about the measure of
the set of critical *values*, which for a merely `C¹` map may well be positive.  The map is assumed
`C¹`, not Lipschitz.  The fibre measure is the normalized Hausdorff measure of the complementary
dimension, in the repository's standing convention.

**The route, in one paragraph.**  Rank stratification decomposes the critical set by the exact rank of the
differential into finitely many measurable layers.  On a layer, The kernel identity says the differential dies
along the fibres of the regular component `P ∘ u`, a locally uniform right-inverse bound makes this quantitative, and small tangential Lipschitz control turns the two into a small tangential Lipschitz constant.
fibrewise slicing then runs the approximating partition on `u` itself and applies the Eilenberg bound **inside a
fibre**, where `k + (m − r) = n − r` is the right exponent, integrating against the proved regular
coarea formula; that gives the layer's nullity near each of its points.  critical-set localization here patches those
neighbourhoods together by second countability, the finite union over `r < m` gives critical-fibre nullity, and the
critical part of the coarea equality then vanishes on both sides, giving vector coarea.
-/

noncomputable section
open MeasureTheory Module Set Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **critical-set localization: a local null-slicing statement patches to a global one.**  `V` is second countable, so
the neighbourhood family has a countable subcover and the almost-everywhere quantifier survives the
countable intersection.  No regularity of `u` and no measurability of `A` is used. -/
theorem ae_hausdorffMeasure_inter_levelSet_eq_zero_of_local {u : V → W} {A : Set V} {k : ℕ}
    (h : ∀ x₀ ∈ A, ∃ U ∈ nhds x₀, ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] (A ∩ U ∩ {x : V | u x = t}) = 0) :
    ∀ᵐ t ∂(volume : Measure W), μH[(k : ℝ)] (A ∩ {x : V | u x = t}) = 0 := by
  classical
  rcases Set.eq_empty_or_nonempty A with hAe | ⟨z₀, hz₀⟩
  · simp [hAe]
  have hopen : ∀ z : A, ∃ N : Set V, IsOpen N ∧ (z : V) ∈ N ∧
      ∀ᵐ t ∂(volume : Measure W), μH[(k : ℝ)] (A ∩ N ∩ {x : V | u x = t}) = 0 := by
    intro z
    obtain ⟨U, hU, hUae⟩ := h z z.2
    obtain ⟨N, hNU, hNopen, hzN⟩ := mem_nhds_iff.1 hU
    refine ⟨N, hNopen, hzN, ?_⟩
    filter_upwards [hUae] with t ht
    refine le_antisymm ?_ (by simp)
    calc μH[(k : ℝ)] (A ∩ N ∩ {x : V | u x = t})
        ≤ μH[(k : ℝ)] (A ∩ U ∩ {x : V | u x = t}) :=
          measure_mono (fun x hx => ⟨⟨hx.1.1, hNU hx.1.2⟩, hx.2⟩)
      _ = 0 := ht
  choose N hNopen hzN hNae using hopen
  obtain ⟨T, hTc, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable N hNopen
  have hTne : T.Nonempty := by
    have hz : z₀ ∈ ⋃ z ∈ T, N z := by
      rw [hTu]; exact Set.mem_iUnion.2 ⟨⟨z₀, hz₀⟩, hzN _⟩
    obtain ⟨z, hzT, -⟩ := Set.mem_iUnion₂.1 hz
    exact ⟨z, hzT⟩
  obtain ⟨σ, hσ⟩ := hTc.exists_eq_range hTne
  have hcov : A ⊆ ⋃ n, N (σ n) := by
    intro x hx
    have hx' : x ∈ ⋃ z : A, N z := Set.mem_iUnion.2 ⟨⟨x, hx⟩, hzN _⟩
    rw [← hTu] at hx'
    obtain ⟨z, hzT, hxz⟩ := Set.mem_iUnion₂.1 hx'
    rw [hσ] at hzT
    obtain ⟨n, rfl⟩ := hzT
    exact Set.mem_iUnion.2 ⟨n, hxz⟩
  filter_upwards [(ae_all_iff (ι := ℕ)).2 fun n => hNae (σ n)] with t ht
  refine le_antisymm ?_ (by simp)
  have hsub : A ∩ {x : V | u x = t} ⊆ ⋃ n, A ∩ N (σ n) ∩ {x : V | u x = t} := by
    rintro x ⟨hxA, hxt⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hcov hxA)
    exact Set.mem_iUnion.2 ⟨n, ⟨hxA, hn⟩, hxt⟩
  calc μH[(k : ℝ)] (A ∩ {x : V | u x = t})
      ≤ μH[(k : ℝ)] (⋃ n, A ∩ N (σ n) ∩ {x : V | u x = t}) := measure_mono hsub
    _ ≤ ∑' n, μH[(k : ℝ)] (A ∩ N (σ n) ∩ {x : V | u x = t}) := measure_iUnion_le _
    _ = 0 := by simp [ht]

/-- Each rank stratum is globally null in almost every level. -/
theorem ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero {u : V → W} (hu : ContDiff ℝ 1 u)
    {k r : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) (hr : r < finrank ℝ W) :
    ∀ᵐ t ∂(volume : Measure W), μH[(k : ℝ)] (stratum u r ∩ {x : V | u x = t}) = 0 :=
  ae_hausdorffMeasure_inter_levelSet_eq_zero_of_local
    fun _x₀ hx₀ => exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero hu hk hr hx₀

/-- **critical-fibre nullity: the critical set of a `C¹` map is `ℋ^k`-null in almost every level.**  This is the
target of the rank-deficient route, and it covers the **whole** critical set
`{x | fderiv ℝ u x` is not surjective`}`, not merely the part where the derivative vanishes.

No positivity of the codimension is needed: with a zero-dimensional target every linear map is
surjective, the critical set is empty and the statement is vacuous rather than false.

**This is not a Sard theorem**: nothing is claimed about the measure of the set of critical
*values*. -/
theorem ae_hausdorffMeasure_critical_inter_levelSet_eq_zero {u : V → W} (hu : ContDiff ℝ 1 u)
    {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) :
    ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] ({x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t}) = 0 := by
  have hall : ∀ᵐ t ∂(volume : Measure W), ∀ r ∈ Finset.range (finrank ℝ W),
      μH[(k : ℝ)] (stratum u r ∩ {x : V | u x = t}) = 0 := by
    rw [Filter.eventually_all_finset]
    intro r hr
    exact ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero hu hk (Finset.mem_range.1 hr)
  filter_upwards [hall] with t ht
  refine le_antisymm ?_ (by simp)
  rw [setOf_not_surjective_fderiv_eq_iUnion u, Set.iUnion₂_inter]
  calc μH[(k : ℝ)] (⋃ r ∈ Finset.range (finrank ℝ W), stratum u r ∩ {x : V | u x = t})
      ≤ ∑ r ∈ Finset.range (finrank ℝ W), μH[(k : ℝ)] (stratum u r ∩ {x : V | u x = t}) :=
        measure_biUnion_finset_le _ _
    _ = 0 := by
        refine Finset.sum_eq_zero fun r hr => ht r hr

/-- The normalized form of critical-fibre nullity, which the coarea layer consumes. -/
theorem ae_hausdorffNormalized_critical_inter_levelSet_eq_zero {u : V → W} (hu : ContDiff ℝ 1 u)
    {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) :
    ∀ᵐ t ∂(volume : Measure W),
      KLS.hausdorffNormalized V k
        ({x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t}) = 0 := by
  filter_upwards [ae_hausdorffMeasure_critical_inter_levelSet_eq_zero hu hk] with t ht
  exact (hausdorffNormalized_eq_zero_iff (V := V) k _).2 ht

/-- **vector coarea: the codimension-`m` coarea formula for `C¹` maps, with no hypothesis on the critical
set.**  `Analysis/Vector/Slice/Critical.lean` proved this under the extra assumption that the
derivative vanishes wherever it fails to be surjective, which for `m ≥ 2` is a genuine restriction;
critical-fibre nullity removes it.

No finiteness, boundedness, integrability or regular-value hypothesis is used, `S` is an arbitrary
Borel set, `g` an arbitrary measurable `ℝ≥0∞` weight, and no positivity of the codimension is
required.  **It is not a Sard theorem.** -/
theorem coarea_of_contDiff {S : Set V} {u : V → W} {g : V → ℝ≥0∞} {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hu : ContDiff ℝ 1 u)
    (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) ∧
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
          ∂(volume : Measure W)) := by
  apply coarea_of_contDiff_of_ae_null_critical hk hu hS hg
  simpa only [coareaJacobian_eq_zero_iff, ContinuousLinearMap.coe_coe] using
    ae_hausdorffNormalized_critical_inter_levelSet_eq_zero hu hk
end FunctionalInequalities.Analysis

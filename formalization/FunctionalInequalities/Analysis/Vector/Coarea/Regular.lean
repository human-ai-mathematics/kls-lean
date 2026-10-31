module

public import FunctionalInequalities.Analysis.MeasurableCover
public import FunctionalInequalities.Analysis.Vector.Coarea.Local

/-! # Weighted slice measurability in codimension `m`, and the regular coarea formula

The assembly of the local coarea equality into a statement about a whole regular open set needs one
more ingredient: the level function `t ↦ ∫⁻ over S ∩ {u = t}` must be measurable, since the
patching exchanges a countable sum with the outer integral and `lintegral_tsum` needs measurability.

Local chart slice integrals are Tonelli sections on the parameter–level product.
`Vector/Coarea/Local.lean` owns their measurability and the local equality; the subordinate
measurable partition assembles them on regular open sets here. This argument uses no
Eilenberg inequality. The general codimension Eilenberg majorant is separately available in
`Vector/Slice/Hausdorff.lean`.

`coarea_of_contDiffOn_of_coareaJacobian_ne_zero` includes measurable weighted slices on the
regular open set. `coarea_of_contDiff_of_ae_null_critical` extends it when actual almost-everywhere
null critical fibres are supplied. Their rank-deficient and zero-derivative producers remain
separate in `Vector/RankDeficient/Coarea.lean` and `Vector/Slice/Critical.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

variable {H K V W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/--
**The codimension-`m` regular coarea formula.**  On an open set where the differential of `u` is
everywhere surjective, for every Borel `S ⊆ O` and every measurable `ℝ≥0∞` weight, the level
function is measurable and the coarea equality holds, with the normalized Hausdorff measure of the
codimension as the fibre measure.

This is the analogue of the scalar regular-domain coarea,
`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`; the level
function is even **measurable**, not merely almost everywhere measurable.

No finiteness, boundedness, integrability, regular-value or `SFinite` hypothesis is used, and no
regularity of `u` outside `O`.  **Nothing is claimed about the critical set**: surjectivity of the
differential is assumed at every point of `O`. -/
theorem coarea_of_contDiffOn_of_coareaJacobian_ne_zero {O S : Set V} {u : V → W} {g : V → ℝ≥0∞}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    (hreg : ∀ x ∈ O, coareaJacobian (fderiv ℝ u x) ≠ 0) (hS : MeasurableSet S) (hSO : S ⊆ O)
    (hg : Measurable g) :
    Measurable
        (fun t : W =>
          ∫⁻ y in S ∩ {x : V | u x = t},
            g y ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W))) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V) =
        ∫⁻ t,
          ∫⁻ y in S ∩ {x : V | u x = t},
            g
              y ∂(KLS.hausdorffNormalized V
              (finrank ℝ V - finrank ℝ W)) ∂(volume : Measure W)) := by
  classical
  set ν : Measure V := KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W) with hν
  rcases S.eq_empty_or_nonempty with hSe | ⟨z₀, hz₀⟩
  · subst hSe
    simp
  choose N hN hxN hNO hformula using fun z : O =>
    exists_vector_coarea_neighborhood_measurable hO hu z.2 (hreg z z.2)
  obtain ⟨σ, Q, hQm, hQd, hQu, hQn⟩ :=
    exists_measurable_partition_subordinate hS hSO ⟨z₀, hz₀⟩ N hN hxN hNO
  have hQO : ∀ n, Q n ⊆ O := fun n => (hQn n).trans (hNO (σ n))
  have hslicem : ∀ n t, MeasurableSet (Q n ∩ {x : V | u x = t}) := by
    have hw : Measurable (O.piecewise u (fun _ => (0 : W))) :=
      hu.continuousOn.measurable_piecewise continuous_const.continuousOn hO.measurableSet
    intro n t
    have heq :
      Q n ∩ {x : V | u x = t} = Q n ∩ {x : V | O.piecewise u (fun _ => (0 : W)) x = t} := by
      ext x
      constructor <;> rintro ⟨hx, ht⟩ <;> exact ⟨hx, by simpa [hQO n hx] using ht⟩
    rw [heq]
    exact (hQm n).inter (hw (measurableSet_singleton t))
  have hmeas : ∀ n, Measurable (fun t : W => ∫⁻ y in Q n ∩ {x : V | u x = t}, g y ∂ν) :=
    fun n => (hformula (σ n) (Q n) (hQm n) (hQn n) g hg).1
  have hsum :
    ∀ t : W,
      (∫⁻ y in S ∩ {x : V | u x = t}, g y ∂ν) = ∑' n, ∫⁻ y in Q n ∩ {x : V | u x = t}, g y ∂ν := by
    intro t
    rw [← hQu, Set.iUnion_inter]
    exact
      lintegral_iUnion (fun n => hslicem n t)
        (fun i j hij => (hQd hij).mono Set.inter_subset_left Set.inter_subset_left) g
  refine ⟨?_, ?_⟩
  · simp_rw [hsum]
    exact Measurable.tsum hmeas
  · calc
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)) =
          ∑' n,
            ∫⁻ x in Q n,
              ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V) := by
        rw [← hQu]
        exact lintegral_iUnion hQm hQd _
      _ = ∑' n, ∫⁻ t, ∫⁻ y in Q n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) :=
        tsum_congr fun n => (hformula (σ n) (Q n) (hQm n) (hQn n) g hg).2
      _ = ∫⁻ t, ∑' n, ∫⁻ y in Q n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) :=
        (lintegral_tsum fun n => (hmeas n).aemeasurable).symm
      _ = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) := by simp_rw [hsum]

/-- Regular coarea extends over AE-null critical fibres. The nullity is an
explicit input, independently of the theorem used to establish it. -/
theorem coarea_of_contDiff_of_ae_null_critical {S : Set V} {u : V → W} {g : V → ℝ≥0∞}
    {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) (hu : ContDiff ℝ 1 u)
    (hS : MeasurableSet S) (hg : Measurable g)
    (hnull : ∀ᵐ t ∂(volume : Measure W),
      (KLS.hausdorffNormalized V k) ({x | coareaJacobian (fderiv ℝ u x) = 0} ∩
        {x : V | u x = t}) = 0) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y
      ∂(KLS.hausdorffNormalized V k)) (volume : Measure W) ∧
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
        ∂(volume : Measure W) := by
  let ν : Measure V := KLS.hausdorffNormalized V k
  let R : Set V := {x : V | coareaJacobian (fderiv ℝ u x) ≠ 0}
  have hRopen : IsOpen R :=
    isOpen_ne_fun (continuous_coareaJacobian.comp (hu.continuous_fderiv one_ne_zero))
      continuous_const
  have hkdim : k = finrank ℝ V - finrank ℝ W := by omega
  obtain ⟨hm, heq⟩ := coarea_of_contDiffOn_of_coareaJacobian_ne_zero (O := R) (S := S ∩ R)
    hRopen hu.contDiffOn (fun _ hx => hx) (hS.inter hRopen.measurableSet) Set.inter_subset_right hg
  rw [← hkdim] at hm heq
  have hfibre : ∀ᵐ t ∂(volume : Measure W),
      (∫⁻ y in S ∩ {x : V | u x = t}, g y ∂ν) =
        ∫⁻ y in (S ∩ R) ∩ {x : V | u x = t}, g y ∂ν := by
    filter_upwards [hnull] with t ht
    apply setLIntegral_congr
    apply MeasureTheory.ae_eq_set.2
    constructor
    · refine measure_mono_null ?_ ht
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨by by_contra h; exact hx.2 ⟨⟨hx.1.1, h⟩, hx.1.2⟩, hx.1.2⟩
    · have hempty : ((S ∩ R) ∩ {x : V | u x = t}) \ (S ∩ {x : V | u x = t}) = ∅ := by
        ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_empty_iff_false]; tauto
      rw [hempty]; simp
  refine ⟨hm.aemeasurable.congr (Filter.EventuallyEq.symm hfibre), ?_⟩
  have hambient : (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
      ∂(volume : Measure V)) =
      ∫⁻ x in S ∩ R, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
        ∂(volume : Measure V) := by
    rw [← lintegral_inter_add_sdiff _ _ hRopen.measurableSet]
    have hz : (∫⁻ x in S \ R, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
        ∂(volume : Measure V)) = 0 := by
      refine setLIntegral_eq_zero (hS.diff hRopen.measurableSet) fun x hx => ?_
      have h0 : coareaJacobian (fderiv ℝ u x) = 0 := by simpa [R] using hx.2
      simp [h0]
    rw [hz, add_zero]
  exact hambient.trans (heq.trans (lintegral_congr_ae (Filter.EventuallyEq.symm hfibre)))

end FunctionalInequalities.Analysis

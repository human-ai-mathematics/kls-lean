import FunctionalInequalities.Analysis.Vector.LocalCoarea

/-! # Weighted slice measurability in codimension `m`, and the regular coarea formula

The assembly of the local coarea equality into a statement about a whole regular open set needs one
more ingredient: the level function `t ↦ ∫⁻ over S ∩ {u = t}` must be measurable, since the
patching exchanges a countable sum with the outer integral and `lintegral_tsum` needs measurability.

**The route taken here is not the scalar one.**  In codimension one the repository proves slice
measurability for an arbitrary Borel `S` inside an open `C¹` domain **with no regular-point
hypothesis**, through the Eilenberg slicing inequality of `KLS/Geometry/SurfaceSlicing.lean`.  The
codimension-`m` Eilenberg inequality is **not** available here, so this module proves the statement
only where the differential is surjective, and proves it **directly from the chart**: on a chart the
slice integral is a Tonelli section of one measurable function on the parameter–level product, so
its measurability is immediate and no slicing inequality is used.

That is enough for the regular case, and `coarea_of_contDiffOn_of_coareaJacobian_ne_zero` assembles
it: the **codimension-`m` regular coarea formula**, the analogue of the scalar `L9`
`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`, with weighted slice measurability included.

**What is still open**: slice measurability **without** the regularity hypothesis, which in
codimension one is what lets the critical part be treated at all; the critical set, sharp
finite-regularity Sard, and everything beyond the regular case.
-/

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

omit [MeasurableSpace K] [BorelSpace K] in
/-- **Weighted slices of a chart piece are measurable in the level.**  On a level-graph family the
slice integral is the Tonelli section of a single measurable function on the parameter–level
product, so its measurability in the level needs no slicing inequality. -/
theorem measurable_setLIntegral_inter_levelSet_levelGraphFamily {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hsp : IsVectorGraphSplitting ι κ) {u : V → W} {Ω : Set (H × W)} {ψ : H × W → K}
    (hψ : ContDiff ℝ 1 ψ) (hlevel : ∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2)
    {A : Set (H × W)} (hA : MeasurableSet A) (hAΩ : A ⊆ Ω)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun t : W =>
      ∫⁻ x in ((fun p : H × W => ι p.1 + κ (ψ p)) '' A) ∩ {x : V | u x = t}, g x
        ∂(KLS.hausdorffNormalized V (finrank ℝ H))) := by
  have hcont : Continuous (fun p : H × W => ι p.1 + κ (ψ p)) :=
    (ι.continuous.comp continuous_fst).add (κ.continuous.comp hψ.continuous)
  set F : H × W → ℝ≥0∞ := fun p => ENNReal.ofReal (LinearMap.normDet
      ((graphMapLinear ι κ (fderiv ℝ (fun y => ψ (y, p.2)) p.1) : H →ₗ[ℝ] V)))
      * g (ι p.1 + κ (ψ p)) with hF
  have hFmeas : Measurable F :=
    (continuous_normDet_graphMapLinear_fderiv_fst ι κ hψ).measurable.ennreal_ofReal.mul
      (hg.comp hcont.measurable)
  have hkey : ∀ t : W,
      (∫⁻ x in ((fun p : H × W => ι p.1 + κ (ψ p)) '' A) ∩ {x : V | u x = t}, g x
          ∂(KLS.hausdorffNormalized V (finrank ℝ H)))
        = ∫⁻ y, (A.indicator F) (y, t) ∂(volume : Measure H) := by
    intro t
    have hAt : MeasurableSet {y : H | (y, t) ∈ A} :=
      hA.preimage (measurable_id.prodMk measurable_const)
    have hγ : ContDiff ℝ 1 (fun y => ψ (y, t)) := hψ.comp (contDiff_id.prodMk contDiff_const)
    have hslice := slice_eq_image_vectorGraphMap (ι := ι) (κ := κ) (u := u) (Ω := A) (ψ := ψ)
      (N := (fun p : H × W => ι p.1 + κ (ψ p)) '' A) rfl (fun p hp => hlevel p (hAΩ hp)) t
    rw [hslice, setLIntegral_image_vectorGraphMap ι κ hsp.perp hγ hAt hg,
      ← lintegral_indicator hAt]
    refine lintegral_congr fun y => ?_
    by_cases hy : (y, t) ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ {y : H | (y, t) ∈ A} from hy)]
      rfl
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (show y ∉ {y : H | (y, t) ∈ A} from hy)]
  simp_rw [hkey]
  exact (hFmeas.indicator hA).lintegral_prod_left'

/-- **Local regular coarea with slice measurability.**  The neighbourhood of
`exists_vector_coarea_neighborhood`, carrying in addition the measurability of the level function,
which the patching needs.  Both conclusions hold for every Borel subset and every measurable
weight. -/
theorem exists_vector_coarea_neighborhood_measurable {u : V → W} {O : Set V} (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O)
    (hreg : coareaJacobian (fderiv ℝ u x₀) ≠ 0) :
    ∃ N : Set V, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      ∀ S : Set V, MeasurableSet S → S ⊆ N → ∀ g : V → ℝ≥0∞, Measurable g →
        Measurable (fun t : W => ∫⁻ x in S ∩ {x : V | u x = t}, g x
            ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W))) ∧
        (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ x in S ∩ {x : V | u x = t}, g x
              ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W))
              ∂(volume : Measure W)) := by
  obtain ⟨P, Ω, ψ, N, hsp, hdim, hΩ, hψ, hN, hxN, hNO, hlevel, himg, hinj⟩ :=
    exists_levelGraphFamily_of_coareaJacobian_ne_zero hO hu hx₀ hreg
  set Ψ : P × W → V := fun p => P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p) with hΨ
  have hcont : Continuous Ψ :=
    ((P.subtypeₗᵢ).continuous.comp continuous_fst).add
      (((Pᗮ).subtypeₗᵢ).continuous.comp hψ.continuous)
  have hmem : ∀ p ∈ Ω, Ψ p ∈ O := fun p hp => hNO (himg ▸ ⟨p, hp, rfl⟩)
  have hPdim : finrank ℝ P = finrank ℝ V - finrank ℝ W := by
    have h1 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := V) P
    omega
  refine ⟨N, hN, hxN, hNO, fun S hS hSN g hg => ?_⟩
  set A : Set (P × W) := Ω ∩ Ψ ⁻¹' S with hA
  have hAmeas : MeasurableSet A := hΩ.measurableSet.inter (hS.preimage hcont.measurable)
  have hAΩ : A ⊆ Ω := Set.inter_subset_left
  have hAimg : Ψ '' A = S := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact hp.2
    · intro x hx
      obtain ⟨p, hp, hpx⟩ : x ∈ Ψ '' Ω := by rw [himg]; exact hSN hx
      exact ⟨p, ⟨hp, by show Ψ p ∈ S; rw [hpx]; exact hx⟩, hpx⟩
  constructor
  · have h := measurable_setLIntegral_inter_levelSet_levelGraphFamily hsp hψ hlevel
      hAmeas hAΩ hg
    rw [hAimg, hPdim] at h
    exact h
  · have h := setLIntegral_coarea_levelGraphFamily hsp hdim hO hu hΩ hψ hlevel hmem hinj
      hAmeas hAΩ hg
    rw [hAimg, hPdim] at h
    exact h

/-- **The codimension-`m` regular coarea formula.**  On an open set where the differential of `u` is
everywhere surjective, for every Borel `S ⊆ O` and every measurable `ℝ≥0∞` weight, the level
function is measurable and the coarea equality holds, with the normalized Hausdorff measure of the
codimension as the fibre measure.

This is the analogue of the scalar `L9`, `KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`; the level
function is even **measurable**, not merely almost everywhere measurable.

No finiteness, boundedness, integrability, regular-value or `SFinite` hypothesis is used, and no
regularity of `u` outside `O`.  **Nothing is claimed about the critical set**: surjectivity of the
differential is assumed at every point of `O`. -/
theorem coarea_of_contDiffOn_of_coareaJacobian_ne_zero {O S : Set V} {u : V → W} {g : V → ℝ≥0∞}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    (hreg : ∀ x ∈ O, coareaJacobian (fderiv ℝ u x) ≠ 0)
    (hS : MeasurableSet S) (hSO : S ⊆ O) (hg : Measurable g) :
    Measurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y
        ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W))) ∧
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y
          ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W)) ∂(volume : Measure W)) := by
  classical
  set ν : Measure V := KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W) with hν
  rcases S.eq_empty_or_nonempty with hSe | ⟨z₀, hz₀⟩
  · subst hSe
    simp
  choose N hN hxN hNO hformula using fun z : O =>
    exists_vector_coarea_neighborhood_measurable hO hu z.2 (hreg z z.2)
  obtain ⟨T, hTc, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable N hN
  have hOcov : ⋃ z : O, N z = O :=
    Set.Subset.antisymm (Set.iUnion_subset hNO) fun y hy =>
      Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxN ⟨y, hy⟩⟩
  have hTne : T.Nonempty := by
    have : z₀ ∈ ⋃ z ∈ T, N z := by rw [hTu, hOcov]; exact hSO hz₀
    obtain ⟨z, hzT, -⟩ := Set.mem_iUnion₂.1 this
    exact ⟨z, hzT⟩
  obtain ⟨σ, hσ⟩ := hTc.exists_eq_range hTne
  have hcov : O ⊆ ⋃ n, N (σ n) := by rw [← hOcov, ← hTu, hσ, Set.biUnion_range]
  set Q : ℕ → Set V := disjointed fun n => S ∩ N (σ n) with hQ
  have hQm : ∀ n, MeasurableSet (Q n) :=
    MeasurableSet.disjointed fun n => hS.inter (hN (σ n)).measurableSet
  have hQd : Pairwise (Function.onFun Disjoint Q) := disjoint_disjointed _
  have hQn : ∀ n, Q n ⊆ N (σ n) := fun n =>
    (disjointed_subset _ n).trans Set.inter_subset_right
  have hQO : ∀ n, Q n ⊆ O := fun n => (hQn n).trans (hNO (σ n))
  have hQu : ⋃ n, Q n = S := by
    rw [hQ, iUnion_disjointed, ← Set.inter_iUnion]
    exact Set.inter_eq_self_of_subset_left (hSO.trans hcov)
  have hslicem : ∀ n t, MeasurableSet (Q n ∩ {x : V | u x = t}) := by
    have hw : Measurable (O.piecewise u (fun _ => (0 : W))) :=
      hu.continuousOn.measurable_piecewise continuous_const.continuousOn hO.measurableSet
    intro n t
    have heq : Q n ∩ {x : V | u x = t}
        = Q n ∩ {x : V | O.piecewise u (fun _ => (0 : W)) x = t} := by
      ext x
      constructor <;> rintro ⟨hx, ht⟩ <;> exact ⟨hx, by simpa [hQO n hx] using ht⟩
    rw [heq]
    exact (hQm n).inter (hw (measurableSet_singleton t))
  have hmeas : ∀ n, Measurable (fun t : W => ∫⁻ y in Q n ∩ {x : V | u x = t}, g y ∂ν) :=
    fun n => (hformula (σ n) (Q n) (hQm n) (hQn n) g hg).1
  have hsum : ∀ t : W, (∫⁻ y in S ∩ {x : V | u x = t}, g y ∂ν)
      = ∑' n, ∫⁻ y in Q n ∩ {x : V | u x = t}, g y ∂ν := by
    intro t
    rw [← hQu, Set.iUnion_inter]
    exact lintegral_iUnion (fun n => hslicem n t)
      (fun i j hij => (hQd hij).mono Set.inter_subset_left Set.inter_subset_left) g
  refine ⟨?_, ?_⟩
  · simp_rw [hsum]
    exact Measurable.tsum hmeas
  · calc
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V))
          = ∑' n, ∫⁻ x in Q n, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
              ∂(volume : Measure V) := by
        rw [← hQu]
        exact lintegral_iUnion hQm hQd _
      _ = ∑' n, ∫⁻ t, ∫⁻ y in Q n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) :=
        tsum_congr fun n => (hformula (σ n) (Q n) (hQm n) (hQn n) g hg).2
      _ = ∫⁻ t, ∑' n, ∫⁻ y in Q n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) :=
        (lintegral_tsum fun n => (hmeas n).aemeasurable).symm
      _ = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) := by
        simp_rw [hsum]

end FunctionalInequalities.Analysis

import FunctionalInequalities.Analysis.Vector.Graph.Integral
import FunctionalInequalities.Analysis.Vector.Coarea.FiberIntegral

/-! # The local codimension-`m` coarea equality on a level chart

Everything the codimension-`m` coarea formula needs on one chart is now available, and this module
puts it together.  The three inputs, each proved separately:

* the **ambient side**, `setLIntegral_coareaJacobian_levelGraphFamily`: on a Borel piece of a level
  family the ambient coarea density becomes the graph area density, by the fibrewise
  `m`-dimensional change of variables and the fibre Jacobian identity;
* the **fibre side**, `setLIntegral_image_vectorGraphMap`: the weighted codimension-`m` graph area
  formula;
* the **slice description**, `slice_eq_image_vectorGraphMap`: each level set of the family is a
  graph over the corresponding parameter slice.

Tonelli in the level variable joins them.  The result,
`setLIntegral_coarea_levelGraphFamily`, is the codimension-`m` analogue of the scalar
`setLIntegral_coarea_graph_family`: on the image of a Borel piece of the chart,

`∫ coareaJacobian (Du) · g dx = ∫_t ∫_{fibre} g dℋ^{n-m} dt`,

with an arbitrary measurable `ℝ≥0∞` weight and no finiteness hypothesis anywhere.

**This is a local statement on one chart, not the codimension-`m` regular coarea formula.**  Two
things are still missing for that: the countable cover of a regular open set by such charts with the
disjoint patching, and the codimension-`m` weighted slice measurability that makes the outer
integral well posed as an a.e. statement (the scalar analogues are the assembly in
`Analysis/Coarea/Regular.lean` and `Analysis/Hausdorff/Slice/OpenMeasurable.lean`).
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

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K]
  [MeasurableSpace K] [BorelSpace K] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
/-- The derivative in the parameter coordinate is the joint derivative restricted to the parameter
factor. -/
theorem fderiv_fst_eq {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ) (p : H × W) :
    fderiv ℝ (fun y => ψ (y, p.2)) p.1 = fderiv ℝ ψ p ∘L (ContinuousLinearMap.inl ℝ H W) := by
  have hpath : HasFDerivAt (fun y : H => (y, p.2)) (ContinuousLinearMap.inl ℝ H W) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  exact (((hψ.differentiable one_ne_zero p).hasFDerivAt).comp p.1 hpath).fderiv

omit [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in
/-- The graph area density of the level family varies continuously with parameter and level. -/
theorem continuous_normDet_graphMapLinear_fderiv_fst (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (fun p : H × W => LinearMap.normDet
      ((graphMapLinear ι κ (fderiv ℝ (fun y => ψ (y, p.2)) p.1) : H →ₗ[ℝ] V))) := by
  simp_rw [fderiv_fst_eq hψ]
  exact (continuous_graphMapLinear_normDet ι κ).comp
    (((ContinuousLinearMap.compL ℝ H (H × W) K).flip
      (ContinuousLinearMap.inl ℝ H W)).continuous.comp (hψ.continuous_fderiv (by simp)))

/-- **The local codimension-`m` coarea equality.**  On the image of a Borel piece of a level-graph
family the integral of the ambient coarea density against an arbitrary measurable `ℝ≥0∞` weight is
the level integral of the surface integrals of that weight over the fibres.  The surface measure is
the repository's normalized `(n - m)`-dimensional Hausdorff measure.

No finiteness, boundedness or integrability is assumed, and there is no regularity of `u` outside
`O`.

**This is not the codimension-`m` regular coarea formula.**  It is the statement on **one chart**;
the countable cover with disjoint patching, and the codimension-`m` weighted slice measurability
that the a.e. form of the outer integral needs, are not proved. -/
theorem setLIntegral_coarea_levelGraphFamily {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hsp : IsVectorGraphSplitting ι κ) (hdim : finrank ℝ K = finrank ℝ W)
    {u : V → W} {O : Set V} (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    {Ω : Set (H × W)} (hΩ : IsOpen Ω) {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ)
    (hlevel : ∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2)
    (hmem : ∀ p ∈ Ω, ι p.1 + κ (ψ p) ∈ O)
    (hinj : InjOn (fun p : H × W => ι p.1 + κ (ψ p)) Ω)
    {A : Set (H × W)} (hA : MeasurableSet A) (hAΩ : A ⊆ Ω)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in (fun p : H × W => ι p.1 + κ (ψ p)) '' A,
        ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ x in ((fun p : H × W => ι p.1 + κ (ψ p)) '' A) ∩ {x : V | u x = t}, g x
          ∂(KLS.hausdorffNormalized V (finrank ℝ H)) ∂(volume : Measure W) := by
  have hcont : Continuous (fun p : H × W => ι p.1 + κ (ψ p)) :=
    (ι.continuous.comp continuous_fst).add (κ.continuous.comp hψ.continuous)
  have hm : Measurable (fun p : H × W => ENNReal.ofReal (LinearMap.normDet
      ((graphMapLinear ι κ (fderiv ℝ (fun y => ψ (y, p.2)) p.1) : H →ₗ[ℝ] V)))
        * g (ι p.1 + κ (ψ p))) :=
    (continuous_normDet_graphMapLinear_fderiv_fst ι κ hψ).measurable.ennreal_ofReal.mul
      (hg.comp hcont.measurable)
  rw [setLIntegral_coareaJacobian_levelGraphFamily hsp hdim hO hu hΩ hψ hlevel hmem hinj hA hAΩ hg,
    Measure.volume_eq_prod, setLIntegral_prod_fibers_symm hA hm]
  refine lintegral_congr fun t => ?_
  have hAt : MeasurableSet {y : H | (y, t) ∈ A} :=
    hA.preimage (measurable_id.prodMk measurable_const)
  have hslice := slice_eq_image_vectorGraphMap (ι := ι) (κ := κ) (u := u) (Ω := A) (ψ := ψ)
    (N := (fun p : H × W => ι p.1 + κ (ψ p)) '' A) rfl (fun p hp => hlevel p (hAΩ hp)) t
  have hγ : ContDiff ℝ 1 (fun y => ψ (y, t)) := hψ.comp (contDiff_id.prodMk contDiff_const)
  rw [hslice, setLIntegral_image_vectorGraphMap ι κ hsp.perp hγ hAt hg]
  rfl

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


/-- **Local regular coarea in codimension `m`.**  Every point where the differential is surjective
has an open neighbourhood on **every** Borel subset of which the coarea equality holds, for
**every** measurable `ℝ≥0∞` weight; the neighbourhood is independent of the weight.  The surface
measure is the normalized Hausdorff measure of the codimension, `finrank V - finrank W`.

This is the codimension-`m` analogue of `KLS.exists_regular_coarea_neighborhood`.  The stronger local theorem above also supplies weighted slice measurability.
The countable disjoint patching into the regular-domain coarea theorem is in
`Analysis/Vector/Coarea/Regular.lean`. -/
theorem exists_vector_coarea_neighborhood {u : V → W} {O : Set V} (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O)
    (hreg : coareaJacobian (fderiv ℝ u x₀) ≠ 0) :
    ∃ N : Set V, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      ∀ S : Set V, MeasurableSet S → S ⊆ N → ∀ g : V → ℝ≥0∞, Measurable g →
        ∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ x in S ∩ {x : V | u x = t}, g x
              ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W))
              ∂(volume : Measure W) := by
  obtain ⟨N, hN, hxN, hNO, h⟩ := exists_vector_coarea_neighborhood_measurable hO hu hx₀ hreg
  exact ⟨N, hN, hxN, hNO, fun S hS hSN g hg => (h S hS hSN g hg).2⟩
end FunctionalInequalities.Analysis

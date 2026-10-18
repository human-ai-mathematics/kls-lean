import FunctionalInequalities.Analysis.Vector.Graph.Area

/-! # The weighted codimension-`m` graph area formula

Property `B2` of the area formula route computes the normalized `k`-dimensional measure of a `C¹`
graph.  That is an identity of **measures of sets**; the coarea formula integrates an arbitrary
weight over a fibre, so it needs the same identity as a **change of variables**.

`map_vectorGraphMap_withDensity` upgrades it in the standard way: the graph parametrization pushes
the Jacobian-weighted Lebesgue measure on the parameter space forward to the normalized surface
measure restricted to the graph.  Injectivity of the graph map — automatic, by construction — and
measurability of its image are what make the two restrictions match.  From it,
`setLIntegral_image_vectorGraphMap` is the change of variables for an arbitrary measurable
`ℝ≥0∞`-valued weight.

This is the codimension-`m` analogue of `setLIntegral_image_graphMap` in `OpenGraphIntegral.lean`,
proved through `GraphIntegral.lean`; the structure of the argument is the same, with the
codimension-one Jacobian `√(1 + ‖∇g‖²)` replaced by `normDet (graphMapLinear ι κ (Dγ y))`.

**No integrability, finiteness or boundedness hypothesis** is used: the weight may be unbounded or
identically `∞`, and the parameter set need only be measurable.  **No coarea formula is proved
here.**
-/

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The graph parametrization pushes the Jacobian-weighted Lebesgue measure to the surface
measure.**  This upgrades the codimension-`m` area formula, an identity of *measures of sets*, into
an identity of measures usable as a change of variables for arbitrary integrands. -/
theorem map_vectorGraphMap_withDensity (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : ContDiff ℝ 1 γ)
    {s : Set H} (hs : MeasurableSet s) :
    Measure.map (vectorGraphMap ι κ γ)
        (((volume : Measure H).withDensity fun y => ENNReal.ofReal (LinearMap.normDet
            ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V)))).restrict s)
      = (KLS.hausdorffNormalized V (finrank ℝ H)).restrict (vectorGraphMap ι κ γ '' s) := by
  set Ψ : H → V := vectorGraphMap ι κ γ with hΨ
  set μ : Measure H := (volume : Measure H).withDensity fun y => ENNReal.ofReal
    (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) with hμ
  set ν : Measure V := KLS.hausdorffNormalized V (finrank ℝ H) with hν
  have hcont : Continuous Ψ := continuous_vectorGraphMap ι κ hγ.continuous
  have hmeasΨ : Measurable Ψ := hcont.measurable
  have hinj : Function.Injective Ψ := vectorGraphMap_injective ι κ hperp γ
  have hkey : Measure.map Ψ μ = ν.restrict (Set.range Ψ) := by
    refine Measure.ext fun E hE => ?_
    rw [Measure.map_apply hmeasΨ hE, hμ, withDensity_apply _ (hE.preimage hmeasΨ),
      ← hausdorffNormalized_image_vectorGraphMap ι κ hperp hγ (hE.preimage hmeasΨ),
      Measure.restrict_apply hE, Set.image_preimage_eq_inter_range]
  have himgmeas : MeasurableSet (Ψ '' s) :=
    measurableSet_image_vectorGraphMap ι κ hperp hγ.continuous hs
  have hpre : Ψ ⁻¹' (Ψ '' s) = s := hinj.preimage_image s
  calc Measure.map Ψ (μ.restrict s)
      = Measure.map Ψ (μ.restrict (Ψ ⁻¹' (Ψ '' s))) := by rw [hpre]
    _ = (Measure.map Ψ μ).restrict (Ψ '' s) := (Measure.restrict_map hmeasΨ himgmeas).symm
    _ = (ν.restrict (Set.range Ψ)).restrict (Ψ '' s) := by rw [hkey]
    _ = ν.restrict (Ψ '' s ∩ Set.range Ψ) := Measure.restrict_restrict himgmeas
    _ = ν.restrict (Ψ '' s) := by
        rw [Set.inter_eq_self_of_subset_left (Set.image_subset_range Ψ s)]

/-- **The weighted codimension-`m` graph area formula.**  The surface integral of an arbitrary
measurable `ℝ≥0∞` weight over a piece of a `C¹` graph is the Lebesgue integral of the weight against
the graph area density.  `B2` is the case `f = 1`.

No integrability, boundedness or finiteness is assumed; the parameter set need only be
measurable. -/
theorem setLIntegral_image_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : ContDiff ℝ 1 γ)
    {s : Set H} (hs : MeasurableSet s) {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in vectorGraphMap ι κ γ '' s, f x ∂(KLS.hausdorffNormalized V (finrank ℝ H))
      = ∫⁻ y in s, ENNReal.ofReal (LinearMap.normDet
            ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) * f (vectorGraphMap ι κ γ y)
          ∂(volume : Measure H) := by
  have hcont : Continuous (vectorGraphMap ι κ γ) := continuous_vectorGraphMap ι κ hγ.continuous
  rw [← map_vectorGraphMap_withDensity ι κ hperp hγ hs, lintegral_map hf hcont.measurable,
    setLIntegral_withDensity_eq_setLIntegral_mul _
      (measurable_vectorGraphJacobian ι κ γ).ennreal_ofReal
      (show Measurable fun y : H => f (vectorGraphMap ι κ γ y) from hf.comp hcont.measurable) hs]
  rfl

end FunctionalInequalities.Analysis

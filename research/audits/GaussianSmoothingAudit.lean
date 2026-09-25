import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing

/-! Independent full-signature clients for the proved Gaussian convolution properties.
The clients do not assert smoothness or convergence. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace GaussianSmoothingAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem finite_positive {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 ≤ s) (x : V) :
    0 < FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density ρ s x ∧
      FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.raw ρ s x < ⊤ :=
  ⟨FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density_pos hρ hs x,
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.raw_lt_top hρ hs x⟩

theorem pointwise_logConcave {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 ≤ s) (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density ρ s x ^ t *
      FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density ρ s y ^ (1 - t) ≤
      FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density ρ s
        (t • x + (1 - t) • y) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.density_logConcave
    hρ hs x y ht0 ht1

theorem normalized_kernel_mass {s : ℝ} (hs : 0 < s) :
    ∫ x : V,
      FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedKernel s x = 1 :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_normalizedKernel hs

theorem normalized_law {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure
        (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw ν s) ∧
      FunctionalInequalities.KLS.IsBorellDensity
        (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw ν s)
        volume
        (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s) :=
  ⟨FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_probability hs,
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_isBorellDensity
      hρ hs⟩

theorem normalized_tilted_convex {ν : Measure V} [IsProbabilityMeasure ν] {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw ν s =
      (volume : Measure V).tilted
        (-(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential ρ s))) ∧
      ConvexOn ℝ Set.univ
        (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential ρ s) :=
  ⟨FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_eq_tilted_potential
      hρ hs,
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential_convex hρ hs⟩

theorem normalized_logConcave_law {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ)
    {s : ℝ} (hs : 0 < s) :
    FunctionalInequalities.KLS.LogConcave
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw
        ν s hs) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw_logConcave
    hρ hs

end GaussianSmoothingAudit

#print axioms GaussianSmoothingAudit.finite_positive
#print axioms GaussianSmoothingAudit.pointwise_logConcave
#print axioms GaussianSmoothingAudit.normalized_kernel_mass
#print axioms GaussianSmoothingAudit.normalized_law
#print axioms GaussianSmoothingAudit.normalized_tilted_convex
#print axioms GaussianSmoothingAudit.normalized_logConcave_law

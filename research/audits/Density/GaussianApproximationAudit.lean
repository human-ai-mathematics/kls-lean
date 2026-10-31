module

public import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation

/-! Independent full-signature client for pointwise Gaussian approximation. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology

namespace GaussianApproximationAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem density_at_continuity {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {x : V} (hx : ContinuousAt ρ x) :
    Tendsto
      (fun s : ℝ => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity
        ρ s x)
      atTop (𝓝 (ρ x)) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_at_continuity
    hρ hx

theorem density_ae {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ) :
    ∀ᵐ x ∂(volume : Measure V),
      Tendsto
        (fun s : ℝ => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity
          ρ s x)
        atTop (𝓝 (ρ x)) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_ae_tendsto hρ

theorem density_L1 {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ) :
    Tendsto
      (fun s : ℝ => ∫ x : V,
        |FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s x -
          ρ x|)
      atTop (𝓝 0) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_L1 hρ

theorem law_setwise {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {D : Set V} (hD : MeasurableSet D) :
    Tendsto
      (fun s : ℝ =>
        (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw ν s) D)
      atTop (𝓝 (ν D)) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_set_tendsto hρ hD

end GaussianApproximationAudit

#print axioms GaussianApproximationAudit.density_at_continuity
#print axioms GaussianApproximationAudit.density_ae
#print axioms GaussianApproximationAudit.density_L1
#print axioms GaussianApproximationAudit.law_setwise

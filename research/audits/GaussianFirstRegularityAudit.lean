import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic

open FunctionalInequalities.Probability.Gaussian

/-! Independent full-signature client for first regularity of the actual Gaussian convolution. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace GaussianFirstRegularityAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem density_derivative {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) (x : V) :
    HasFDerivAt
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s)
      (∫ y, (-2 * s *
        FunctionalInequalities.Probability.Gaussian.normalizedKernel s (x-y)) •
          innerSL ℝ (x-y) ∂ν) x :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_hasFDerivAt
    hρ hs x

theorem density_C1 {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 1
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_contDiff_one
    hρ hs

theorem potential_C1 {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 1
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential ρ s) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential_contDiff_one
    hρ hs

end GaussianFirstRegularityAudit

#print axioms GaussianFirstRegularityAudit.density_derivative
#print axioms GaussianFirstRegularityAudit.density_C1
#print axioms GaussianFirstRegularityAudit.potential_C1

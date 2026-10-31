module

public import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic

/-! Independent full-signature client for second regularity of the actual Gaussian convolution. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace GaussianSecondRegularityAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem density_C2 {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 2
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_contDiff_two
    hρ hs

theorem potential_C2 {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 2
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential ρ s) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential_contDiff_two
    hρ hs

end GaussianSecondRegularityAudit

#print axioms GaussianSecondRegularityAudit.density_C2
#print axioms GaussianSecondRegularityAudit.potential_C2

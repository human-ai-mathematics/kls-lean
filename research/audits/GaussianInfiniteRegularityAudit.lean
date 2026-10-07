import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic

/-! Independent full-signature client for smoothness of the actual Gaussian convolution. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace GaussianInfiniteRegularityAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem density_Cinfty {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_contDiff_infty
    hρ hs

theorem potential_Cinfty {ν : Measure V} [IsProbabilityMeasure ν]
    {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential ρ s) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential_contDiff_infty
    hρ hs

theorem density_Cinfty_zero
    {ν : Measure (EuclideanSpace ℝ (Fin 0))} [IsProbabilityMeasure ν]
    {ρ : EuclideanSpace ℝ (Fin 0) → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity ρ s) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_contDiff_infty
    hρ hs

theorem potential_Cinfty_zero
    {ν : Measure (EuclideanSpace ℝ (Fin 0))} [IsProbabilityMeasure ν]
    {ρ : EuclideanSpace ℝ (Fin 0) → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity ν volume ρ)
    {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential ρ s) :=
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential_contDiff_infty
    hρ hs

end GaussianInfiniteRegularityAudit

#print axioms GaussianInfiniteRegularityAudit.density_Cinfty
#print axioms GaussianInfiniteRegularityAudit.potential_Cinfty
#print axioms GaussianInfiniteRegularityAudit.density_Cinfty_zero
#print axioms GaussianInfiniteRegularityAudit.potential_Cinfty_zero

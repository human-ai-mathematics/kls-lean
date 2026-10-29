import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Poincare

open FunctionalInequalities.Probability.Gaussian

/-! Independent full-signature clients for actual Gaussian-convolution Poincaré stability. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace GaussianPoincareStabilityAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem actualGaussianFactor {s : ℝ} (hs : 0 < s) :
    FunctionalInequalities.Poincare.SmoothTest.Holds
      (FunctionalInequalities.Probability.Gaussian.law (V := V) s)
      (1 / (2 * s)) := by
  exact FunctionalInequalities.Poincare.SmoothTest.holds_gaussianLaw hs

theorem actualConvolutionConstant (ν : Measure V) [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 < s) :
    FunctionalInequalities.Poincare.SmoothTest.constant
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw ν s) ≤
      FunctionalInequalities.Poincare.SmoothTest.constant ν +
        ENNReal.ofReal (1 / (2 * s)) := by
  exact FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_smoothTest_constant_le ν hs

theorem actualLiteratureConstant (ν : ProbabilityMeasure V) {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ)
    {s : ℝ} (hs : 0 < s) :
    FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw ν s hs) ≤
      FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν +
        ENNReal.ofReal (1 / (2 * s)) := by
  exact FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw_literatureConstant_le ν hρ hs

theorem actualLiteratureConstantZero
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)))
    {ρ : EuclideanSpace ℝ (Fin 0) → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity
      (ν : Measure (EuclideanSpace ℝ (Fin 0))) volume ρ)
    {s : ℝ} (hs : 0 < s) :
    FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw ν s hs) ≤
      FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν +
        ENNReal.ofReal (1 / (2 * s)) := by
  exact actualLiteratureConstant ν hρ hs

#print axioms actualGaussianFactor
#print axioms actualConvolutionConstant
#print axioms actualLiteratureConstant
#print axioms actualLiteratureConstantZero

end GaussianPoincareStabilityAudit

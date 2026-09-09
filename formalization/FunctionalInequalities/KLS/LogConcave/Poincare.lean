import FunctionalInequalities.KLS.LogConcave.AbsoluteContinuity
import FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison

/-!
# Poincare constants for general log-concave laws

Read `KLS.LogConcave.AbsoluteContinuity` for intrinsic absolute continuity, then `LiteratureComparison`
for the test-class comparison. This module removes the explicit absolute-continuity premise
from the comparison when the probability law is compact-set log-concave. Ambient singularity,
zero-dimensional affine support, and infinite optimal constants are included. No dimension-free
bound, Cheeger energy identification, or raw/core agreement is asserted.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.KLS.LogConcave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The ambient smooth-test, intrinsic smooth-test, and intrinsic literature optima agree
for every log-concave probability law. Absolute continuity is derived, not assumed. -/
theorem smoothTest_constant_eq_intrinsic_and_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothTest.constant (μ : Measure E) =
        Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.constant μ :=
  Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope μ Measure.addHaar
    (hμ.intrinsic_absolutelyContinuous Measure.addHaar)

/-- The smooth-test optimum equals the literature optimum for every log-concave law. -/
theorem smoothTest_constant_eq_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothTest.constant (μ : Measure E) = Poincare.LocalSlope.Intrinsic.constant μ :=
  (smoothTest_constant_eq_intrinsic_and_localSlope hμ).1.trans
    (smoothTest_constant_eq_intrinsic_and_localSlope hμ).2

/-- The selected intrinsic-affine relaxed constant agrees with the literature constant for
all finite-dimensional log-concave probability laws, including singular and Dirac laws. -/
theorem intrinsicSmooth_constant_eq_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothGradient.Intrinsic.constant μ = Poincare.LocalSlope.Intrinsic.constant μ :=
  Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope μ Measure.addHaar
    (hμ.intrinsic_absolutelyContinuous Measure.addHaar)

end FunctionalInequalities.KLS.LogConcave

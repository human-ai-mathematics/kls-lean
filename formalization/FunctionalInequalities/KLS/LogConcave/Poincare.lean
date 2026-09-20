import FunctionalInequalities.KLS.LogConcave.Density.AbsoluteContinuity
import FunctionalInequalities.Poincare.LocalSlope.Gradient
import FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison

/-!
# Poincare constants for general log-concave laws

Read `KLS/LogConcave/Density/AbsoluteContinuity.lean` for intrinsic absolute continuity, then
`Poincare/LocalSlope/SmoothTestComparison.lean` for the test-class comparison. This module removes the explicit absolute-continuity premise
from the comparison when the probability law is compact-set log-concave. It also supplies the
gradient-form optimum `Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient_of_logConcave`.
Ambient singularity,
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

namespace FunctionalInequalities.Poincare.LocalSlope

open ProbabilityTheory TopologicalSpace

universe u_2

variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- `Q0`: the literature-Poincaré clause of `thm:klartag-density-frontend-identification`.

Every finite-dimensional log-concave law has an absolutely continuous intrinsic law, so its
literature optimum is the gradient-form optimum. The reference Haar measure is produced here
rather than assumed: the direction of the affine support is a finite-dimensional normed space,
hence weakly locally compact, so it carries an additive Haar measure. The statement therefore
mentions no reference measure, and the constant does not depend on the choice. -/
theorem Intrinsic.constant_eq_iInf_gradient_of_logConcave {μ : ProbabilityMeasure E}
    (hμ : KLS.LogConcave μ) :
    Poincare.LocalSlope.Intrinsic.constant μ =
      ⨅ C : {C : NNReal //
          ∀ g : (Probability.affineSupport μ).direction → ℝ, LocallyLipschitz g →
            MemLp g 2 (Probability.intrinsicMeasure μ :
              Measure (Probability.affineSupport μ).direction) →
            MemLp (gradient g) 2 (Probability.intrinsicMeasure μ :
              Measure (Probability.affineSupport μ).direction) →
            evariance g (Probability.intrinsicMeasure μ :
                Measure (Probability.affineSupport μ).direction) ≤
              (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2
                ∂(Probability.intrinsicMeasure μ :
                  Measure (Probability.affineSupport μ).direction)},
        (C.1 : ENNReal) := by
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (Probability.affineSupport μ).direction) := inferInstance
  have hm : (Measure.addHaarMeasure K₀).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_addHaarMeasure K₀
  exact Intrinsic.constant_eq_iInf_gradient μ (Measure.addHaarMeasure K₀)
    (hμ.intrinsic_absolutelyContinuous _)


end FunctionalInequalities.Poincare.LocalSlope

import FunctionalInequalities.KLS.LogConcave.AbsoluteContinuity
import FunctionalInequalities.Poincare.Euclidean.LiteratureComparison

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
theorem legacy_eq_intrinsic_and_literature
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.constant (μ : Measure E) =
        Poincare.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      Poincare.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        KLS.literatureConstant μ :=
  Poincare.Euclidean.constant_eq_intrinsic_and_literature μ Measure.addHaar
    (hμ.intrinsic_absolutelyContinuous Measure.addHaar)

/-- The legacy smooth-test optimum equals the literature optimum for every log-concave law. -/
theorem legacy_eq_literature
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.constant (μ : Measure E) = KLS.literatureConstant μ :=
  (legacy_eq_intrinsic_and_literature hμ).1.trans
    (legacy_eq_intrinsic_and_literature hμ).2

/-- The selected intrinsic-affine relaxed constant agrees with the literature constant for
all finite-dimensional log-concave probability laws, including singular and Dirac laws. -/
theorem canonical_eq_literature
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.Canonical.constant μ = KLS.literatureConstant μ :=
  Poincare.Canonical.eq_literature_of_ac μ Measure.addHaar
    (hμ.intrinsic_absolutelyContinuous Measure.addHaar)

end FunctionalInequalities.KLS.LogConcave

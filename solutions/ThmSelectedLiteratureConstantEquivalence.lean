module

public import FunctionalInequalities.KLS.LogConcave.Poincare

/-!
# Lean certificate: `thm:selected-literature-constant-equivalence`

Every finite-dimensional compact-set log-concave probability law has the same selected and
literature Poincare constant. No explicit density, full-dimensional ambient support, positive
dimension, or finite-moment hypothesis is added. This is a frontend equality, not a KLS bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.ThmSelectedLiteratureConstantEquivalence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The complete general log-concave comparison from the Blueprint. -/
theorem certificate (μ : ProbabilityMeasure E) (hμ : KLS.LogConcave μ) :
    FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.constant μ =
      FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ :=
  hμ.intrinsicSmooth_constant_eq_localSlope

/-- Typed applications cover the exact Euclidean family in Conjecture, including dimension zero. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : KLS.LogConcave μ) :
    FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.constant μ =
      FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ := certificate μ hμ

example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) (hμ : KLS.LogConcave μ) :
    FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.constant μ =
      FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ := certificate μ hμ

end Solutions.ThmSelectedLiteratureConstantEquivalence

/--
info: 'Solutions.ThmSelectedLiteratureConstantEquivalence.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmSelectedLiteratureConstantEquivalence.certificate

/--
info: 'FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_intrinsic_and_localSlope'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_intrinsic_and_localSlope

/--
info: 'FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_localSlope'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_localSlope

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsicSmooth_constant_eq_localSlope'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicSmooth_constant_eq_localSlope

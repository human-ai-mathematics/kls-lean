import FunctionalInequalities.Poincare

/-!
# Candidate statement for the first KLS autoformalization calibration

The live actor replaces only the definition below. The initial `True` value is a compiling sentinel,
not a mathematical candidate and not repository evidence.
-/

noncomputable section

open MeasureTheory

namespace Experiments.Humanize2KLS

def candidateLinearTestLowerStatement {D : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin D))) [IsProbabilityMeasure μ]
    (_hμ : MemLp (id : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)) 2 μ) : Prop :=
  (∀ f : EuclideanSpace ℝ (Fin D) → ℝ,
      FunctionalInequalities.IsAdmissible μ f →
        FunctionalInequalities.poincareRayleighQuotient μ f ≤
          FunctionalInequalities.optimalPoincareConstant μ) ∧
    FunctionalInequalities.lambdaMaxCovariance μ ≤
      FunctionalInequalities.optimalPoincareConstant μ

end Experiments.Humanize2KLS

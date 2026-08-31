import FunctionalInequalities.Project.LinearTestLower

/-!
# Lean certificate for Issue #2

The reusable proof lives in `FunctionalInequalities.Project.LinearTestLower`.  This deliberately
thin file exposes the complete project theorem as a separately compiled certificate.
-/

noncomputable section

open MeasureTheory

namespace Solutions.LemLinearTestLower

/-- Machine certificate for the full linear-test Poincaré lower bound on `ℝ^D`. -/
theorem lem_linear_test_lower {D : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin D))) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)) 2 μ) :
    (∀ ⦃f : EuclideanSpace ℝ (Fin D) → ℝ⦄,
      FunctionalInequalities.IsAdmissible μ f →
      FunctionalInequalities.poincareRayleighQuotient μ f ≤
        FunctionalInequalities.optimalPoincareConstant μ) ∧
      FunctionalInequalities.lambdaMaxCovariance μ ≤
        FunctionalInequalities.optimalPoincareConstant μ :=
  FunctionalInequalities.Project.linearTestLowerCertificate μ hμ

end Solutions.LemLinearTestLower

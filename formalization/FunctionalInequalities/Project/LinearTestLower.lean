import FunctionalInequalities.Poincare

/-!
# Project certificate for `lem:linear-test-lower`

This module packages the reusable Poincaré API into the exact finite-dimensional probability
statement used by the repository ledger.  `MemLp id 2 μ` is the explicit finite-covariance
hypothesis.  The zero-dimensional case is included: its unit sphere is empty and
`lambdaMaxCovariance μ = 0`.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Project

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The covariance part of ledger node `lem:linear-test-lower`, on an abstract finite-dimensional
real Hilbert space. -/
theorem linearTestLower (μ : Measure E) [FiniteDimensional ℝ E] [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMaxCovariance μ ≤ optimalPoincareConstant μ :=
  lambdaMaxCovariance_le_optimal hμ

/-- The complete machine-facing content of `lem:linear-test-lower`: every admissible test gives an
extended Rayleigh lower bound, and linear tests give the largest covariance eigenvalue lower
bound. -/
theorem linearTestLowerCertificate (μ : Measure E) [FiniteDimensional ℝ E]
    [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) :
    (∀ ⦃f : E → ℝ⦄, IsAdmissible μ f →
      poincareRayleighQuotient μ f ≤ optimalPoincareConstant μ) ∧
      lambdaMaxCovariance μ ≤ optimalPoincareConstant μ := by
  constructor
  · intro f hf
    exact poincareRayleighQuotient_le_optimal hf
  · exact linearTestLower μ hμ

/-- Concrete `ℝ^D` specialization of the ledger theorem. -/
theorem euclideanLinearTestLower {D : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin D))) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)) 2 μ) :
    lambdaMaxCovariance μ ≤ optimalPoincareConstant μ :=
  linearTestLower μ hμ

end FunctionalInequalities.Project

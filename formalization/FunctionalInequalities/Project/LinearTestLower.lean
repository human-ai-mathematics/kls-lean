import FunctionalInequalities.Poincare

/-!
# Issue 2 certificate for the linear half of `KLS.pdf`, Remark 3.8

The reference says that a test function gives a Rayleigh-quotient lower bound on `C_P`, and that
linear tests give `C_P ≥ λ_max(Cov_P)`.  This module packages precisely those two statements into
the finite-dimensional probability theorem used by ledger node `lem:linear-test-lower`.

`MemLp id 2 μ` makes the reference's covariance hypothesis explicit.  The zero-dimensional case
is included with value `0`.  Mode-indicator tests and the Gaussian equality of Family 4.1 are not
part of this certificate.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Project.LinearTestLower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The linear-test conclusion `C_P ≥ λ_max(Cov_P)` from Remark 3.8, written in Lean's order and
on an abstract finite-dimensional real Hilbert space. -/
theorem covariance (μ : Measure E) [FiniteDimensional ℝ E] [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) :
    Covariance.lambdaMax μ ≤ Poincare.constant μ :=
  Covariance.lambdaMax_le_constant hμ

/-- The complete Issue 2 certificate for Remark 3.8: every admissible test gives an extended
Rayleigh lower bound, and linear tests give the largest centered-covariance eigenvalue lower
bound. -/
theorem certificate (μ : Measure E) [FiniteDimensional ℝ E]
    [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) :
    (∀ ⦃f : E → ℝ⦄, Poincare.Admissible μ f →
      Poincare.rayleigh μ f ≤ Poincare.constant μ) ∧
      Covariance.lambdaMax μ ≤ Poincare.constant μ := by
  constructor
  · intro f hf
    exact Poincare.rayleigh_le_constant hf
  · exact covariance μ hμ

/-- Concrete `ℝ^D` specialization of the reference's linear-test covariance lower bound. -/
theorem euclidean {D : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin D))) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)) 2 μ) :
    Covariance.lambdaMax μ ≤ Poincare.constant μ :=
  covariance μ hμ

end FunctionalInequalities.Project.LinearTestLower

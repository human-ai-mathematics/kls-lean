import FunctionalInequalities.Project.LinearTestLower

/-!
# Lean certificate for `KLS.pdf`, Remark 3.8 (`lem:linear-test-lower`)

The reference's Issue 2 claim is the lower-bound direction: Rayleigh quotients bound `C_P` from
below, and linear tests give `C_P ≥ λ_max(Cov_P)`.  The reusable proof and its precise moment and
zero-dimensional conventions live in `FunctionalInequalities.Project.LinearTestLower`.  This
deliberately thin file is the node-specific artifact that the ledger checker binds through
`lean_solution`; it certifies no Poincaré upper bound.
-/

noncomputable section

open MeasureTheory
open FunctionalInequalities

namespace Solutions.LemLinearTestLower

/-- Machine certificate for the two lower-bound conclusions of Remark 3.8 that belong to Issue 2:
the admissible-test Rayleigh bound and its linear-test covariance consequence on `ℝ^D`. -/
theorem certificate {D : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin D))) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)) 2 μ) :
    (∀ ⦃f : EuclideanSpace ℝ (Fin D) → ℝ⦄,
      Poincare.Admissible μ f → Poincare.rayleigh μ f ≤ Poincare.constant μ) ∧
      Covariance.lambdaMax μ ≤ Poincare.constant μ :=
  Project.LinearTestLower.certificate μ hμ

end Solutions.LemLinearTestLower

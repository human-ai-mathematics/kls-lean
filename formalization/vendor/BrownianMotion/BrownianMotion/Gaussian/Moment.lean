-- Modified 2026-10-31 by the KLS formalization project: explicit import of the square-root
-- calculus needed under Mathlib v4.35.0's module imports; see vendor/port.patch.
-- Modified 2026-11-18 by the KLS formalization project to obtain even Gaussian
-- moments from Tau Ceti. See vendor/port.patch.
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Probability.Distributions.Gaussian.Moments

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

lemma centralMoment_two_mul_gaussianReal (μ : ℝ) (σ : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (gaussianReal μ (σ^2))
    = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) := by
  calc
    _ = (((σ ^ 2 : ℝ≥0) : ℝ) ^ n) * Nat.doubleFactorial (2 * n - 1) :=
      TauCeti.Probability.centralMoment_id_two_mul_gaussianReal μ (σ ^ 2) n
    _ = _ := by rw [NNReal.coe_pow, ← pow_mul]

lemma centralMoment_fun_two_mul_gaussianReal (μ : ℝ) (σ : ℝ≥0) (n : ℕ) :
    centralMoment (fun x ↦ x) (2 * n) (gaussianReal μ (σ^2))
    = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) :=
  centralMoment_two_mul_gaussianReal ..

end ProbabilityTheory

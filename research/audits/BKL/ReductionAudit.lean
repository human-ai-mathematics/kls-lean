import FunctionalInequalities.KLS.BKL.Reduction

/-!
# Audit: the p. 30 conditional reduction (BKL)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, p. 30, proof of Theorem 1.1 from Theorems 3.1,
4.1 and Proposition 7.1. The reduction is conditional on the universal cumulant bounds
`CumulantBound d ((d!)² K^d)` for all `d ≥ 2` (supplied separately by the proved Theorem 4.1); it yields
`C_P(μ) ≤ 2 C_{3.1} K` for every isotropic regular law in every dimension. Clients: the `d = 1` Taylor
bound for the standard Gaussian on `ℝ¹`, the numeric step at `K = 1`, and the conditional conclusion
specialised to `K = 1`. Neither Theorem 4.1 nor Theorem 1.1 is asserted.
-/

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace

namespace ReductionAudit

/-- Numeric step at `K = 1`, `d = 2`: `2 ≤ 4`. -/
theorem numeric_two : 2 * (1 : ℝ) ^ 2 ≤ (2 * 1) ^ 2 :=
  KLS.RegularPotential.two_mul_pow_le_two_mul_pow zero_le_one (by norm_num)

/-- The conditional conclusion at `K = 1`: under `CumulantBound d ((d!)²)` for all `d ≥ 2`, every
isotropic regular law has `C_P ≤ 2 C`. -/
theorem conditional_at_one
    (hcb : ∀ d : ℕ, 2 ≤ d → KLS.LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * 1 ^ d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
      (hV : KLS.RegularPotential V a b), KLS.Isotropic hV.law →
      Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (2 * C * 1) := by
  obtain ⟨C, hC, h⟩ := KLS.RegularPotential.poincare_le_of_cumulantBound
  exact ⟨C, hC, fun n V a b hV hiso => h 1 le_rfl hcb n V a b hV hiso⟩

end ReductionAudit

#print axioms FunctionalInequalities.Analysis.BakryEmery.tiltAverage_mul_integral_exp
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_apply
#print axioms FunctionalInequalities.KLS.coordTensor_taylorTensor_one_apply
#print axioms FunctionalInequalities.KLS.Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries
#print axioms FunctionalInequalities.KLS.Isotropic.norm_coordTensor_taylorTensor_one_le
#print axioms FunctionalInequalities.KLS.RegularPotential.two_mul_pow_le_two_mul_pow
#print axioms FunctionalInequalities.KLS.RegularPotential.poincare_le_of_cumulantBound
#print axioms ReductionAudit.numeric_two
#print axioms ReductionAudit.conditional_at_one

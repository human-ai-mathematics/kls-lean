import FunctionalInequalities.Analysis.Matrix.Trace.Algebra

/-!
# Audit: trace–energy inequality (support of the BKL (67) log-determinant non-explosion route)

Module: `Analysis/Matrix/Trace/Algebra.lean`.

Clients of `sum_trace_sq_le_card_mul_sum_sq`: the full original statement, a signed nonsymmetric
two-dimensional family (`64 ≤ 94`), saturation of the dimension-two identity, and the `Fin 0`
instance. Deterministic support only: no covariance dynamics, stochastic integral, Itô formula,
strong solution or non-explosion theorem is involved.
-/

noncomputable section
open FunctionalInequalities.Analysis

namespace IndependentTraceEnergy

theorem original_contract {n : ℕ} (B : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i : Fin n, Matrix.trace (B i) ^ 2) ≤
      (n : ℝ) * ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (B i j k) ^ 2 :=
  sum_trace_sq_le_card_mul_sum_sq B

def signedB (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  if i = 0 then !![1, 2; -3, -1] else !![4, 0; 0, 4]

theorem signed_nonsymmetric : (64 : ℝ) ≤ 94 := by
  calc
    (64 : ℝ) = ∑ i : Fin 2, Matrix.trace (signedB i) ^ 2 := by
      norm_num [signedB, Matrix.trace, Fin.sum_univ_two]
    _ ≤ (2 : ℝ) * ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, (signedB i j k) ^ 2 :=
      sum_trace_sq_le_card_mul_sum_sq signedB
    _ = 94 := by norm_num [signedB, Fin.sum_univ_two]

theorem saturation :
    (∑ _i : Fin 2, Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℝ) ^ 2) =
      (2 : ℝ) * ∑ _i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) j k) ^ 2 := by
  norm_num [Matrix.trace, Fin.sum_univ_two]

theorem empty (B : Fin 0 → Matrix (Fin 0) (Fin 0) ℝ) :
    (∑ i : Fin 0, Matrix.trace (B i) ^ 2) ≤
      ((0 : ℕ) : ℝ) * ∑ i : Fin 0, ∑ j : Fin 0, ∑ k : Fin 0, (B i j k) ^ 2 :=
  sum_trace_sq_le_card_mul_sum_sq B

#print axioms original_contract
#print axioms signed_nonsymmetric
#print axioms saturation
#print axioms empty
#print axioms FunctionalInequalities.Analysis.sum_trace_sq_le_card_mul_sum_sq

end IndependentTraceEnergy

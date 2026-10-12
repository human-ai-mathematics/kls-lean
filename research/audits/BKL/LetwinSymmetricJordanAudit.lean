import FunctionalInequalities.Analysis.Matrix.Sign

/-!
# Audit: Jordan decomposition and trace energy of real symmetric matrices

Source: Letwin, arXiv:2607.24164v1, Theorem 2.5 (support only: the extension from positive semidefinite to all symmetric
`B`). A real indefinite, noncommuting client on `Fin 2`: `B = diag(1, −2)` is symmetric and neither `B` nor `−B` is
positive semidefinite, `H = [[2, 1], [1, 2]]` is positive semidefinite, `B H ≠ H B`, and `tr(B H B H) = 16 ≥ 0`.
A real algebraic example, not a moment-map or source-law certificate. Client body: strong-API candidate
(`api-symmetric-compiler-patch-v3`, e735387e…), verbatim.
-/

open Matrix
open FunctionalInequalities.Analysis

namespace LetwinSymmetricJordanAudit

/-- A concrete noncommuting indefinite two-dimensional example. -/
theorem fin2_client :
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -2]
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]
    B.IsSymm ∧ ¬ B.PosSemidef ∧ ¬ (-B).PosSemidef ∧ H.PosSemidef ∧
      B * H ≠ H * B ∧ (B * H * B * H).trace = 16 ∧
      0 ≤ (B * H * B * H).trace := by
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -2]
  let H : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]
  change B.IsSymm ∧ ¬ B.PosSemidef ∧ ¬ (-B).PosSemidef ∧ H.PosSemidef ∧
    B * H ≠ H * B ∧ (B * H * B * H).trace = 16 ∧
    0 ≤ (B * H * B * H).trace
  have hB : B.IsSymm := by
    change B.transpose = B
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hnotP : ¬ B.PosSemidef := by
    intro h
    have hd := h.diag_nonneg (i := (1 : Fin 2))
    norm_num [B] at hd
  have hnotN : ¬ (-B).PosSemidef := by
    intro h
    have hd := h.diag_nonneg (i := (0 : Fin 2))
    norm_num [B] at hd
  have hH : H.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · change H.conjTranspose = H
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro x
      simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1),
        sq_nonneg (x 0 + x 1)]
  have hcomm : B * H ≠ H * B := by
    intro h
    have he := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [B, H, Matrix.mul_apply, Fin.sum_univ_succ] at he
  have htrace : (B * H * B * H).trace = 16 := by
    norm_num [B, H, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨hB, hnotP, hnotN, hH, hcomm, htrace, ?_⟩
  rw [htrace]
  norm_num

end LetwinSymmetricJordanAudit

#print axioms FunctionalInequalities.Analysis.cfc_posSemidef_of_nonneg
#print axioms FunctionalInequalities.Analysis.trace_cross_nonneg
#print axioms FunctionalInequalities.Analysis.trace_energy_nonneg
#print axioms FunctionalInequalities.Analysis.jordan_trace_domination
#print axioms FunctionalInequalities.Analysis.symmetric_jordan_decomposition
#print axioms FunctionalInequalities.Analysis.symmetric_jordan_trace_support
#print axioms LetwinSymmetricJordanAudit.fin2_client

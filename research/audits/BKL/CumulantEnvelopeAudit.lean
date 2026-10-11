import FunctionalInequalities.KLS.BKL.CumulantEnvelope
import FunctionalInequalities.Analysis.Tensor.Coordinate

/-!
# Audit: BKL Section 6 envelope arithmetic with source-range consumers

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 6, pp. 26–27: the envelope
`b_m = K^{m-1}((m-1)!)²`, the identities (105)–(106) and the scalar absorption after (106), and
the contraction (101)–(102). These are the arithmetic steps of the induction only; no cumulant
process, energy estimate or Theorem 4.1 is asserted.

* `identity105`, `sum106_boundary`: (105) at `m = 4, a = 2` and the empty sum of (106) at `m = 3`.
* `absorption_source`: the absorption under the source's own constants `C ≥ 1`,
  `K ≥ max{5, 9C, 64}`, instantiating the stronger `C ≥ 0` library statement.
* `absorption_at_four`: a source-range instance in which the square-root term is positive.
* `contract_identity`: a nonzero instance of the contraction (101)–(102).
-/

namespace BKLCumulantEnvelopeAudit

open FunctionalInequalities.KLS.BKL FunctionalInequalities.Analysis.Tensor

/-- (105) at `m = 4`, `a = 2`, `K = 64`. -/
theorem identity105 :
    ((4 - 1).choose (2 - 1) : ℝ) * Real.sqrt (envelope 64 2 * envelope 64 (4 - 2 + 1)) =
      Real.sqrt (envelope 64 4) :=
  choose_mul_sqrt_envelope (by norm_num) (by norm_num) (by norm_num)

/-- The instance is not degenerate. -/
theorem envelope_nonzero : 0 < envelope 64 4 := by
  norm_num [envelope]

/-- At `m = 3` the range of (106) is empty. -/
theorem sum106_boundary :
    ∑ a ∈ Finset.Icc 2 (3 - 2),
      ((3 - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope 64 a * envelope 64 (3 - a + 1)) = 0 := by
  have h := sum_choose_mul_sqrt_envelope (K := 64) (by norm_num) (m := 3) (by norm_num)
  exact h.trans (by norm_num)

/-- The absorption under the source's constants `C ≥ 1`, `K ≥ max{5, 9C, 64}`. -/
theorem absorption_source {K C : ℝ} (hC : 1 ≤ C)
    (hK : max 5 (max (9 * C) 64) ≤ K) {m : ℕ} (hm : 3 ≤ m) :
    2 * C * (m : ℝ) ^ 2 * envelope K (m - 1) +
        4 * ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K (m - 1) * envelope K m) ≤
      envelope K m := by
  have hKrest : max (9 * C) 64 ≤ K := le_of_max_le_right hK
  exact absorption_le_envelope (by linarith) (le_of_max_le_left hKrest)
    (le_of_max_le_right hKrest) hm

/-- `C = 1`, `K = 64`, `m = 4`: the square-root term is positive. -/
theorem absorption_at_four :
    2 * (1 : ℝ) * (4 : ℝ) ^ 2 * envelope 64 (4 - 1) +
        4 * ((4 - 3 : ℕ) : ℝ) * Real.sqrt (envelope 64 (4 - 1) * envelope 64 4) ≤
      envelope 64 4 :=
  absorption_source (by norm_num) (by norm_num) (by norm_num)

/-- The square-root term at `m = 4` is positive. -/
theorem sqrt_term_pos_at_four :
    0 < 4 * ((4 - 3 : ℕ) : ℝ) * Real.sqrt (envelope 64 (4 - 1) * envelope 64 4) := by
  have h : 0 < envelope 64 (4 - 1) * envelope 64 4 := by norm_num [envelope]
  have hc : (0 : ℝ) < 4 * ((4 - 3 : ℕ) : ℝ) := by norm_num
  exact mul_pos hc (Real.sqrt_pos.mpr h)

/-- A nonzero identity-row contraction: two rows and two columns. -/
theorem contract_identity :
    (∑ _i : Fin 2, ∑ j : Fin 2,
      (∑ k : Fin 2, (1 : ℝ) * (if k = j then 1 else 0)) ^ 2) ≤
      (1 : ℝ) * ∑ _i : Fin 2, ∑ _k : Fin 2, (1 : ℝ) ^ 2 := by
  let T : Fin 2 → Fin 2 → ℝ := fun j k => if k = j then 1 else 0
  have hT : ∀ v : Fin 2 → ℝ, ∑ j, (∑ k, v k * T j k) ^ 2 ≤ 1 * ∑ k, v k ^ 2 := by
    intro v
    simp [T, mul_ite]
  exact sum_sq_contract_le T hT (fun _ _ => 1)

end BKLCumulantEnvelopeAudit

#print axioms BKLCumulantEnvelopeAudit.identity105
#print axioms BKLCumulantEnvelopeAudit.sum106_boundary
#print axioms BKLCumulantEnvelopeAudit.absorption_source
#print axioms BKLCumulantEnvelopeAudit.absorption_at_four
#print axioms BKLCumulantEnvelopeAudit.sqrt_term_pos_at_four
#print axioms BKLCumulantEnvelopeAudit.contract_identity
#print axioms FunctionalInequalities.KLS.BKL.envelope_succ
#print axioms FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope
#print axioms FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope
#print axioms FunctionalInequalities.KLS.BKL.absorption_le_envelope
#print axioms FunctionalInequalities.Analysis.Tensor.sum_sq_contract_le

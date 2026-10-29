import FunctionalInequalities.Analysis.Cutoff.Profile

/-!
# Audit: tail primitive of Letwin Lemma A.4

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17), `q_R(t) = R⁻¹ ∫_{t/R}^∞ w`. Actual
clients of `inv_mul_intervalIntegral_div_three_cutoff`, with every hypothesis derived here, never
the primitive's conclusions: the explicit smooth bump
`w t = smoothTransition t · smoothTransition (3 − t)` (nonnegative, zero for `t ≤ 0` and `t ≥ 3`,
`w 1 = 1`) at `R = 1` and `R = 2`, on both sides (`t = −1 < 0` and `t > 3R`), with the source
coefficient `q_R′(R) = −R⁻² w(1) = −R⁻²`; and the majorant of `|η″|` composed with the primitive
for any `R ≥ 1`.
-/

open FunctionalInequalities.Analysis
open scoped ContDiff

namespace A4CutoffPrimitiveClient

/-- An actual smooth bump supported in `[0, 3]`. -/
noncomputable def bump (t : ℝ) : ℝ := Real.smoothTransition t * Real.smoothTransition (3 - t)

theorem contDiff_bump : ContDiff ℝ ∞ bump :=
  Real.smoothTransition.contDiff.mul (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem bump_nonneg (t : ℝ) : 0 ≤ bump t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bump_eq_zero (t : ℝ) (h : t ≤ 0 ∨ 3 ≤ t) : bump t = 0 := by
  rcases h with h | h
  · rw [bump, Real.smoothTransition.zero_of_nonpos h, zero_mul]
  · rw [bump, Real.smoothTransition.zero_of_nonpos (by linarith : 3 - t ≤ 0), mul_zero]

theorem bump_one : bump 1 = 1 := by
  rw [bump, Real.smoothTransition.one_of_one_le le_rfl,
    Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 3 - 1), mul_one]

/-- `R = 1`: smooth; `q′(1) = −1` (the coefficient `−R⁻²` times `w 1 = 1`); `q′(−1) = 0`; `q(4) = 0` (`4 ≥ 3R`); bounds at
`t = −1 < 0`. -/
theorem primitive_one :
    ContDiff ℝ ∞ (fun t => (1 : ℝ)⁻¹ * ∫ s in t / 1..3, bump s) ∧
      deriv (fun t => (1 : ℝ)⁻¹ * ∫ s in t / 1..3, bump s) 1 = -1 ∧
      deriv (fun t => (1 : ℝ)⁻¹ * ∫ s in t / 1..3, bump s) (-1) = 0 ∧
      (1 : ℝ)⁻¹ * ∫ s in (4 : ℝ) / 1..3, bump s = 0 ∧
      0 ≤ (1 : ℝ)⁻¹ * ∫ s in (-1 : ℝ) / 1..3, bump s ∧
      (1 : ℝ)⁻¹ * ∫ s in (-1 : ℝ) / 1..3, bump s ≤ (1 : ℝ)⁻¹ * ∫ s in (0 : ℝ)..3, bump s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    inv_mul_intervalIntegral_div_three_cutoff contDiff_bump bump_nonneg bump_eq_zero (R := 1) one_pos
  refine ⟨h1, ?_, ?_, h5 4 (by norm_num), h3 (-1), h4 (-1)⟩
  · rw [h2 1, div_one, bump_one]; norm_num
  · rw [h2 (-1), bump_eq_zero _ (Or.inl (by norm_num))]; norm_num

/-- `R = 2`: `q′(2) = −1/4 = −R⁻²`; `q′(−1) = 0`; `q(7) = 0` (`7 > 3R = 6`); bounds at `t = −1 < 0`. -/
theorem primitive_two :
    deriv (fun t => (2 : ℝ)⁻¹ * ∫ s in t / 2..3, bump s) 2 = -(1 / 4) ∧
      deriv (fun t => (2 : ℝ)⁻¹ * ∫ s in t / 2..3, bump s) (-1) = 0 ∧
      (2 : ℝ)⁻¹ * ∫ s in (7 : ℝ) / 2..3, bump s = 0 ∧
      0 ≤ (2 : ℝ)⁻¹ * ∫ s in (-1 : ℝ) / 2..3, bump s ∧
      (2 : ℝ)⁻¹ * ∫ s in (-1 : ℝ) / 2..3, bump s ≤ (2 : ℝ)⁻¹ * ∫ s in (0 : ℝ)..3, bump s := by
  obtain ⟨-, h2, h3, h4, h5⟩ :=
    inv_mul_intervalIntegral_div_three_cutoff contDiff_bump bump_nonneg bump_eq_zero (R := 2) two_pos
  refine ⟨?_, ?_, h5 7 (by norm_num), h3 (-1), h4 (-1)⟩
  · rw [h2 2, div_self (two_ne_zero), bump_one]; norm_num
  · rw [h2 (-1), bump_eq_zero _ (Or.inl (by norm_num))]; norm_num

/-- The majorant of `|η″|` composed with the primitive, for every `R ≥ 1` (the Lemma A.4
energy weight). -/
theorem majorant_primitive (R : ℝ) (hR : 1 ≤ R) :
    ∃ w : ℝ → ℝ, (∀ t, |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ w t) ∧
      ContDiff ℝ ∞ (fun t => R⁻¹ * ∫ s in t / R..3, w s) ∧
      (∀ t, deriv (fun t => R⁻¹ * ∫ s in t / R..3, w s) t = -((R ^ 2)⁻¹ * w (t / R))) ∧
      ∀ t, 3 * R ≤ t → R⁻¹ * ∫ s in t / R..3, w s = 0 := by
  obtain ⟨w, hw, -, hw0, hws, hmaj⟩ := exists_majorant_abs_deriv_deriv_smoothTransition_two_sub
  obtain ⟨h1, h2, -, -, h5⟩ :=
    inv_mul_intervalIntegral_div_three_cutoff hw hw0 hws (lt_of_lt_of_le one_pos hR)
  exact ⟨w, hmaj, h1, h2, h5⟩

end A4CutoffPrimitiveClient

#print axioms inv_mul_intervalIntegral_div_three_cutoff
#print axioms A4CutoffPrimitiveClient.contDiff_bump
#print axioms A4CutoffPrimitiveClient.bump_nonneg
#print axioms A4CutoffPrimitiveClient.bump_eq_zero
#print axioms A4CutoffPrimitiveClient.bump_one
#print axioms A4CutoffPrimitiveClient.primitive_one
#print axioms A4CutoffPrimitiveClient.primitive_two
#print axioms A4CutoffPrimitiveClient.majorant_primitive

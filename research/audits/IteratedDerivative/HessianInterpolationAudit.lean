module

public import FunctionalInequalities.Analysis.IteratedDerivative.Interpolation
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Audit: local Hessian interpolation

Real client of `FunctionalInequalities/Analysis/IteratedDerivative/Interpolation.lean` (support for
Gilbarg–Trudinger, Classics 2001, Section 6.1 (6.8) and Theorem 6.2).
A nonquadratic concrete client: q(t) = t² + t⁴ on [-1,1].
The actual Hessian at zero is nonzero, and its central-difference remainder
at step 1/2 is nonzero. The Hölder exponent is the GT-relevant alpha=1/2. -/

@[expose] public section

noncomputable section
open Set Metric
namespace HessianInterpolationAudit
open FunctionalInequalities.Analysis


def q (t : ℝ) : ℝ := t ^ 2 + t ^ 4
def q1 (t : ℝ) : ℝ := 2 * t + 4 * t ^ 3
def q2 (t : ℝ) : ℝ := 2 + 12 * t ^ 2

def D : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
def B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := D.smulRight D

def qF1 (t : ℝ) : ℝ →L[ℝ] ℝ := q1 t • D
def qF2 (t : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := q2 t • B

private theorem q_deriv (t : ℝ) : HasDerivAt q (q1 t) t := by
  change HasDerivAt (fun y : ℝ => y ^ 2 + y ^ 4) (2 * t + 4 * t ^ 3) t
  convert ((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).pow 4) using 1
  all_goals first | rfl | (simp only [id_eq]; ring)
private theorem q1_deriv (t : ℝ) : HasDerivAt q1 (q2 t) t := by
  change HasDerivAt (fun y : ℝ => 2 * y + 4 * y ^ 3) (2 + 12 * t ^ 2) t
  convert ((hasDerivAt_id t).const_mul 2).add (((hasDerivAt_id t).pow 3).const_mul 4) using 1
  all_goals first | rfl | (simp only [id_eq]; ring)

theorem q_fderiv (t : ℝ) : HasFDerivAt q (qF1 t) t := by
  rw [hasFDerivAt_iff_hasDerivAt]
  simpa [qF1, D] using q_deriv t

theorem qF1_fderiv (t : ℝ) : HasFDerivAt qF1 (qF2 t) t := by
  have h := B.hasFDerivAt.comp t (q1_deriv t).hasFDerivAt
  have hfun : (fun x : ℝ => B (q1 x)) = qF1 := rfl
  have hmap : B.comp (ContinuousLinearMap.toSpanSingleton ℝ (q2 t)) = qF2 t := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp [qF2, B, D]
    ring
  change HasFDerivAt (fun x : ℝ => B (q1 x))
    (B.comp (ContinuousLinearMap.toSpanSingleton ℝ (q2 t))) t at h
  rw [hfun, hmap] at h
  exact h

/-- The norm of the actual bilinear Hessian at zero is computed directly by
operator norm bounds and evaluation, without changing any inherited instances. -/
theorem norm_qF2_zero : ‖qF2 0‖ = 2 := by
  apply le_antisymm
  · apply (qF2 0).opNorm_le_bound₂ (by norm_num : (0 : ℝ) ≤ 2)
    intro v w
    simp [qF2, q2, B, D, norm_mul, mul_assoc]
  · have h := ContinuousLinearMap.le_opNorm₂ (qF2 0) (1 : ℝ) (1 : ℝ)
    simpa [qF2, q2, B, D] using h

theorem q_value_bound : ∀ t ∈ closedBall (0 : ℝ) 1, |q t| ≤ 2 := by
  intro t ht
  have habs : |t| ≤ 1 := by simpa [mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using ht
  have hsq : t ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg t) habs 2
    simpa only [sq_abs, one_pow] using h
  have hfour : t ^ 4 ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hsq)]
  rw [q, abs_of_nonneg (by positivity)]
  linarith

theorem q_hessian_holder : ∀ t ∈ closedBall (0 : ℝ) 1,
    ‖qF2 t - qF2 0‖ ≤ 12 * ‖t - 0‖ ^ (1 / 2 : ℝ) := by
  intro t ht
  have habs : |t| ≤ 1 := by simpa [mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using ht
  have hp : t ^ 2 ≤ |t| ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg t) habs
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 2)
    simpa [Real.rpow_two, sq_abs] using h
  have hc : |q2 t - q2 0| ≤ 12 * |t| ^ (1 / 2 : ℝ) := by
    have he : q2 t - q2 0 = 12 * t ^ 2 := by dsimp [q2]; ring
    rw [he, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 12)
  apply (qF2 t - qF2 0).opNorm_le_bound₂ (by positivity : 0 ≤ 12 * ‖t - 0‖ ^ (1 / 2 : ℝ))
  intro v w
  have he : (qF2 t - qF2 0) v w = (q2 t - q2 0) * v * w := by
    simp only [qF2, sub_apply, smul_apply, B, D, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  rw [he, Real.norm_eq_abs, abs_mul, abs_mul]
  simpa only [sub_zero, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (abs_nonneg v)) (abs_nonneg w)

/-- The same constant works for every epsilon before the concrete polynomial
and its M=2, H=12 bounds are supplied; the Hessian norm equals 2 at the base point. -/
theorem quartic_interpolation (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ 2 ≤ C * 2 + ε * 12 := by
  obtain ⟨C, hC, h⟩ := exists_hessian_interpolation_constant (E := ℝ)
    (1 / 2 : ℝ) (by norm_num) ε hε
  have hp := h 1 (by norm_num) q qF1 qF2 q_fderiv qF1_fderiv 0 2 12 (by norm_num)
    q_value_bound q_hessian_holder
  refine ⟨C, hC, ?_⟩
  simpa [norm_qF2_zero] using hp

/-- At the concrete step 1/2 the central remainder is 1/8, so the client
is not a vanishing-remainder quadratic case. -/
theorem quartic_central_remainder :
    |q ((1 : ℝ) / 2) + q (-(1 : ℝ) / 2) - 2 * q 0 - ((1 : ℝ) / 2) ^ 2 * q2 0| = 1 / 8 := by
  norm_num [q, q2]

#print axioms quartic_interpolation
#print axioms quartic_central_remainder
end HessianInterpolationAudit

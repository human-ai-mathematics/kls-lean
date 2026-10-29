import FunctionalInequalities.Analysis.IteratedDerivative.Schauder.CoefficientCoordinates
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Audit: coefficient freezing

Real client of `FunctionalInequalities/Analysis/IteratedDerivative/Schauder/CoefficientFreezing.lean`
(support for Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001, Theorem 6.2, pp. 90–92, (6.17)–(6.19)).

The concrete data are one direction pair `v = w = 1` on `ℝ`, the variable, nonconstant coefficient
`a(t) = 1 + t`, and the nonquadratic function `q(t) = t² + t⁴` with its actual derivatives
`qF1`, `qF2` (the quartic producers are copied verbatim from `HessianInterpolationAudit`, which is
an audit client and cannot be imported). The Hölder exponent is `α = 1/2`.

* `q_hessian_pair_holder`, `a_holder`: pairwise `1/2`-Hölder caps `12` and `1` on `[-1/2, 1/2]`;
* `quartic_variable_absorption`: `exists_freezing_absorption_constants` applies with `M = 2`,
  `H = 12`, constants and radius chosen before the radius `r` and the evaluation points;
* `quartic_freezing_error_nonzero`: the freezing error at `r / 2` equals `-r - (3/2) r³ ≠ 0`, so the
  client is not a vanishing-error case.
-/

noncomputable section
open Set Metric
namespace CoefficientFreezingAudit
open FunctionalInequalities.Analysis

/-! ### Quartic producers (verbatim from `HessianInterpolationAudit`) -/

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

theorem q_value_bound : ∀ t ∈ closedBall (0 : ℝ) 1, |q t| ≤ 2 := by
  intro t ht
  have habs : |t| ≤ 1 := by simpa [mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using ht
  have hsq : t ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg t) habs 2
    simpa only [sq_abs, one_pow] using h
  have hfour : t ^ 4 ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hsq)]
  rw [q, abs_of_nonneg (by positivity)]
  linarith

/-! ### Coefficient-freezing client -/

def a (_ : Fin 1) (t : ℝ) : ℝ := 1 + t

def error (t : ℝ) : ℝ := freezingError a (fun _ => 1) (fun _ => 1) qF2 0 t

private theorem abs_sub_half {x y : ℝ} (hx : x ∈ closedBall 0 (1 / 2 : ℝ))
    (hy : y ∈ closedBall 0 (1 / 2 : ℝ)) : |x - y| ≤ 1 := by
  have hx' : |x| ≤ 1 / 2 := by simpa [mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hx
  have hy' : |y| ≤ 1 / 2 := by simpa [mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hy
  linarith [abs_sub x y]

private theorem linear_le_half_power {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ t ^ (1 / 2 : ℝ) := by
  have h := Real.rpow_le_rpow_of_exponent_ge' ht ht1
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  simpa only [Real.rpow_one] using h

/-- A pairwise Hölder cap on the actual quartic Hessian; the cap is nonzero. -/
theorem q_hessian_pair_holder : ∀ x ∈ closedBall (0 : ℝ) (1 / 2 : ℝ),
    ∀ y ∈ closedBall (0 : ℝ) (1 / 2 : ℝ),
      ‖qF2 x - qF2 y‖ ≤ 12 * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  intro x hx y hy
  have hx' : |x| ≤ 1 / 2 := by simpa [mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hx
  have hy' : |y| ≤ 1 / 2 := by simpa [mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hy
  have hsum : |x + y| ≤ 1 := by
    have h := norm_add_le x y
    simp only [Real.norm_eq_abs] at h
    linarith
  have hpow := linear_le_half_power (abs_nonneg (x - y)) (abs_sub_half hx hy)
  have hc : |q2 x - q2 y| ≤ 12 * |x - y| ^ (1 / 2 : ℝ) := by
    have he : q2 x - q2 y = 12 * ((x - y) * (x + y)) := by dsimp [q2]; ring
    rw [he, abs_mul, abs_mul]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (x - y))]
  apply (qF2 x - qF2 y).opNorm_le_bound₂ (by positivity : 0 ≤ 12 * ‖x - y‖ ^ (1 / 2 : ℝ))
  intro v w
  have he : (qF2 x - qF2 y) v w = (q2 x - q2 y) * v * w := by
    simp only [qF2, sub_apply, smul_apply, B, D, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  rw [he, Real.norm_eq_abs, abs_mul, abs_mul]
  simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (abs_nonneg v)) (abs_nonneg w)

theorem a_holder : ∀ i, ∀ x ∈ closedBall (0 : ℝ) (1 / 2 : ℝ),
    ∀ y ∈ closedBall (0 : ℝ) (1 / 2 : ℝ),
      |a i x - a i y| ≤ 1 * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  intro i x hx y hy
  have he : a i x - a i y = x - y := by dsimp [a]; ring
  rw [he, one_mul, Real.norm_eq_abs]
  exact linear_le_half_power (abs_nonneg _) (abs_sub_half hx hy)

/-- A real variable-coefficient, nonquadratic client of the small-radius theorem.
Constants and radius are chosen before the concrete evaluation points and r. -/
theorem quartic_variable_absorption (η : ℝ) (hη : 0 < η) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ ≤ 1 / 4 ∧
      ∀ r : ℝ, 0 < r → r ≤ ρ →
      (∀ x ∈ closedBall (0 : ℝ) r, r ^ 2 * |error x| ≤
        C * 2 + η * 12 * r ^ (2 + (1 / 2 : ℝ))) ∧
      (∀ x ∈ closedBall (0 : ℝ) r, ∀ y ∈ closedBall (0 : ℝ) r,
        r ^ (2 + (1 / 2 : ℝ)) * |error x - error y| ≤
          (C * 2 + η * 12 * r ^ (2 + (1 / 2 : ℝ))) * ‖x - y‖ ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, ρ, hC, hρ, _hρ1, h⟩ := exists_freezing_absorption_constants
    (E := ℝ) (ι := Fin 1) (1 / 2 : ℝ) (by norm_num) η hη 1 (by norm_num)
  refine ⟨C, min ρ (1 / 4), hC, lt_min hρ (by norm_num), min_le_right _ _, ?_⟩
  intro r hr hrρ
  have hr1 : r ≤ 1 / 4 := hrρ.trans (min_le_right _ _)
  have hs : closedBall (0 : ℝ) (2 * r) ⊆ closedBall 0 (1 / 2 : ℝ) :=
    closedBall_subset_closedBall (by linarith)
  have hs1 : closedBall (0 : ℝ) (2 * r) ⊆ closedBall 0 1 :=
    closedBall_subset_closedBall (by linarith)
  have hs0 : closedBall (0 : ℝ) r ⊆ closedBall 0 (1 / 2 : ℝ) :=
    closedBall_subset_closedBall (by linarith)
  exact h r hr (hrρ.trans (min_le_left _ _)) a (fun _ => 1) (fun _ => 1)
    q qF1 qF2 q_fderiv qF1_fderiv (by intro i; norm_num) (by intro i; norm_num)
    0 2 12 (by norm_num) (fun z hz => q_value_bound z (hs1 hz))
    (fun x hx y hy => q_hessian_pair_holder x (hs hx) y (hs hy))
    (fun i x hx y hy => a_holder i x (hs0 hx) y (hs0 hy))

/-- The frozen-principal error is nonzero at every positive half-radius. -/
theorem quartic_freezing_error_nonzero {r : ℝ} (hr : 0 < r) : error (r / 2) ≠ 0 := by
  have he : error (r / 2) = -r - (3 / 2 : ℝ) * r ^ 3 := by
    simp [error, freezingError, a, qF2, q2, B, D]
    ring
  rw [he]
  have hc : 0 < r ^ 3 := pow_pos hr 3
  linarith

#print axioms q_hessian_pair_holder
#print axioms a_holder
#print axioms quartic_variable_absorption
#print axioms quartic_freezing_error_nonzero
#print axioms FunctionalInequalities.Analysis.exists_freezing_absorption_constants
#print axioms FunctionalInequalities.Analysis.euclidean_freezing_bounds
#print axioms FunctionalInequalities.Analysis.freezing_bounds

end CoefficientFreezingAudit

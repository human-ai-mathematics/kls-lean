module

public import LevyStochCalc.Brownian.TaylorTwoModulus
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Second central differences and local Hessian interpolation

A radius-scaled core estimate supporting the interpolation step (6.8) of Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7),
Section 6.1, p. 89, and its use in Theorem 6.2, pp. 90–92.

* `central_difference_error`: the centered second difference differs from the actual Hessian
  quadratic term by twice the local Hessian oscillation times the squared step;
* `diagonal_interpolation`, `norm_bilinear_le_of_diagonal`, `hessian_interpolation`: interpolation
  of the actual Hessian in operator norm from value bounds and a local Hölder bound of the Hessian
  around the base point, via polarization of the symmetric second derivative;
* `exists_hessian_interpolation_constant`: the constant is chosen from `α` and `ε` before the
  radius,
  the function and the value and Hölder bounds.

Derivatives are given as global `HasFDerivAt` witnesses. This is not the full weighted-domain
interpolation (6.8)/(6.9), the constant-coefficient transform of Lemma 6.1, or a Schauder estimate.
The second-order Taylor remainder is the vendored
`LevyStochCalc.abs_sub_taylor_two_le_modulus_normed`
(LevyStochCalc, Christian Garry, Apache-2.0).
-/

@[expose] public section

noncomputable section
open Set Metric
namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The centered second difference differs from the actual quadratic Hessian term
by at most twice the local Hessian oscillation times the squared step. -/
theorem central_difference_error
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {x v : E} {h A : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hv : ‖v‖ = 1)
    (hosc : ∀ z ∈ closedBall x h, ‖f'' z - f'' x‖ ≤ A) :
    |f (x + h • v) + f (x - h • v) - 2 * f x - h ^ 2 * f'' x v v|
      ≤ 2 * A * h ^ 2 := by
  have hnp : ‖x + h • v - x‖ = h := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hh, hv]
  have hnm : ‖x - h • v - x‖ = h := by
    have he : x - h • v - x = -(h • v) := by abel
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh, hv, mul_one]
  have hs (y : E) (hy : ‖y - x‖ = h) :
      ∀ z ∈ segment ℝ x y, ‖f'' z - f'' x‖ ≤ A := by
    intro z hz
    apply hosc z
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le_of_mem_segment hz).trans hy.le
  have hp := LevyStochCalc.abs_sub_taylor_two_le_modulus_normed hA hf hf' (hs _ hnp)
  have hm := LevyStochCalc.abs_sub_taylor_two_le_modulus_normed hA hf hf' (hs _ hnm)
  rw [hnp] at hp
  rw [hnm] at hm
  simp only [add_sub_cancel_left, sub_sub_cancel_left, map_smul, map_neg,
    smul_apply, neg_apply, smul_eq_mul] at hp hm
  have hem : f (x - h • v) - f x - -(h * f' x v) - -(h * -(h * f'' x v v)) / 2 =
      f (x - h • v) - f x + h * f' x v - h * (h * f'' x v v) / 2 := by ring
  rw [hem] at hm
  have he : f (x + h • v) + f (x - h • v) - 2 * f x - h ^ 2 * f'' x v v =
      (f (x + h • v) - f x - h * f' x v - h * (h * f'' x v v) / 2) +
      (f (x - h • v) - f x + h * f' x v - h * (h * f'' x v v) / 2) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by nlinarith [hp, hm])

/-- Actual Hessian directional interpolation at any positive step, using only the
three sampled values and a local Hölder bound on the Hessian around the base point. -/
theorem diagonal_interpolation
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {x v : E} {h M H α : ℝ} (hh : 0 < h) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hv : ‖v‖ = 1)
    (hb : ∀ z ∈ closedBall x h, |f z| ≤ M)
    (hholder : ∀ z ∈ closedBall x h, ‖f'' z - f'' x‖ ≤ H * ‖z - x‖ ^ α) :
    |f'' x v v| ≤ 4 * M / h ^ 2 + 2 * H * h ^ α := by
  have herr := central_difference_error hf hf' hh (by positivity : 0 ≤ H * h ^ α) hv
    (fun z hz => (hholder z hz).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by simpa [mem_closedBall, dist_eq_norm] using hz) hα) hH))
  have hxp : x + h • v ∈ closedBall x h := by
    simp [mem_closedBall, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hh, hv]
  have hxm : x - h • v ∈ closedBall x h := by
    rw [mem_closedBall, dist_eq_norm]
    have he : x - h • v - x = -(h • v) := by abel
    simp [he, norm_smul, Real.norm_eq_abs, abs_of_pos hh, hv]
  have hx : x ∈ closedBall x h := mem_closedBall_self hh.le
  have hd : |f (x + h • v) + f (x - h • v) - 2 * f x| ≤ 4 * M := by
    calc
      _ ≤ |f (x + h • v)| + |f (x - h • v)| + |2 * f x| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 4 * M := by rw [abs_mul]; norm_num; linarith [hb _ hxp, hb _ hxm, hb _ hx]
  have hmain : h ^ 2 * |f'' x v v| ≤ 4 * M + 2 * H * h ^ α * h ^ 2 := by
    have htri : |h ^ 2 * f'' x v v| ≤
        |f (x + h • v) + f (x - h • v) - 2 * f x| +
        |f (x + h • v) + f (x - h • v) - 2 * f x - h ^ 2 * f'' x v v| := by
      calc
        _ = |(f (x + h • v) + f (x - h • v) - 2 * f x) -
          (f (x + h • v) + f (x - h • v) - 2 * f x - h ^ 2 * f'' x v v)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    rw [abs_mul, abs_sq] at htri
    nlinarith [hd, herr]
  have hs : 0 < h ^ 2 := sq_pos_of_pos hh
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    |f'' x v v| * h ^ 2 ≤ 4 * M + 2 * H * h ^ α * h ^ 2 := by nlinarith [hmain]
    _ = (4 * M / h ^ 2 + 2 * H * h ^ α) * h ^ 2 := by field_simp [hh.ne']

/-- A symmetric bilinear map is controlled in operator norm by twice the bound
of its quadratic form on unit vectors. Valid for arbitrary real normed spaces. -/
theorem norm_bilinear_le_of_diagonal
    (B : E →L[ℝ] E →L[ℝ] ℝ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hsym : ∀ v w, B v w = B w v)
    (hdiag : ∀ v, ‖v‖ = 1 → |B v v| ≤ Q) : ‖B‖ ≤ 2 * Q := by
  have hall (z : E) : |B z z| ≤ Q * ‖z‖ ^ 2 := by
    by_cases hz : z = 0
    · simp [hz]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hw : ‖‖z‖⁻¹ • z‖ = 1 := by simp [norm_smul, hn.ne']
    have hd := hdiag _ hw
    have he : B (‖z‖⁻¹ • z) (‖z‖⁻¹ • z) = ‖z‖⁻¹ * (‖z‖⁻¹ * B z z) := by
      simp [map_smul]
    rw [he, abs_mul, abs_mul, abs_inv, abs_of_pos hn] at hd
    calc
      |B z z| = ‖z‖ ^ 2 * (‖z‖⁻¹ * (‖z‖⁻¹ * |B z z|)) := by field_simp
      _ ≤ ‖z‖ ^ 2 * Q := mul_le_mul_of_nonneg_left hd (sq_nonneg ‖z‖)
      _ = Q * ‖z‖ ^ 2 := mul_comm _ _

  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  rw [Real.norm_eq_abs]
  have hp := hall (v + w)
  have hm := hall (v - w)
  have hnp : ‖v + w‖ ≤ 2 := by simpa only [hv, hw, one_add_one_eq_two] using norm_add_le v w
  have hnm : ‖v - w‖ ≤ 2 := by simpa only [hv, hw, one_add_one_eq_two] using norm_sub_le v w
  have hnp2 : ‖v + w‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (v + w)]
  have hnm2 : ‖v - w‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (v - w)]
  have he : 4 * B v w = B (v + w) (v + w) - B (v - w) (v - w) := by
    simp only [map_add, map_sub, add_apply, sub_apply]
    rw [hsym w v]
    ring
  have ht : |4 * B v w| ≤ |B (v + w) (v + w)| + |B (v - w) (v - w)| := by
    rw [he]
    exact abs_sub _ _
  rw [abs_mul] at ht
  rw [show |(4 : ℝ)| = 4 by norm_num] at ht
  nlinarith [mul_le_mul_of_nonneg_left hnp2 hQ, mul_le_mul_of_nonneg_left hnm2 hQ]

/-- Local interpolation of the actual Hessian in operator norm.
No estimate on that Hessian norm is assumed. -/
theorem hessian_interpolation
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {x : E} {h M H α : ℝ} (hh : 0 < h) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hb : ∀ z ∈ closedBall x h, |f z| ≤ M)
    (hholder : ∀ z ∈ closedBall x h, ‖f'' z - f'' x‖ ≤ H * ‖z - x‖ ^ α) :
    ‖f'' x‖ ≤ 8 * M / h ^ 2 + 4 * H * h ^ α := by
  have hM : 0 ≤ M := (abs_nonneg (f x)).trans (hb _ (mem_closedBall_self hh.le))
  have hn := norm_bilinear_le_of_diagonal (f'' x)
    (by positivity : 0 ≤ 4 * M / h ^ 2 + 2 * H * h ^ α)
    (second_derivative_symmetric hf (hf' x))
    (fun v hv => diagonal_interpolation hf hf' hh hH hα hv hb hholder)
  convert hn using 1
  ring

/-- The interpolation constant is chosen from alpha and epsilon before the radius,
function, value bound, or Hessian Hölder bound. The radius powers are explicit. -/
theorem exists_hessian_interpolation_constant (α : ℝ) (hα : 0 < α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (R : ℝ),
          0 < R →
            ∀ (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (f'' : E → E →L[ℝ] E →L[ℝ] ℝ),
              (∀ z, HasFDerivAt f (f' z) z) →
                (∀ z, HasFDerivAt f' (f'' z) z) →
                  ∀ (x : E) (M H : ℝ),
                    0 ≤ H →
                      (∀ z ∈ closedBall x R, |f z| ≤ M) →
                        (∀ z ∈ closedBall x R, ‖f'' z - f'' x‖ ≤ H * ‖z - x‖ ^ α) →
                          R ^ 2 * ‖f'' x‖ ≤ C * M + ε * H * R ^ (2 + α) := by
  let θ : ℝ := min 1 ((ε / 4) ^ α⁻¹)
  have hθ : 0 < θ := lt_min zero_lt_one (Real.rpow_pos_of_pos (by positivity) _)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθa : 4 * θ ^ α ≤ ε := by
    have ht := Real.rpow_le_rpow hθ.le (min_le_right 1 ((ε / 4) ^ α⁻¹)) hα.le
    rw [Real.rpow_inv_rpow (by positivity) hα.ne'] at ht
    linarith
  refine ⟨8 / θ ^ 2, by positivity, ?_⟩
  intro R hR f f' f'' hf hf' x M H hH hb hholder
  have hstep : 0 < θ * R := mul_pos hθ hR
  have hstepR : θ * R ≤ R := by nlinarith
  have hsub : closedBall x (θ * R) ⊆ closedBall x R := closedBall_subset_closedBall hstepR
  have hn :=
    hessian_interpolation hf hf' hstep hH hα.le (fun z hz => hb z (hsub hz))
      (fun z hz => hholder z (hsub hz))
  have hs : 0 < R ^ 2 := sq_pos_of_pos hR
  have he : R ^ (2 + α) = R ^ 2 * R ^ α := by rw [Real.rpow_add hR, Real.rpow_two]
  have hn' : R ^ 2 * ‖f'' x‖ ≤ (8 / θ ^ 2) * M + (4 * θ ^ α) * H * (R ^ 2 * R ^ α) := by
    calc
      _ ≤ R ^ 2 * (8 * M / (θ * R) ^ 2 + 4 * H * (θ * R) ^ α) :=
        mul_le_mul_of_nonneg_left hn hs.le
      _ = _ := by
        rw [Real.mul_rpow hθ.le hR.le]
        field_simp [hθ.ne', hR.ne']
  rw [he]
  exact
    hn'.trans
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hθa hH)
          (by positivity : 0 ≤ R ^ 2 * R ^ α)))


end FunctionalInequalities.Analysis

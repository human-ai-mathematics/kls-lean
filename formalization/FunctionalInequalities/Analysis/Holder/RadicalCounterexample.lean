module

public import FunctionalInequalities.Analysis.Holder.Closure
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Real.Sqrt

/-!
# A continuous radial source without a uniform `3/4`-Hölder cap

`not_holderOnWith_radical_ball_three_quarters`: in `EuclideanSpace ℝ (Fin n)` with `n ≥ 1`
(witnessed by an index `i : Fin n`), the continuous function `y ↦ √(4 - ‖y‖²)` satisfies no
`HolderOnWith C (3/4)` cap on `ball 0 2`, for any `C`. Along the ray through the basis vector `i`,
the value at radius `√(4 - t⁴)` is `t²`, while the distance to the boundary point is at most `t⁴`;
the exponent `3/4` would force `t² ≤ C t³`, which fails for small `t`.

This is a boundary-nonuniformity witness for the local-source setting of Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7),
Lemma 4.4, pp. 57–59: a continuous source, smooth inside the ball, need not carry the uniform
Hölder cap on the outer ball that the lemma assumes. It is not used as a hypothesis anywhere and
makes no claim about other exponents.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal
namespace FunctionalInequalities.Analysis

/-- The continuous radial source used in the local GT2001 Lemma4.4 client
has no uniform exponent-3/4 Hölder cap on the outer ball. -/
theorem not_holderOnWith_radical_ball_three_quarters {n : ℕ} (i : Fin n) (C : ℝ≥0) :
    ¬HolderOnWith C (3 / 4) (fun y : EuclideanSpace ℝ (Fin n) => Real.sqrt (4 - ‖y‖ ^ 2))
        (ball 0 2) := by
  intro h
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun y => Real.sqrt (4 - ‖y‖ ^ 2)
  let b := EuclideanSpace.basisFun (Fin n) ℝ i
  let t : ℝ := 1 / (2 * ((C : ℝ) + 1))
  let q : ℝ := Real.sqrt (4 - t ^ 4)
  let y : EuclideanSpace ℝ (Fin n) := q • b
  let p : EuclideanSpace ℝ (Fin n) := (2 : ℝ) • b
  have hb : ‖b‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i
  have ht0 : 0 < t := by dsimp [t]; positivity
  have hden : 0 < 2 * ((C : ℝ) + 1) := by positivity
  have htt : t * (2 * ((C : ℝ) + 1)) = 1 := by dsimp [t]; field_simp
  have hCt0 : 0 ≤ (C : ℝ) * t := mul_nonneg C.coe_nonneg ht0.le
  have ht1 : t ≤ 1 := by nlinarith
  have hCt : (C : ℝ) * t < 1 := by nlinarith
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1
  have ht4pos : 0 < t ^ 4 := pow_pos ht0 4
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqSq : q ^ 2 = 4 - t ^ 4 := Real.sq_sqrt (by linarith)
  have hq2 : q < 2 := by nlinarith
  have hδ0 : 0 ≤ 2 - q := by linarith
  have hδ : 2 - q ≤ t ^ 4 := by nlinarith [mul_nonneg hδ0 (by linarith : 0 ≤ q + 1)]
  have hny : ‖y‖ = q := by
    simp only [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0, hb, mul_one]
  have hnp : ‖p‖ = 2 := by norm_num [p, norm_smul, hb]
  have hfy : f y = t ^ 2 := by
    change Real.sqrt (4 - ‖y‖ ^ 2) = t ^ 2
    rw [hny, hqSq, show 4 - (4 - t ^ 4) = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg t)]
  have hfp : f p = 0 := by
    change Real.sqrt (4 - ‖p‖ ^ 2) = 0
    rw [hnp]
    norm_num
  have hd : dist y p = 2 - q := by
    rw [dist_eq_norm, show y - p = (q - 2) • b by dsimp [y, p]; rw [sub_smul]]
    rw [norm_smul, Real.norm_eq_abs, hb, mul_one, abs_of_nonpos (by linarith : q - 2 ≤ 0)]
    ring
  have hf : Continuous f :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2))
  have hc :=
    holderOnWith_closure_of_continuous (show HolderOnWith C (3 / 4) f (ball 0 2) from h) hf
  rw [closure_ball (0 : EuclideanSpace ℝ (Fin n)) (by norm_num : (2 : ℝ) ≠ 0)] at hc
  have hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 2 := by
    rw [mem_closedBall, dist_zero_right, hny]
    exact hq2.le
  have hp : p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 2 := by
    rw [mem_closedBall, dist_zero_right, hnp]
  have hh := hc.dist_le hy hp
  rw [hfy, hfp, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t), hd] at hh
  change t ^ 2 ≤ (C : ℝ) * (2 - q) ^ (3 / 4 : ℝ) at hh
  have hpow : (t ^ 4) ^ (3 / 4 : ℝ) = t ^ 3 := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_mul ht0.le]
    norm_num [Real.rpow_natCast]
  have hupper :=
    hh.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ0 hδ (by norm_num : (0 : ℝ) ≤ 3 / 4))
        C.coe_nonneg)
  rw [hpow] at hupper
  nlinarith [mul_pos (sq_pos_of_pos ht0) (sub_pos.mpr hCt)]
end FunctionalInequalities.Analysis

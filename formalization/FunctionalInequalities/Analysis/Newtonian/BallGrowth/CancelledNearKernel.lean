import FunctionalInequalities.Analysis.Newtonian.BallGrowth.NearKernel

/-!
# Near-field integral of a cancelled singular kernel

`cancelled_near_kernel_lintegral_le`: for a measure `ν` with `ν (ball x r) ≤ K r^d`, a kernel with
`|k y| ≤ A ‖y - x‖^(-d)` and `f` with `|f y - f x| ≤ H ‖y - x‖^α` on `ball x R` (`0 < α < d`),
`∫⁻_{ball x R} |k y (f y - f x)| dν ≤ A H K d / α · R^α`. This is the abstract form of the near-field
step in the Hölder estimate of Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), pp. 57–59.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The actual near cancelled-kernel integral in the Newtonian Holder estimate,
with a general measure having power ball growth at the center. -/
theorem cancelled_near_kernel_lintegral_le (ν : Measure E) (x : E)
    {K R alpha d A H : ℝ} (hK : 0 ≤ K) (hR : 0 < R) (ha : 0 < alpha)
    (had : alpha < d) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg : ∀ r : ℝ, 0 < r → ν (ball x r) ≤ ENNReal.ofReal (K*r^d))
    (k f : E → ℝ)
    (hk : ∀ y ∈ ball x R, y ≠ x → |k y| ≤ A*‖y-x‖^(-d))
    (hf : ∀ y ∈ ball x R, |f y-f x| ≤ H*‖y-x‖^alpha) :
    (∫⁻ y in ball x R, ENNReal.ofReal |k y*(f y-f x)| ∂ν) ≤
      ENNReal.ofReal (A*H*(K*d/alpha*R^alpha)) := by
  have hAH : 0 ≤ A*H := mul_nonneg hA hH
  have hb (y : E) (hy : y ∈ ball x R) :
      |k y*(f y-f x)| ≤ (A*H)*‖y-x‖^(alpha-d) := by
    by_cases he : y = x
    · subst y
      simp only [sub_self,mul_zero,abs_zero]
      exact mul_nonneg hAH (Real.rpow_nonneg (norm_nonneg _) _)
    have hn : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    have hp : ‖y-x‖^(-d)*‖y-x‖^alpha = ‖y-x‖^(alpha-d) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    rw [abs_mul]
    calc
      _ ≤ (A*‖y-x‖^(-d))*(H*‖y-x‖^alpha) :=
        mul_le_mul (hk y hy he) (hf y hy) (abs_nonneg _)
          (mul_nonneg hA (Real.rpow_nonneg (norm_nonneg _) _))
      _ = (A*H)*(‖y-x‖^(-d)*‖y-x‖^alpha) := by ring
      _ = _ := by rw [hp]
  have hm : Measurable (fun y : E => ENNReal.ofReal (‖y-x‖^(alpha-d))) :=
    ((continuous_id.sub continuous_const).norm.measurable.pow_const (alpha-d)).ennreal_ofReal
  calc
    _ ≤ ∫⁻ y in ball x R, ENNReal.ofReal ((A*H)*‖y-x‖^(alpha-d)) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact ENNReal.ofReal_le_ofReal (hb y hy)
    _ = ENNReal.ofReal (A*H)*(∫⁻ y in ball x R, ENNReal.ofReal (‖y-x‖^(alpha-d)) ∂ν) := by
      simp_rw [ENNReal.ofReal_mul hAH]
      exact lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal (A*H)*ENNReal.ofReal (K*d/alpha*R^alpha) :=
      by
      gcongr
      exact near_rpow_integral_le_of_ball_growth ν x hK hR ha had hg
    _ = _ := (ENNReal.ofReal_mul hAH).symm

end FunctionalInequalities.Analysis

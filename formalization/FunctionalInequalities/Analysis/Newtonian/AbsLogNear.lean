import FunctionalInequalities.Analysis.Newtonian.LogNear

/-!
# Absolute logarithmic near-field integrals

Under the ball growth `μ (ball x r) ≤ K r^d` (`d > 0`), for every `R > 0`:

* `lintegral_abs_log_norm_sub_le_of_ball_growth`: `∫⁻_{ball x R} |log ‖y - x‖| dμ ≤ K R^d (|log R| + 1/d)`;
* `integrableOn_log_norm_sub_ball_of_ball_growth`: `log ‖· - x‖` is integrable on `ball x R` with the
  same bound.

Used for the planar Newtonian kernel of Gilbarg–Trudinger, *Elliptic Partial Differential Equations
of Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

/-- Absolute logarithmic near integral. This is valid for every positive
radius, since log(R/r) bounds the variation from log R on r<R. -/
theorem lintegral_abs_log_norm_sub_le_of_ball_growth
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (x : E) {K R d : ℝ} (hK : 0 ≤ K) (hR : 0 < R) (hd : 0 < d)
    (hgrowth : ∀ r : ℝ, 0 < r → μ (ball x r) ≤ ENNReal.ofReal (K*r^d)) :
    (∫⁻ y in ball x R, ENNReal.ofReal |Real.log ‖y-x‖| ∂μ) ≤
      ENNReal.ofReal (K*R^d*(|Real.log R|+1/d)) := by
  have hP : 0 ≤ K*R^d := mul_nonneg hK (Real.rpow_nonneg hR.le _)
  have hratio := lintegral_log_ratio_le_of_ball_growth μ x hK hR hd hgrowth
  have hpoint : ∀ y ∈ ball x R, |Real.log ‖y-x‖| ≤ |Real.log R|+Real.log (R/‖y-x‖) := by
    intro y hy
    by_cases hy0 : ‖y-x‖=0
    · simp [hy0]
    · have hyr : 0 < ‖y-x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
      have hyrR : ‖y-x‖ < R := by simpa only [mem_ball,dist_eq_norm] using hy
      have hq : 0 ≤ Real.log (R/‖y-x‖) := Real.log_nonneg ((le_div_iff₀ hyr).mpr
        (by simpa only [one_mul] using hyrR.le))
      have he : Real.log ‖y-x‖ = Real.log R-Real.log (R/‖y-x‖) := by
        rw [Real.log_div hR.ne' hyr.ne']
        ring
      rw [he]
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hq])
  calc
    _ ≤ ∫⁻ y in ball x R, ENNReal.ofReal (|Real.log R|)+ENNReal.ofReal (Real.log (R/‖y-x‖)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact (ENNReal.ofReal_le_ofReal (hpoint y hy)).trans ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (|Real.log R|)*μ (ball x R)+
        ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R/‖y-x‖)) ∂μ := by
      rw [lintegral_add_left measurable_const,setLIntegral_const]
    _ ≤ ENNReal.ofReal (|Real.log R|)*ENNReal.ofReal (K*R^d)+ENNReal.ofReal (K*R^d/d) := by
      apply add_le_add _ hratio
      gcongr
      exact hgrowth R hR
    _ = _ := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _),← ENNReal.ofReal_add
        (mul_nonneg (abs_nonneg _) hP) (div_nonneg hP hd.le)]
      congr 1
      ring

/-- The logarithmic kernel is locally L1 under positive-dimensional ball
growth, with an explicit bound valid at every positive radius. -/
theorem integrableOn_log_norm_sub_ball_of_ball_growth
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (x : E) {K R d : ℝ} (hK : 0 ≤ K) (hR : 0 < R) (hd : 0 < d)
    (hgrowth : ∀ r : ℝ, 0 < r → μ (ball x r) ≤ ENNReal.ofReal (K*r^d)) :
    IntegrableOn (fun y => Real.log ‖y-x‖) (ball x R) μ ∧
    (∫ y in ball x R, |Real.log ‖y-x‖| ∂μ) ≤ K*R^d*(|Real.log R|+1/d) := by
  have hm : Measurable (fun y : E => Real.log ‖y-x‖) := by fun_prop
  have hb := lintegral_abs_log_norm_sub_le_of_ball_growth μ x hK hR hd hgrowth
  have hf : HasFiniteIntegral (fun y => Real.log ‖y-x‖) (μ.restrict (ball x R)) := by
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  have hi : Integrable (fun y => Real.log ‖y-x‖) (μ.restrict (ball x R)) :=
    ⟨hm.aestronglyMeasurable,hf⟩
  refine ⟨hi,?_⟩
  have he := integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable
  simp only [Real.norm_eq_abs,Real.enorm_eq_ofReal_abs] at he
  rw [he]
  have hC : 0 ≤ K*R^d*(|Real.log R|+1/d) := by positivity
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end FunctionalInequalities.Analysis

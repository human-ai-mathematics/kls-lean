module

public import FunctionalInequalities.Analysis.RieszPotential.Growth
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Logarithmic near-field integrals under ball growth

`lintegral_log_ratio_le_of_ball_growth`: if `μ (ball x r) ≤ K r^d` for all `r > 0`, with `d > 0`,
then
`∫⁻_{ball x R} log(R / ‖y - x‖) dμ ≤ K R^d / d` (layer-cake formula; the value of `Real.log` at `0`
is
included). The planar input for the logarithmic Newtonian kernel in Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Lemmas 4.1–4.4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

/-- Logarithmic near-field estimate from ball growth. The finite value of
Real.log at zero is included; no conclusion about a potential is assumed. -/
theorem lintegral_log_ratio_le_of_ball_growth {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (x : E) {K R d : ℝ} (hK : 0 ≤ K)
    (hR : 0 < R) (hd : 0 < d)
    (hgrowth : ∀ r : ℝ, 0 < r → μ (ball x r) ≤ ENNReal.ofReal (K * r ^ d)) :
    (∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / ‖y - x‖)) ∂μ) ≤
      ENNReal.ofReal (K * R ^ d / d) := by
  let ν := μ.restrict (ball x R)
  let g : E → ℝ := fun y => Real.log (R / ‖y - x‖)
  let C := K * R ^ d
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hgn : ∀ᵐ y ∂ν, 0 ≤ g y := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    by_cases hy0 : ‖y - x‖ = 0
    · simp [g, hy0]
    · have hyr : 0 < ‖y - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
      apply Real.log_nonneg
      apply (le_div_iff₀ hyr).mpr
      simpa only [one_mul] using
        (show ‖y - x‖ < R by simpa only [mem_ball, dist_eq_norm] using hy).le
  have htail : ∀ t : ℝ, 0 < t → ν {y | t < g y} ≤ ENNReal.ofReal (C * Real.exp ((-d) * t)) := by
    intro t ht
    have hset : {y | t < g y} ⊆ ball x (R * Real.exp (-t)) := by
      intro y hy
      have hyr : 0 < ‖y - x‖ := by
        by_contra h
        have hz : ‖y - x‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
        simp [g, hz] at hy
        linarith
      have he := (Real.lt_log_iff_exp_lt (div_pos hR hyr)).mp hy
      have hb : ‖y - x‖ < R / Real.exp t :=
        (lt_div_iff₀ (Real.exp_pos t)).mpr
          (by simpa only [mul_comm] using (lt_div_iff₀ hyr).mp he)
      rw [div_eq_mul_inv, ← Real.exp_neg] at hb
      simpa only [mem_ball, dist_eq_norm] using hb
    have hg := hgrowth (R * Real.exp (-t)) (mul_pos hR (Real.exp_pos _))
    have heq : K * (R * Real.exp (-t)) ^ d = C * Real.exp ((-d) * t) := by
      rw [Real.mul_rpow hR.le (Real.exp_nonneg _), ← Real.exp_mul]
      dsimp [C]
      rw [← mul_assoc]
      congr 2
      ring
    dsimp [ν]
    exact (Measure.restrict_apply_le (ball x R) _).trans ((measure_mono hset).trans (heq ▸ hg))
  have hi : IntegrableOn (fun t : ℝ => C * Real.exp ((-d) * t)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -d < 0) 0).const_mul C
  have hn : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ C * Real.exp ((-d) * t) :=
    Eventually.of_forall (fun _ => mul_nonneg hC (Real.exp_nonneg _))
  have hint :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C * Real.exp ((-d) * t))) = ENNReal.ofReal (C / d) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_const_mul,
      integral_exp_mul_Ioi (by linarith : -d < 0) 0]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
    rfl
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ν {y | t < g y} :=
      lintegral_eq_lintegral_meas_lt ν hgn hgm.aemeasurable
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C * Real.exp ((-d) * t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact htail t ht
    _ = _ := hint

end FunctionalInequalities.Analysis

import FunctionalInequalities.Analysis.Newtonian.BallGrowth.Layercake

/-!
# Far-field integrals of radial powers under ball growth

`far_rpow_integral_le_of_ball_growth`: if `ν (ball x r) ≤ K r^d` for all `r > 0`, `δ > 0` and `0 < d < b`,
then `∫⁻_{‖y - x‖ ≥ δ} ‖y - x‖^(-b) dν ≤ K b / (b - d) · δ^(d-b)`, from the bounded layer-cake estimate of
`Analysis/Newtonian/BallGrowth/Layercake.lean`. The coarse constant suffices for the far integral in the Hölder
estimate of Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Radial tail estimate from ball growth alone. This coarse constant suffices
for the far integral of the GT (2001), Lemma 4.4 Hölder estimate. -/
theorem far_rpow_integral_le_of_ball_growth (ν : Measure E) (x : E)
    {K delta d b : ℝ} (hK : 0 ≤ K) (hdelta : 0 < delta) (hd : 0 < d) (hdb : d < b)
    (hg : ∀ r : ℝ, 0 < r → ν (ball x r) ≤ ENNReal.ofReal (K*r^d)) :
    (∫⁻ y in {y : E | delta ≤ ‖y-x‖}, ENNReal.ofReal (‖y-x‖^(-b)) ∂ν) ≤
      ENNReal.ofReal (K*b/(b-d)*delta^(d-b)) := by
  have hb : 0 < b := hd.trans hdb
  let S : Set E := {y | delta ≤ ‖y-x‖}
  let σ := ν.restrict S
  have hS : MeasurableSet S := (isClosed_le continuous_const
    (continuous_id.sub continuous_const).norm).measurableSet
  have hm : AEMeasurable (fun y : E => ‖y-x‖^(-b)) σ :=
    ((continuous_id.sub continuous_const).norm.measurable.pow_const (-b)).aemeasurable
  have hnon : ∀ᵐ y ∂σ, 0 ≤ ‖y-x‖^(-b) := ae_of_all _ fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hcap : ∀ᵐ y ∂σ, ‖y-x‖^(-b) ≤ delta^(-b) := by
    filter_upwards [ae_restrict_mem hS] with y hy
    exact Real.rpow_le_rpow_of_nonpos hdelta hy (by linarith)
  have htail (t : ℝ) (ht : 0 < t) :
      σ {y | t < ‖y-x‖^(-b)} ≤ ENNReal.ofReal (K*t^(-(d/b))) := by
    let r := t^((-b)⁻¹)
    have hr : 0 < r := Real.rpow_pos_of_pos ht _
    have hset : {y : E | t < ‖y-x‖^(-b)} ⊆ ball x r := by
      intro y hy
      change t < ‖y-x‖^(-b) at hy
      have hn : 0 < ‖y-x‖ := by
        by_contra h
        have hz : ‖y-x‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
        rw [hz,Real.zero_rpow (by linarith : -b ≠ 0)] at hy
        linarith
      rw [mem_ball,dist_eq_norm]
      exact (Real.lt_rpow_inv_iff_of_neg hn ht (by linarith : -b < 0)).mpr hy
    have he : (-b)⁻¹*d = -(d/b) := by rw [inv_neg,div_eq_mul_inv];ring
    have hgr := hg r hr
    dsimp only [r] at hgr
    rw [← Real.rpow_mul ht.le,he] at hgr
    exact (Measure.restrict_apply_le S _).trans ((measure_mono hset).trans hgr)
  have hs : d/b < 1 := (div_lt_one hb).mpr hdb
  have bound := lintegral_le_of_bounded_rpow_superlevels σ hm hnon hK hs
    (Real.rpow_pos_of_pos hdelta (-b)) hcap htail
  have hp : (delta^(-b))^(1-d/b) = delta^(d-b) := by
    rw [← Real.rpow_mul hdelta.le]
    congr 1
    field_simp [hb.ne']
    ring
  have he : K*(delta^(-b))^(1-d/b)/(1-d/b) = K*b/(b-d)*delta^(d-b) := by
    rw [hp]
    have he' : 1-d/b = (b-d)/b := by field_simp [hb.ne']
    rw [he']
    field_simp [hb.ne',(sub_pos.mpr hdb).ne']
  simpa only [he] using bound

end FunctionalInequalities.Analysis

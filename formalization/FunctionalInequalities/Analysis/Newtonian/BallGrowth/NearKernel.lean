module

public import FunctionalInequalities.Analysis.RieszPotential.Growth

/-!
# Near-field integrals of radial powers under ball growth

`near_rpow_integral_le_of_ball_growth`: if `ν (ball x r) ≤ K r^d` for all `r > 0` and `0 < α < d`,
then
`∫⁻_{ball x R} ‖y - x‖^(α-d) dν ≤ K d / α · R^α`. A restatement of the Riesz-potential growth bound
of
`Analysis/RieszPotential/Growth.lean` in the form used for the near-field part of the Newtonian
kernel estimates of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), Lemmas 4.1–4.4.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

theorem near_rpow_integral_le_of_ball_growth (ν : Measure E) (x : E) {K R alpha d : ℝ}
    (hK : 0 ≤ K) (hR : 0 < R) (ha : 0 < alpha) (had : alpha < d)
    (hg : ∀ r : ℝ, 0 < r → ν (ball x r) ≤ ENNReal.ofReal (K * r ^ d)) :
    (∫⁻ y in ball x R, ENNReal.ofReal (‖y - x‖ ^ (alpha - d)) ∂ν) ≤
      ENNReal.ofReal (K * d / alpha * R ^ alpha) := by
  have hs : ∀ᵐ y ∂ν.restrict (ball x R), y ∈ closedBall x R :=
    (ae_restrict_mem measurableSet_ball).mono (fun _ h => ball_subset_closedBall h)
  have hgr : ∀ r : ℝ, 0 < r → (ν.restrict (ball x R)) (ball x r) ≤ ENNReal.ofReal (K * r ^ d) := by
    intro r hr
    rw [Measure.restrict_apply measurableSet_ball]
    exact (measure_mono inter_subset_left).trans (hg r hr)
  have h :=
    FunctionalInequalities.Analysis.lintegral_norm_sub_rpow_neg_le_of_ae_closedBall_ball_growth
      (ν.restrict (ball x R)) x hK hR (sub_pos.mpr had) (by linarith : d - alpha < d) hs hgr
  have h1 : -(d - alpha) = alpha - d := by ring
  have h2 : d - (d - alpha) = alpha := by ring
  simpa only [h1, h2] using h

end FunctionalInequalities.Analysis

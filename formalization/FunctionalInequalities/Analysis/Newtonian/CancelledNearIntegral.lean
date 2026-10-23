import FunctionalInequalities.Analysis.Newtonian.CancelledNearKernel

/-!
# Integrability of a cancelled singular kernel near its centre

`cancelled_near_kernel_integrable_integral_le`: under the hypotheses of
`cancelled_near_kernel_lintegral_le` and a.e.-measurability of the product, `y ↦ k y (f y - f x)` is
integrable on `ball x R` and `|∫_{ball x R} k (f - f x) dν| ≤ A H K d / α · R^α`. Integrability is
derived, not assumed. Used for the near-field part of Lemma 4.4 of Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7).
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Integrability and the actual scalar integral estimate from the near
Hölder cancellation bound. No integrability conclusion is assumed. -/
theorem cancelled_near_kernel_integrable_integral_le (ν : Measure E) (x : E)
    {K R alpha d A H : ℝ} (hK : 0 ≤ K) (hR : 0 < R) (ha : 0 < alpha)
    (had : alpha < d) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg : ∀ r : ℝ, 0 < r → ν (ball x r) ≤ ENNReal.ofReal (K*r^d))
    (k f : E → ℝ)
    (hm : AEMeasurable (fun y => k y*(f y-f x)) (ν.restrict (ball x R)))
    (hk : ∀ y ∈ ball x R, y ≠ x → |k y| ≤ A*‖y-x‖^(-d))
    (hf : ∀ y ∈ ball x R, |f y-f x| ≤ H*‖y-x‖^alpha) :
    IntegrableOn (fun y => k y*(f y-f x)) (ball x R) ν ∧
      |∫ y in ball x R, k y*(f y-f x) ∂ν| ≤ A*H*(K*d/alpha*R^alpha) := by
  have hb := cancelled_near_kernel_lintegral_le ν x hK hR ha had hA hH hg k f hk hf
  have hc : 0 ≤ A*H*(K*d/alpha*R^alpha) := by
    have hd : 0 < d := ha.trans had
    positivity
  have hfinite : HasFiniteIntegral (fun y => k y*(f y-f x))
      (ν.restrict (ball x R)) := by
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  refine ⟨⟨hm.aestronglyMeasurable, hfinite⟩, ?_⟩
  have hn := norm_integral_le_lintegral_norm (μ := ν.restrict (ball x R))
    (fun y => k y*(f y-f x))
  simp only [Real.norm_eq_abs] at hn
  exact hn.trans (by
    simpa only [ENNReal.toReal_ofReal hc] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hb)

end FunctionalInequalities.Analysis

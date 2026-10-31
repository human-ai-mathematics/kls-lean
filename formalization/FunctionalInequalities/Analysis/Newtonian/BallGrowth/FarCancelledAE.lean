module

public import FunctionalInequalities.Analysis.Newtonian.BallGrowth.FarKernel

/-!
# Far-field integral of a cancelled kernel difference

`cancelled_far_kernel_integrable_integral_le_of_ae`: for a measure `ν` with `ν (ball x r) ≤ K r^d`,
`δ > 0`,
`0 < α < 1`, and a.e. bounds `|k₁ y - k₂ y| ≤ A δ ‖y - x‖^(-d-1)` and `|f y - f x| ≤ H ‖y - x‖^α` on
`{‖y - x‖ ≥ δ}`, the product `(k₁ - k₂)(f - f x)` is integrable there with
`|∫| ≤ A H K (d + 1 - α) / (1 - α) · δ^α`. This is the radial mechanism of the far integral in the
proof
of Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics
2001 (ISBN 3-540-41160-7); no Newtonian kernel bound is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The actual far scalar integral after the kernel-difference and Hölder
bounds almost everywhere on the restricted measure, with all integrability derived. This supplies
the radial mechanism of
I6 in GT (2001), Lemma 4.4; Newtonian kernel bounds are not asserted here. -/
theorem cancelled_far_kernel_integrable_integral_le_of_ae (ν : Measure E) (x : E)
    {K delta alpha d A H : ℝ} (hK : 0 ≤ K) (hdelta : 0 < delta) (_ha : 0 < alpha)
    (ha1 : alpha < 1) (hd : 0 < d) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg : ∀ r : ℝ, 0 < r → ν (ball x r) ≤ ENNReal.ofReal (K * r ^ d)) (k₁ k₂ f : E → ℝ)
    (hm :
      AEMeasurable (fun y => (k₁ y - k₂ y) * (f y - f x)) (ν.restrict {y | delta ≤ ‖y - x‖}))
    (hk :
      ∀ᵐ y ∂(ν.restrict {y | delta ≤ ‖y - x‖}), |k₁ y - k₂ y| ≤ A * delta * ‖y - x‖ ^ (-d - 1))
    (hf : ∀ᵐ y ∂(ν.restrict {y | delta ≤ ‖y - x‖}), |f y - f x| ≤ H * ‖y - x‖ ^ alpha) :
    IntegrableOn (fun y => (k₁ y - k₂ y) * (f y - f x)) {y | delta ≤ ‖y - x‖} ν ∧
      |∫ y in {y | delta ≤ ‖y - x‖}, (k₁ y - k₂ y) * (f y - f x) ∂ν| ≤
        A * H * (K * (d + 1 - alpha) / (1 - alpha)) * delta ^ alpha := by
  let b := d + 1 - alpha
  have hdb : d < b := by dsimp [b]; linarith
  have hnon : 0 ≤ A * H * delta := by positivity
  have hS : MeasurableSet {y : E | delta ≤ ‖y - x‖} :=
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).measurableSet
  have hb (y : E) (hy : delta ≤ ‖y - x‖) (hky : |k₁ y - k₂ y| ≤ A * delta * ‖y - x‖ ^ (-d - 1))
    (hfy : |f y - f x| ≤ H * ‖y - x‖ ^ alpha) :
    |(k₁ y - k₂ y) * (f y - f x)| ≤ (A * H * delta) * ‖y - x‖ ^ (-b) := by
    have hn : 0 < ‖y - x‖ := hdelta.trans_le hy
    have hp : ‖y - x‖ ^ (-d - 1) * ‖y - x‖ ^ alpha = ‖y - x‖ ^ (-b) := by
      rw [← Real.rpow_add hn]
      congr 1
      dsimp [b]
      ring
    rw [abs_mul]
    calc
      _ ≤ (A * delta * ‖y - x‖ ^ (-d - 1)) * (H * ‖y - x‖ ^ alpha) :=
        mul_le_mul hky hfy (abs_nonneg _) (by positivity)
      _ = (A * H * delta) * (‖y - x‖ ^ (-d - 1) * ‖y - x‖ ^ alpha) := by ring
      _ = _ := by rw [hp]
  have hpm : Measurable (fun y : E => ENNReal.ofReal (‖y - x‖ ^ (-b))) :=
    ((continuous_id.sub continuous_const).norm.measurable.pow_const (-b)).ennreal_ofReal
  have hpower :
    (A * H * delta) * (K * b / (b - d) * delta ^ (d - b)) =
      A * H * (K * (d + 1 - alpha) / (1 - alpha)) * delta ^ alpha := by
    have h1 : b - d = 1 - alpha := by dsimp [b]; ring
    have h2 : delta * delta ^ (d - b) = delta ^ alpha := by
      calc
        _ = delta ^ (1 : ℝ) * delta ^ (d - b) := by rw [Real.rpow_one]
        _ = delta ^ (1 + (d - b)) := (Real.rpow_add hdelta _ _).symm
        _ = _ := by congr 1; dsimp [b]; ring
    calc
      _ = (A * H) * (K * b / (b - d)) * (delta * delta ^ (d - b)) := by ring
      _ = _ := by rw [h2, h1]
  have bound :
    (∫⁻ y in {y | delta ≤ ‖y - x‖}, ENNReal.ofReal |(k₁ y - k₂ y) * (f y - f x)| ∂ν) ≤
      ENNReal.ofReal (A * H * (K * (d + 1 - alpha) / (1 - alpha)) * delta ^ alpha) := by
    calc
      _ ≤ ∫⁻ y in {y | delta ≤ ‖y - x‖}, ENNReal.ofReal ((A * H * delta) * ‖y - x‖ ^ (-b)) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hS, hk, hf] with y hy hky hfy
        exact ENNReal.ofReal_le_ofReal (hb y hy hky hfy)
      _ =
          ENNReal.ofReal (A * H * delta) *
            (∫⁻ y in {y | delta ≤ ‖y - x‖}, ENNReal.ofReal (‖y - x‖ ^ (-b)) ∂ν) := by
        simp_rw [ENNReal.ofReal_mul hnon]
        exact lintegral_const_mul _ hpm
      _ ≤ ENNReal.ofReal (A * H * delta) * ENNReal.ofReal (K * b / (b - d) * delta ^ (d - b)) := by
        gcongr
        exact far_rpow_integral_le_of_ball_growth ν x hK hdelta hd hdb hg
      _ = _ := by rw [← ENNReal.ofReal_mul hnon, hpower]
  have hc : 0 ≤ A * H * (K * (d + 1 - alpha) / (1 - alpha)) * delta ^ alpha := by
    have hp : 0 < d + 1 - alpha := by linarith
    positivity
  have hfinite :
    HasFiniteIntegral (fun y => (k₁ y - k₂ y) * (f y - f x))
      (ν.restrict {y | delta ≤ ‖y - x‖}) := by
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact lt_of_le_of_lt bound ENNReal.ofReal_lt_top
  refine ⟨⟨hm.aestronglyMeasurable, hfinite⟩, ?_⟩
  have hn :=
    norm_integral_le_lintegral_norm (μ := ν.restrict {y | delta ≤ ‖y - x‖})
      (fun y => (k₁ y - k₂ y) * (f y - f x))
  simp only [Real.norm_eq_abs] at hn
  exact
    hn.trans
      (by
        simpa only [ENNReal.toReal_ofReal hc] using
          ENNReal.toReal_mono ENNReal.ofReal_ne_top bound)

end FunctionalInequalities.Analysis

import FunctionalInequalities.Analysis.Harmonic.CompactReproduction
import FunctionalInequalities.Analysis.Cutoff.LocalRegularity

/-!
# Local reproduction and smoothness of harmonic functions on the unit ball

Supporting the harmonic part of the interior estimates of Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Theorem 4.6, p. 60, and the
derivative estimates for harmonic functions, Theorem 2.10 / (2.31). For `n ≥ 2` (including `n = 2`)
and `h ∈ C²(B₂)` with `Δh = 0` on `B₂ = ball 0 2`:

* `harmonicBump n`, `harmonicLocalization n h = harmonicBump n * h`: a fixed smooth cutoff equal to
  `1` on `ball 0 (3/2)` and supported in `closedBall 0 (7/4)`, and the compactly supported
  localization of `h`;
* `harmonicLocalization_properties`: the localization is `C²` on `ℝⁿ`, compactly supported, and
  agrees with `h` near every point of `ball 0 (3/2)`;
* `local_harmonic_reproduces`: on `B₁`, `h = annularKernel n (1/8) ⋆ harmonicLocalization n h`, with
  the fixed kernel radius `ε = 1/8`;
* `local_harmonic_contDiffOn`: `h` is `C^∞` on `B₁`.

The reproducing formula is derived from `compact_harmonic_reproduces`; it is not a premise. Only
the unit-scale statement on `B₁ ⊂ B₂` is proved here; scaling is in `Harmonic/BallHolder`.
-/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Convolution
namespace FunctionalInequalities.Analysis

/-- The fixed smooth cutoff of the harmonic localization: equal to `1` on `ball 0 (3/2)` and
supported in `closedBall 0 (7/4)`. -/
def harmonicBump (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨3 / 2, 7 / 4, by norm_num, by norm_num⟩

/-- The compactly supported localization `harmonicBump n * h` of a function `h` on `B₂`. -/
def harmonicLocalization (n : ℕ) (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ := fun y => harmonicBump n y * h y

/-- The localization of a `C²` function on `B₂` is globally `C²`, compactly supported, and has the
same germ as `h` at every point of `ball 0 (3/2)`. -/
theorem harmonicLocalization_properties {n : ℕ} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ContDiffOn ℝ 2 h (ball (0 : EuclideanSpace ℝ (Fin n)) 2)) :
    ContDiff ℝ 2 (harmonicLocalization n h) ∧ HasCompactSupport (harmonicLocalization n h) ∧
    ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (3 / 2),
      harmonicLocalization n h =ᶠ[𝓝 x] h := by
  have hsub : closedBall (0 : EuclideanSpace ℝ (Fin n)) (harmonicBump n).rOut ⊆ ball 0 2 := by
    intro y hy
    have hy' : dist y 0 ≤ (7 : ℝ) / 4 := hy
    show dist y 0 < 2
    linarith
  have hc := bump_mul_local (harmonicBump n) isOpen_ball hh hsub
  refine ⟨hc.1, hc.2.1, ?_⟩
  intro x hx
  have hx' : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (harmonicBump n).rIn := hx
  filter_upwards [(harmonicBump n).eventuallyEq_one_of_mem_ball hx'] with y hy
  change harmonicBump n y * h y = h y
  simp only [hy, Pi.one_apply, one_mul]

/-- The unit-scale harmonic representation on `B₁`, derived from `h ∈ C²(B₂)` and `Δh = 0` on `B₂`,
with the fixed dimension-dependent kernel `Kₙ = Δ(truncated Γ at radius 1/8)`. -/
theorem local_harmonic_reproduces {n : ℕ} (hn : 2 ≤ n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ContDiffOn ℝ 2 h (ball (0 : EuclideanSpace ℝ (Fin n)) 2))
    (hLap : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, Laplacian.laplacian h y = 0) :
    ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      h x = (annularKernel n (1 / 8) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        harmonicLocalization n h) x := by
  intro x hx
  have hp := harmonicLocalization_properties hh
  have hxnorm : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
  have hxinner : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (3 / 2) := by
    simpa only [mem_ball, dist_zero_right] using (show ‖x‖ < (3 : ℝ) / 2 by linarith)
  have hzero (y : EuclideanSpace ℝ (Fin n)) (hxy : ‖x - y‖ < 2 * (1 / 8 : ℝ)) :
      Laplacian.laplacian (harmonicLocalization n h) y = 0 := by
    have htri : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
      calc
        ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
        _ = ‖x - y‖ + ‖x‖ := by rw [norm_sub_rev]
    have hyinner : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (3 / 2) := by
      rw [mem_ball, dist_zero_right]
      linarith
    have hyouter : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2 :=
      ball_subset_ball (by norm_num) hyinner
    exact ((InnerProductSpace.laplacian_congr_nhds (hp.2.2 y hyinner)).self_of_nhds).trans
      (hLap y hyouter)
  have hrepro := (compact_harmonic_reproduces hn (by norm_num : (0 : ℝ) < 1 / 8)
    hp.1 hp.2.1 x hzero).2
  have hconv : (∫ y, annularKernel n (1 / 8) (x - y) * harmonicLocalization n h y) =
      (annularKernel n (1 / 8) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        harmonicLocalization n h) x := by
    have ht := integral_sub_left_eq_self
      (fun t => annularKernel n (1 / 8) t * harmonicLocalization n h (x - t)) volume x
    simpa only [sub_sub_cancel, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using ht
  exact ((hp.2.2 x hxinner).self_of_nhds.symm.trans hrepro).trans hconv

/-- Local harmonic smoothing: if `h` is only `C²` on `B₂` and `Δh = 0` there, then `h` is `C^∞` on
`B₁`. Smoothness follows from the derived representation. -/
theorem local_harmonic_contDiffOn {n : ℕ} (hn : 2 ≤ n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ContDiffOn ℝ 2 h (ball (0 : EuclideanSpace ℝ (Fin n)) 2))
    (hLap : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, Laplacian.laplacian h y = 0) :
    ContDiffOn ℝ ∞ h (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have hp := harmonicLocalization_properties hh
  have hsm : ContDiff ℝ ∞ (annularKernel n (1 / 8) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      harmonicLocalization n h) :=
    (hasCompactSupport_annularKernel hn (by norm_num : (0 : ℝ) < 1 / 8)).contDiff_convolution_left
      _ (contDiff_annularKernel hn (by norm_num)) hp.1.continuous.locallyIntegrable
  exact hsm.contDiffOn.congr (local_harmonic_reproduces hn hh hLap)
end FunctionalInequalities.Analysis

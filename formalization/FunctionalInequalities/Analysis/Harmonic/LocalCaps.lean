import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
import FunctionalInequalities.Analysis.Harmonic.LocalReproduction
import FunctionalInequalities.Analysis.Convolution.DerivativeCaps

/-!
# Interior derivative bounds for harmonic functions on the unit ball

The unit-scale form of the derivative estimates for harmonic functions in Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7),
Theorem 2.10 / (2.31), through order three, as used for the harmonic part of Theorem 4.6, p. 60:

* `harmonicLocalization_bound`: the cutoff localization does not increase a value bound `|h| ≤ M`
  on `B₂`;
* `local_harmonic_derivative_caps`: for `n ≥ 2` there are positive constants `C1, C2, C3`, depending
  only on `n` and chosen before `h`, such that every `h ∈ C²(B₂)` with `Δh = 0` and `|h| ≤ M` on `B₂`
  is `C^∞` on `B₁` and satisfies `‖Dh‖ ≤ C1 M`, `‖D²h‖ ≤ C2 M`, `‖D³h‖ ≤ C3 M` on `B₁` (nested Fréchet
  derivatives, operator norm).

The bounds come from the reproducing formula `h = annularKernel n (1/8) ⋆ harmonicLocalization n h`
on `B₁` and `convolution_derivative_caps`. The constants are not GT's explicit `(n|α|/d)^|α|`; only
their existence and dependence on `n` alone are proved.
-/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Convolution
namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms

/-- The outer cutoff does not increase a value bound on `B₂`.
Both the range `[0, 1]` of the cutoff and its support inside `B₂` are used. -/
theorem harmonicLocalization_bound {n : ℕ} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, |h y| ≤ M) :
    ∀ y, |harmonicLocalization n h y| ≤ M := by
  intro y
  by_cases hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2
  · change |harmonicBump n y * h y| ≤ M
    rw [abs_mul, abs_of_nonneg (harmonicBump n).nonneg]
    exact (mul_le_mul_of_nonneg_right (harmonicBump n).le_one (abs_nonneg (h y))).trans
      (by simpa only [one_mul] using hb y hy)
  · have hdist : (harmonicBump n).rOut ≤ dist y 0 := by
      have hd : 2 ≤ dist y 0 := le_of_not_gt hy
      change (7 : ℝ) / 4 ≤ dist y 0
      linarith
    change |harmonicBump n y * h y| ≤ M
    rw [(harmonicBump n).zero_of_le_dist hdist, zero_mul, abs_zero]
    exact hM

/-- Harmonic `C^∞` regularity and uniform first, second and third derivative bounds on `B₁`.
`n ≥ 2` includes the logarithmic planar fundamental solution. The constants depend only on `n` and
are selected before `h`. -/
theorem local_harmonic_derivative_caps {n : ℕ} (hn : 2 ≤ n) :
    ∃ C1 C2 C3 : ℝ, 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧
      ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ 2 h (ball (0 : EuclideanSpace ℝ (Fin n)) 2) →
      (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, Laplacian.laplacian h y = 0) →
      ∀ (M : ℝ), (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, |h y| ≤ M) →
      ContDiffOn ℝ ∞ h (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ‖fderiv ℝ h x‖ ≤ C1 * M ∧
        ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C2 * M ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ h)) x‖ ≤ C3 * M := by
  have hK4 : ContDiff ℝ 4 (annularKernel n (1 / 8)) :=
    (contDiff_annularKernel hn (by norm_num : (0 : ℝ) < 1 / 8)).of_le (by
      change (↑(4 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C1, C2, C3, hC1, hC2, hC3, hcap⟩ := convolution_derivative_caps hK4
    (hasCompactSupport_annularKernel hn (by norm_num : (0 : ℝ) < 1 / 8))
  refine ⟨C1, C2, C3, hC1, hC2, hC3, ?_⟩
  intro h hh hLap M hb
  have hM : 0 ≤ M := (abs_nonneg (h 0)).trans (hb 0 (by simp))
  have hp := harmonicLocalization_properties hh
  have hbump := harmonicLocalization_bound hM hb
  refine ⟨local_harmonic_contDiffOn hn hh hLap, ?_⟩
  intro x hx
  have heq : h =ᶠ[𝓝 x] (annularKernel n (1 / 8) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      harmonicLocalization n h) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact local_harmonic_reproduces hn hh hLap y hy
  have hd1 := heq.fderiv_eq (𝕜 := ℝ)
  have hd2 := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hd3 := ((heq.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  rw [hd1, hd2, hd3]
  exact hcap _ hp.1.continuous.locallyIntegrable M hM hbump x
end FunctionalInequalities.Analysis

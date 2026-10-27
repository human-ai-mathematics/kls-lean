import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
import FunctionalInequalities.Analysis.Harmonic.LocalCaps
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hessian Lipschitz and Hölder bounds for harmonic functions on the unit ball

The unit-scale harmonic part of the interior Hölder estimate of Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Theorem 4.6, p. 60, from
the derivative estimates of Theorem 2.10 / (2.31). For `n ≥ 2`, `h ∈ C²(B₂)` with `Δh = 0` and
`|h| ≤ M` on `B₂`:

* `local_harmonic_hessian_lipschitz`: `‖D²h‖ ≤ C2 M` on `B₁` and
  `‖D²h x - D²h y‖ ≤ C3 M ‖x - y‖` for `x, y ∈ B₁`, by the mean-value inequality on the convex ball
  and the third-derivative cap;
* `local_harmonic_hessian_holder`: one constant `C`, depending only on `n` and chosen before the
  exponent, works for every `0 < α < 1`: `‖D²h‖ ≤ C M` and `‖D²h x - D²h y‖ ≤ C M ‖x - y‖^α` on
  `B₁`. Since `B₁` has diameter `2`, `‖x - y‖ ≤ 2 ‖x - y‖^α` there.

Only the harmonic contribution to GT Theorem 4.6 is proved here; the Newtonian-potential estimate
(GT Theorem 4.5) is `Newtonian/CompactPoisson`, and the two are not combined in this module.
-/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms

-- These are exactly the standard CLM instances at the concrete Hessian type.

/-- Uniform Hessian point and Lipschitz bounds on `B₁` for harmonic functions on `B₂`.
The dimension constants are chosen before the source and its value bound. -/
theorem local_harmonic_hessian_lipschitz {n : ℕ} (hn : 2 ≤ n) :
    ∃ C2 C3 : ℝ, 0 < C2 ∧ 0 < C3 ∧
      ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ 2 h (ball (0 : EuclideanSpace ℝ (Fin n)) 2) →
      (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, Laplacian.laplacian h y = 0) →
      ∀ (M : ℝ), (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, |h y| ≤ M) →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C2 * M) ∧
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ h) y‖ ≤ C3 * M * ‖x - y‖ := by
  obtain ⟨C1, C2, C3, _, hC2, hC3, hcaps⟩ := local_harmonic_derivative_caps hn
  refine ⟨C2, C3, hC2, hC3, ?_⟩
  intro h hh hLap M hb
  have hs := hcaps h hh hLap M hb
  have hs4 : ContDiffOn ℝ 4 h (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := hs.1.of_le (by
    change (↑(4 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hd : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ h)) x := by
    intro x hx
    have ha : ContDiffAt ℝ 4 h x := hs4.contDiffAt (isOpen_ball.mem_nhds hx)
    exact ((ha.fderiv_right (m := 3) (by norm_num)).fderiv_right (m := 2)
      (by norm_num)).differentiableAt (by norm_num)
  refine ⟨fun x hx => (hs.2 x hx).2.1, ?_⟩
  intro x hx y hy
  exact (convex_ball (0 : EuclideanSpace ℝ (Fin n)) 1).norm_image_sub_le_of_norm_fderiv_le
    hd (fun z hz => (hs.2 z hz).2.2) hy hx

/-- Hölder Hessian control on `B₁` for every exponent `0 < α < 1`. The common
constant depends only on `n`; `α` is selected before the harmonic source. -/
theorem local_harmonic_hessian_holder {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α < 1 →
      ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ 2 h (ball (0 : EuclideanSpace ℝ (Fin n)) 2) →
      (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, Laplacian.laplacian h y = 0) →
      ∀ (M : ℝ), (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, |h y| ≤ M) →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C * M) ∧
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ h) y‖ ≤ C * M * ‖x - y‖ ^ α := by
  obtain ⟨C2, C3, hC2, hC3, hcaps⟩ := local_harmonic_hessian_lipschitz hn
  refine ⟨max C2 (2 * C3), hC2.trans_le (le_max_left _ _), ?_⟩
  intro α hα hα1 h hh hLap M hb
  have hM : 0 ≤ M := (abs_nonneg (h 0)).trans (hb 0 (by simp))
  have hs := hcaps h hh hLap M hb
  refine ⟨fun x hx => (hs.1 x hx).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hM), ?_⟩
  intro x hx y hy
  have hd : ‖x - y‖ ≤ 2 := by
    have hx' : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    have hy' : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
    exact (norm_sub_le x y).trans (by linarith)
  have hp : ‖x - y‖ ≤ 2 * ‖x - y‖ ^ α := by
    by_cases ht : ‖x - y‖ ≤ 1
    · have hself := Real.self_le_rpow_of_le_one (norm_nonneg (x - y)) ht hα1.le
      exact hself.trans (by nlinarith [Real.rpow_nonneg (norm_nonneg (x - y)) α])
    · have hpow : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (le_of_not_ge ht) hα.le
      nlinarith
  calc
    ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ h) y‖ ≤ C3 * M * ‖x - y‖ := hs.2 x hx y hy
    _ ≤ C3 * M * (2 * ‖x - y‖ ^ α) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hC3.le hM)
    _ = (2 * C3) * M * ‖x - y‖ ^ α := by ring
    _ ≤ max C2 (2 * C3) * M * ‖x - y‖ ^ α :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM)
        (Real.rpow_nonneg (norm_nonneg _) α)
end FunctionalInequalities.Analysis

module

public import FunctionalInequalities.Analysis.IteratedDerivative.Schauder.CoefficientCoordinates
public import FunctionalInequalities.Analysis.Newtonian.Schauder.CompactPoisson

/-!
# Coefficient freezing fed by the compact Poisson estimates

Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001
(ISBN 3-540-41160-7): Theorem 4.5 (p. 60) supplies global Hessian sup and Hölder caps of a compactly
supported `C²` solution of `Δu = f`, and the coordinate coefficient-freezing residual estimate of
Theorem 6.2, (6.17)–(6.19), consumes exactly those produced caps. This is a bridge between the two
results; it is neither the interior Theorem 4.6 nor the constant-coefficient transformation of
Lemma 6.1.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal
namespace FunctionalInequalities.Analysis

/-- Theorem 4.5 produces both Hessian inputs of the coordinate freezing residual estimate
`euclidean_freezing_bounds`; the `n ≥ 2`, `0 < α < 1`, compact `C²` class, open support ball and
diameter `2R` normalisation of Theorem 4.5 are retained. -/
theorem compactPoisson_freezing_bounds {n : ℕ} (hn : 2 ≤ n) {α : ℝ≥0}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ) (H : ℝ≥0),
      ContDiff ℝ 2 u → tsupport u ⊆ ball c R → (∀ x, Laplacian.laplacian u x = f x) →
      (∀ y ∈ ball c R, |f y| ≤ M) → HolderOnWith H α f (ball c R) →
      ∀ (d : EuclideanSpace ℝ (Fin n)) (r K : ℝ), 0 ≤ r → 0 ≤ K →
      ∀ a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i j, ∀ x ∈ closedBall d r, ∀ y ∈ closedBall d r,
        |a i j x - a i j y| ≤ K * ‖x - y‖ ^ (α : ℝ)) →
      (∀ x ∈ closedBall d r, |euclideanError a u d x| ≤
        (n : ℝ) ^ 2 * K * r ^ (α : ℝ) * (C * (M + (2 * R) ^ (α : ℝ) * H))) ∧
      (∀ x ∈ closedBall d r, ∀ y ∈ closedBall d r,
        |euclideanError a u d x - euclideanError a u d y| ≤
          (n : ℝ) ^ 2 * K * (C * (M + (2 * R) ^ (α : ℝ) * H) +
            r ^ (α : ℝ) * (C * ((2 * R) ^ (-(α : ℝ)) * M + H))) * ‖x - y‖ ^ (α : ℝ)) := by
  obtain ⟨C, hC, hP⟩ := FunctionalInequalities.Analysis.compactPoisson_hessian_estimates hn hα0 hα1
  refine ⟨C, hC, ?_⟩
  intro c R hR u f M H hu hs hΔ hM hH d r K hr hK a ha
  have hp := hP c R hR u f M H hu hs hΔ hM hH
  exact euclidean_freezing_bounds hr α.coe_nonneg hK ha
    (fun x _ => hp.2.1 x) (fun x _ y _ => hp.2.2.1 x y)

end FunctionalInequalities.Analysis

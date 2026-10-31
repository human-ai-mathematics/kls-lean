module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.DifferenceQuotient

/-!
# Audit: difference quotients of the regular moment potential

Real client of `exists_regular_moment_potential_difference_quotient_equations` (Letwin,
arXiv:2607.24164v1, Lemma 2.2
support, strong class; Gilbarg–Trudinger, Classics 2001, Lemma 17.16 precursor). From the original
inputs only
(smooth `κ`-uniformly convex `W`, compact convex `K` with nonempty interior, normalized isotropic
law `1_K e^{−W}`)
it extracts one potential `u` with its gradient transport and `C²`, and, on the ball of radius `1`,
the local
log-determinant Hessian equations of its unit-direction finite differences for every nonzero step
`|q| ≤ 1/2`,
with the same averaged-inverse coefficients and a cap and Hölder constant independent of the
direction and the step.
It claims no regularity gain, lower ellipticity or merely convex Lemma 2.2 statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff ENNReal NNReal

namespace CEKDifferenceQuotientAudit
open FunctionalInequalities FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein

theorem unit_ball_unit_direction_equations {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 2 u ∧ ∃ α C L : ℝ≥0, 0 < α ∧ α < 1 ∧ 0 < C ∧ 0 < L ∧
        ∀ (v : EuclideanSpace ℝ (Fin n)), ‖v‖ = 1 → ∀ q : ℝ, q ≠ 0 → |q| ≤ 1 / 2 →
          ContDiff ℝ 2 (differenceQuotient u (q • v) q) ∧
          (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2), ∀ i j,
            |averagedInverse (hessianMatrix u) (q • v) x i j| ≤ L) ∧
          ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2),
            (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j *
              hessianMatrix (differenceQuotient u (q • v) q) x j i) + differenceQuotient u (q • v)
                q x =
              (W (gradient u (x + q • v)) - W (gradient u x)) / q := by
    obtain ⟨u, hmap, hC2, h⟩ :=
      exists_regular_moment_potential_difference_quotient_equations hn hκ hK hKc hKint
        hW hstrong μ hμ hiso
    obtain ⟨α, C, L, hα, hα1, hC, hL, hq⟩ := h 1 one_pos
    refine ⟨u, hmap, hC2, α, C, L, hα, hα1, hC, hL, fun v hv q hq0 hq1 => ?_⟩
    obtain ⟨h1, -, h3, h4⟩ := hq v q hq0 (by rw [hv, mul_one]; linarith)
    exact ⟨h1, h3, h4⟩

end CEKDifferenceQuotientAudit

#print axioms CEKDifferenceQuotientAudit.unit_ball_unit_direction_equations
#print axioms
  FunctionalInequalities.Analysis.exists_regular_moment_potential_difference_quotient_equations
#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_uniform_differenceQuotient_equations
#print axioms FunctionalInequalities.Analysis.logDet_quotient_eq_averagedInverse

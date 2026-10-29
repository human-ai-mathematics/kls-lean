import FunctionalInequalities.KLS.CEK.MomentRegularity.Ellipticity
import FunctionalInequalities.Analysis.BakryEmery.GradientForcing.Elliptic

/-!
# Audit: uniformly elliptic difference-quotient equations of the regular moment potential

Real clients for the strong regular class of Letwin, arXiv:2607.24164v1, Lemma 2.2 (smooth
`κ`-uniformly convex `W`, compact convex `K` with nonempty interior, normalized isotropic law
`1_K e^{−W}`), supporting Gilbarg–Trudinger, Classics 2001, Lemma 17.16 and Theorem 6.2.

* `unit_ball_unit_direction_elliptic_equations` calls
  `exists_regular_moment_potential_elliptic_quotient_equations` from the original inputs only. It
  extracts one potential `u` with its normalization, gradient transport, `C²`, pointwise positive
  definite Hessian, log-determinant equation and Hessian upper bound, and on the ball of radius
  `1/2`, for every unit direction and nonzero step `|q| ≤ 1/2`, the finite-difference equations with the
  same averaged-inverse coefficients, their entry cap and positive quadratic lower and upper bounds,
  all independent of the direction and the step.
* `unit_ball_unit_direction_linearized_equations` calls
  `exists_regular_moment_potential_holder_hessian_inverse` once and feeds the same `u` (its global
  `16/κ`-Lipschitz gradient and local Hölder Hessian) to
  `BakryEmery.exists_uniform_linearized_differenceQuotient_equations`, producing the linear equation
  `Σᵢⱼ aᵢⱼ ∂ⱼᵢw + w = Σᵢ bᵢ ∂ᵢw` for the finite differences `w`, with uniformly elliptic `a` and
  bounded, Hölder segment forcing coefficients `b`.

Neither client claims a Schauder estimate, a regularity gain or a merely convex Lemma 2.2 statement.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff ENNReal NNReal

namespace CEKEllipticityAudit
open FunctionalInequalities FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein

theorem unit_ball_unit_direction_elliptic_equations {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 2 u ∧
      (∀ x, (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      ∃ (L : ℝ≥0) (a b : ℝ), 0 < L ∧ 0 < a ∧ 0 < b ∧
        ∀ (v : EuclideanSpace ℝ (Fin n)), ‖v‖ = 1 → ∀ q : ℝ, q ≠ 0 → |q| ≤ 1 / 2 →
          ContDiff ℝ 2 (differenceQuotient u (q • v) q) ∧
          (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2), ∀ i j,
            |averagedInverse (hessianMatrix u) (q • v) x i j| ≤ L) ∧
          (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2),
            ∀ ξ : EuclideanSpace ℝ (Fin n),
              a * ‖ξ‖ ^ 2 ≤
                  (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j * ξ i * ξ j) ∧
                (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j * ξ i * ξ j) ≤
                  b * ‖ξ‖ ^ 2) ∧
          ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2),
            (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j *
              hessianMatrix (differenceQuotient u (q • v) q) x j i) +
                differenceQuotient u (q • v) q x =
              (W (gradient u (x + q • v)) - W (gradient u x)) / q := by
  obtain ⟨u, hnorm, hmap, hC2, hEvery, h⟩ :=
    exists_regular_moment_potential_elliptic_quotient_equations hn hκ hK hKc hKint hW hstrong
      μ hμ hiso
  obtain ⟨_α, _C, L, a, b, _hα, _hα1, _hC, hL, ha, hb, hq⟩ := h 1 one_pos
  refine ⟨u, hnorm, hmap, hC2, hEvery, L, a, b, hL, ha, hb, fun v hv q hq0 hq1 => ?_⟩
  obtain ⟨h1, -, h3, h4, h5⟩ := hq v q hq0 (by rw [hv, mul_one]; linarith)
  exact ⟨h1, h3, h4, h5⟩

theorem unit_ball_unit_direction_linearized_equations {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
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
      ContDiff ℝ 2 u ∧
      ∃ (B : ℝ≥0) (a b : ℝ), 0 < B ∧ 0 < a ∧ 0 < b ∧
        ∀ (v : EuclideanSpace ℝ (Fin n)), ‖v‖ = 1 → ∀ q : ℝ, q ≠ 0 → |q| ≤ 1 / 2 →
          (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2),
            ∀ ξ : EuclideanSpace ℝ (Fin n),
              a * ‖ξ‖ ^ 2 ≤
                  (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j * ξ i * ξ j) ∧
                (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j * ξ i * ξ j) ≤
                  b * ‖ξ‖ ^ 2) ∧
          (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2), ∀ i,
            |segmentForcingCoefficient W (gradient u) (q • v) x i| ≤ B) ∧
          ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2),
            (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j *
              hessianMatrix (differenceQuotient u (q • v) q) x j i) +
                differenceQuotient u (q • v) q x =
              ∑ i, segmentForcingCoefficient W (gradient u) (q • v) x i *
                fderiv ℝ (differenceQuotient u (q • v) q) x
                  (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  obtain ⟨u, _L, _LF, _T, _hconv, _hl, _hnorm, hmap, _hC1, hG, _hF, _hd, _hT,
      hC2, _hHc, hEvery, hLocal, _he, _Ψ, _hleft, _hΨ, _hΨc⟩ :=
    exists_regular_moment_potential_holder_hessian_inverse hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨α, C, hα, hα1, _hC, hH⟩ := hLocal 2 (by norm_num)
  have hsubset : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ ball 0 2 :=
    closedBall_subset_ball (by norm_num)
  have hhol (i j : Fin n) : HolderOnWith C α (fun x => hessianMatrix u x i j)
      (closedBall 0 1) := (HolderWith.restrict_iff.mp (hH i j)).mono hsubset
  obtain ⟨_L, B, _Cb, a, b, _hL, hB, _hCb, ha, hb, hlin⟩ :=
    exists_uniform_linearized_differenceQuotient_equations u W hC2 (hW.of_le (by norm_cast))
      0 (1 / 2) 1 (by norm_num) _ hG.lipschitzOnWith C α hα hα1.le hhol
      (fun x _ => (hEvery x).1) (fun x _ => by linarith [(hEvery x).2.1])
  refine ⟨u, hmap, hC2, B, a, b, hB, ha, hb, fun v hv q hq0 hq1 => ?_⟩
  obtain ⟨-, -, -, hell, hbcap, -, heq⟩ := hlin v q hq0 (by rw [hv, mul_one]; linarith)
  exact ⟨hell, hbcap, heq⟩

end CEKEllipticityAudit

#print axioms CEKEllipticityAudit.unit_ball_unit_direction_elliptic_equations
#print axioms CEKEllipticityAudit.unit_ball_unit_direction_linearized_equations
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_potential_elliptic_quotient_equations
#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_uniform_elliptic_differenceQuotient_equations
#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_uniform_linearized_differenceQuotient_equations
#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_uniform_segmentForcingCoefficient_bounds
#print axioms FunctionalInequalities.Analysis.BakryEmery.linearized_differenceQuotient_equation
#print axioms FunctionalInequalities.Analysis.exists_uniform_averagedInverse_ellipticity
#print axioms FunctionalInequalities.Analysis.exists_uniform_quadratic_bounds

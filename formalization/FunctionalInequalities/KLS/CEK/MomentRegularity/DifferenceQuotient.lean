module

public import FunctionalInequalities.Analysis.BakryEmery.DifferenceQuotient
public import FunctionalInequalities.KLS.CEK.MomentRegularity.Inverse

/-!
# Difference quotients of the regular moment potential

The strong regular class of Letwin, arXiv:2607.24164v1, Lemma 2.2 (smooth `κ`-uniformly convex `W`,
compact convex `K` with nonempty interior, normalized isotropic law `1_K e^{−W}`). One call of
`exists_regular_moment_potential_holder_hessian_inverse` supplies `u`, its transport, `C²` Hessian,
positive definiteness, log-determinant
equation and local Hölder modulus; the finite differences use exactly that `u` and `W`. This proves
no
regularity gain, lower ellipticity or merely convex Lemma 2.2 statement.
-/

@[expose] public section

noncomputable section
namespace FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein BakryEmery
open Set MeasureTheory Metric
open scoped ContDiff NNReal ENNReal BigOperators

/-- **Same-witness difference-quotient equations** (Letwin, arXiv:2607.24164v1, Lemma 2.2 support,
strong class;
Gilbarg–Trudinger Lemma 17.16 precursor). One call of
`exists_regular_moment_potential_holder_hessian_inverse` gives a
potential `u` with its actual gradient transport and `C²`; on every ball, its scalar-step finite
differences satisfy
local log-determinant Hessian equations with the same averaged-inverse coefficients, whose cap and
Hölder constant are
uniform in the direction and the nonzero step. No regularity gain is claimed. -/
theorem exists_regular_moment_potential_difference_quotient_equations
    {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y-(κ / 2)*‖y‖^2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 2 u ∧
      ∀ R : ℝ, 0 < R → ∃ α C L : ℝ≥0, 0 < α ∧ α < 1 ∧ 0 < C ∧ 0 < L ∧
        ∀ (v : EuclideanSpace ℝ (Fin n)) (q : ℝ), q ≠ 0 →
          R / 2+|q| * ‖v‖ ≤ R →
          ContDiff ℝ 2 (differenceQuotient u (q • v) q) ∧
          (∀ i j, HolderOnWith ((n : ℝ≥0) ^ 2 * L ^ 2 * C) α
            (fun x => averagedInverse (hessianMatrix u) (q • v) x i j)
              (closedBall 0 (R / 2))) ∧
          (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R / 2), ∀ i j,
            |averagedInverse (hessianMatrix u) (q • v) x i j| ≤ L) ∧
          ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R / 2),
            (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j *
              hessianMatrix (differenceQuotient u (q • v) q) x j i) + differenceQuotient u (q • v)
                q x =
              (W (gradient u (x + q • v))-W (gradient u x)) / q := by
    obtain
      ⟨u, _L, _LF, _T, _hconv, _hl, _hnorm, hmap, _hC1, _hG, _hF, _hd, _hT, hC2, _hHc,
        hEvery, hLocal, _he, _Ψ, _hleft, _hΨ, _hΨc⟩ :=
      exists_regular_moment_potential_holder_hessian_inverse hn hκ hK hKc hKint hW
        hstrong μ hμ hiso
    refine ⟨u, hmap, hC2, ?_⟩
    intro R hR
    obtain ⟨α, C, hα, hα1, hC, hH⟩ := hLocal (R + 1) (by linarith)
    have hsubset : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ ball 0 (R + 1) :=
      closedBall_subset_ball (by linarith)
    have hhol (i j : Fin n) :
      HolderOnWith C α (fun x => hessianMatrix u x i j) (closedBall 0 R) :=
      (HolderWith.restrict_iff.mp (hH i j)).mono hsubset
    obtain ⟨L, hL, hcoeff⟩ :=
      exists_uniform_differenceQuotient_equations u W hC2 0 (R / 2) R (by linarith) C α
        hα hhol (fun x _ => (hEvery x).1) (fun x _ => by linarith [(hEvery x).2.1])
    exact ⟨α, C, L, hα, hα1, hC, hL, hcoeff⟩

end FunctionalInequalities.Analysis

import FunctionalInequalities.Analysis.BakryEmery.HessianEllipticity
import FunctionalInequalities.KLS.CEK.MomentRegularity.Inverse

/-!
# Uniformly elliptic difference-quotient equations of the regular moment potential

The strong regular class of Letwin, arXiv:2607.24164v1, Lemma 2.2 (smooth `κ`-uniformly convex `W`,
compact convex `K` with nonempty interior, normalized isotropic law `1_K e^{−W}`), through the
precursor of Gilbarg–Trudinger, Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464, for
the interior Schauder estimate, Theorem 6.2, pp. 90–92.

`exists_regular_moment_potential_elliptic_quotient_equations`: one call of
`exists_regular_moment_potential_holder_hessian_inverse` supplies a potential `u` with
`∫ e^{−u} = 1`, gradient transport onto `μ`, `C²` regularity, and at every point a positive
definite Hessian, the equation `log det Hess u = −u + W (∇u)` and the bound `Hess u ≤ (16/κ) I`.
On every ball `closedBall 0 (R/2)` its scalar-step finite differences satisfy the local
log-determinant equations with the same `averagedInverse` coefficients, whose entry cap, Hölder
constant and positive quadratic lower and upper ellipticity constants are uniform in the direction
and the nonzero step.

The ellipticity constants are derived at this same `u`; there is no second producer call or
replacement witness. This is quantitative ellipticity support only: no Schauder estimate,
regularity gain, or merely convex Lemma 2.2 statement is proved.
-/
noncomputable section
namespace FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein BakryEmery
open Set MeasureTheory Metric
open scoped ContDiff NNReal ENNReal BigOperators

/-- **Same-witness elliptic difference-quotient equations** (Letwin, arXiv:2607.24164v1, Lemma 2.2
support, strong class; Gilbarg–Trudinger Lemma 17.16 precursor). The normalization, transport,
`C²` regularity, pointwise positive definiteness, log-determinant equation and Hessian upper bound
of one regular moment potential `u` are retained together with, on every ball, uniformly elliptic
finite-difference equations of the same `u`. This is quantitative ellipticity support, not a
Schauder estimate or a regularity gain. -/
theorem exists_regular_moment_potential_elliptic_quotient_equations
    {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y-(κ/2)*‖y‖^2))
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
        Real.log (hessianMatrix u x).det = -u x+W (gradient u x) ∧
        ((16/κ) • (1 : Matrix (Fin n) (Fin n) ℝ)-hessianMatrix u x).PosSemidef) ∧
      ∀ R : ℝ, 0 < R → ∃ (α C L : ℝ≥0) (a b : ℝ),
        0 < α ∧ α < 1 ∧ 0 < C ∧ 0 < L ∧ 0 < a ∧ 0 < b ∧
        ∀ (v : EuclideanSpace ℝ (Fin n)) (q : ℝ), q ≠ 0 → R/2+|q| * ‖v‖ ≤ R →
          ContDiff ℝ 2 (differenceQuotient u (q • v) q) ∧
          (∀ i j, HolderOnWith ((n : ℝ≥0)^2*L^2*C) α
            (fun x => averagedInverse (hessianMatrix u) (q • v) x i j) (closedBall 0 (R/2))) ∧
          (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R/2), ∀ i j,
            |averagedInverse (hessianMatrix u) (q • v) x i j| ≤ L) ∧
          (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R/2),
            ∀ ξ : EuclideanSpace ℝ (Fin n),
              a*‖ξ‖^2 ≤ (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j*ξ i*ξ j) ∧
              (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j*ξ i*ξ j) ≤ b*‖ξ‖^2) ∧
          ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R/2),
            (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j *
              hessianMatrix (differenceQuotient u (q • v) q) x j i) +
              differenceQuotient u (q • v) q x =
              (W (gradient u (x+q • v))-W (gradient u x))/q := by
  obtain ⟨u,_uL,_LF,_T,_hconv,_hl,hnorm,hmap,_hC1,_hG,_hF,_hd,_hT,
      hC2,_hHc,hEvery,hLocal,_he,_Ψ,_hleft,_hΨ,_hΨc⟩ :=
    exists_regular_moment_potential_holder_hessian_inverse hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u,hnorm,hmap,hC2,hEvery,?_⟩
  intro R hR
  obtain ⟨α,C,hα,hα1,hC,hH⟩ := hLocal (R+1) (by linarith)
  have hsubset : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ ball 0 (R+1) :=
    closedBall_subset_ball (by linarith)
  have hhol (i j : Fin n) : HolderOnWith C α (fun x => hessianMatrix u x i j)
      (closedBall 0 R) := (HolderWith.restrict_iff.mp (hH i j)).mono hsubset
  obtain ⟨L,a,b,hL,ha,hb,hbounds⟩ := exists_uniform_elliptic_differenceQuotient_equations
    u W hC2 0 (R/2) R (by linarith) C α hα hhol
    (fun x _ => (hEvery x).1) (fun x _ => by linarith [(hEvery x).2.1])
  exact ⟨α,C,L,a,b,hα,hα1,hC,hL,ha,hb,hbounds⟩

end FunctionalInequalities.Analysis

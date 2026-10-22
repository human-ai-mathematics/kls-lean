import FunctionalInequalities.KLS.CEK.MomentRegularity.Inverse

/-!
# Audit: the gradient inverse of the regular moment potential

Real client of `exists_regular_moment_potential_holder_hessian_inverse` (Letwin, arXiv:2607.24164v1, Lemma 2.2 support, strong
class). From the original inputs only — smooth `κ`-uniformly convex `W`, compact convex `K` with nonempty interior and the
normalized isotropic law `1_K e^{−W}` — it extracts one potential `u` with the gradient transport `(∇u)_* e^{−u} = μ`, `C²`
regularity, positive definite Hessian at every point, a homeomorphism `∇u : ℝⁿ ≃ₜ interior K`, and a `C¹` inverse `Ψ` of `∇u` on
`interior K` that is also a left inverse on all of `ℝⁿ`. It does not claim the full smooth lemma, Schauder/`C^∞` regularity or the
merely convex source class.
-/

noncomputable section

open MeasureTheory Set Metric Matrix
open scoped ContDiff ENNReal NNReal

namespace LetwinGradientInverseAudit
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

section RegularMomentPotential
variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- One potential transports the tilted law to `μ`, is `C²` with positive definite Hessian everywhere, its gradient is a
homeomorphism onto `interior K`, and it has a `C¹` inverse on `interior K` that is a left inverse of `∇u` — all for the same `u`. -/
theorem regular_moment_potential_transport_c2_gradient_inverse :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 2 u ∧ (∀ x, (hessianMatrix u x).PosDef) ∧
      (∃ e : EuclideanSpace ℝ (Fin n) ≃ₜ interior K, ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = gradient u x) ∧
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧ (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ 1 Ψ (interior K) := by
  obtain ⟨u, _L, _LF, _T, _hconv, _hl, _hnorm, hmap, _hC1, _hG, _hF, _hd, _hT, hC2, _hHc, hEvery, _hHol, he, Ψ, hleft, hΨ, hΨc⟩ :=
    exists_regular_moment_potential_holder_hessian_inverse hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, hmap, hC2, fun x => (hEvery x).1, he, Ψ, hleft, hΨ, hΨc⟩

end RegularMomentPotential
end LetwinGradientInverseAudit

#print axioms LetwinGradientInverseAudit.regular_moment_potential_transport_c2_gradient_inverse

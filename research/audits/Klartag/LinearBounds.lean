module

public import FunctionalInequalities.KLS.Klartag.LinearBounds

/-! Klartag arXiv:1309.2767v1, Lemma 2.3, for `C¹` potentials (the paper allows any Lipschitz
convex `ψ`; `C¹` is an added restriction): for `L, ε > 0` there are `α, β, γ > 0` such that every
convex, `C¹`, `L`-Lipschitz `ψ` that is centered (7) (`∫ e^{-ψ} = 1`, `∫ x e^{-ψ(x)} dx = 0` for
an additive Haar measure) and satisfies (13) with `ε` obeys `α|x| - β ≤ ψ(x) ≤ L|x| + γ`. The
intermediate statements (15), (17)–(18) and (19)–(20) are audited separately. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace

namespace KlartagAudit

theorem lemma_2_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : Measure E)
    [m.IsAddHaarMeasure] {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧
      ∀ ψ : E → ℝ, ConvexOn ℝ Set.univ ψ → ContDiff ℝ 1 ψ → LipschitzWith (Real.toNNReal L) ψ →
        ∫ x, Real.exp (-ψ x) ∂m = 1 → ∫ x, Real.exp (-ψ x) • x ∂m = 0 →
        (∀ θ : E, ‖θ‖ = 1 → ε ≤ ∫ x, |⟪gradient ψ x, θ⟫| * Real.exp (-ψ x) ∂m) →
        ∀ x, α * ‖x‖ - β ≤ ψ x ∧ ψ x ≤ L * ‖x‖ + γ :=
  FunctionalInequalities.Probability.MomentMeasure.exists_two_sided_linear_bounds m hL hε

#print axioms lemma_2_3

end KlartagAudit

#print axioms FunctionalInequalities.Probability.integrable_norm_pow_mul_exp_neg_mul_norm
#print axioms FunctionalInequalities.Probability.Line.lintegral_Ioi_deriv_mul_exp_neg_eq
#print axioms FunctionalInequalities.Probability.Line.lintegral_abs_deriv_mul_exp_neg_eq
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.exists_lintegral_line_abs_inner_gradient
#print axioms FunctionalInequalities.Probability.MomentMeasure.lintegral_line_half_ge
#print axioms FunctionalInequalities.Probability.MomentMeasure.abs_le_of_mem_levelSet_of_centered
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_two_sided_linear_bounds

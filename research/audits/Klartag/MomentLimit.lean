import FunctionalInequalities.KLS.Klartag.MomentLimit

/-! Klartag arXiv:1309.2767v1, Proposition 2.1, for convex `L`-Lipschitz `C¹` potentials and an
additive Haar measure: direction (i) ⇒ (ii) with the uniform linear lower bound as an input, and
the compactness step of (ii) ⇒ (i) without the uniqueness step (a limit potential with moment
measure `ν` is produced, not identified with a given potential). Translation, centering and the
nondegeneracy (13) with `ε = 1/R` for isotropic laws in the ball of radius `R` are audited
separately. -/
set_option autoImplicit false
open MeasureTheory Filter Topology

namespace KlartagAudit

theorem proposition_2_1_forward {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : Measure E)
    [m.IsAddHaarMeasure] {ψ : ℕ → E → ℝ} {F : E → ℝ} {L : NNReal} {α β : ℝ} (hα : 0 < α)
    (hψ : ∀ l, ConvexOn ℝ Set.univ (ψ l)) (hC1 : ∀ l, ContDiff ℝ 1 (ψ l))
    (hLip : ∀ l, LipschitzWith L (ψ l))
    (hlow : ∀ l x, α * ‖x‖ - β ≤ ψ l x)
    (hlim : ∀ y, Tendsto (fun l => ψ l y) atTop (𝓝 (F y))) (b : BoundedContinuousFunction E ℝ) :
    Tendsto (fun l => ∫ x, b (gradient (ψ l) x) * Real.exp (-ψ l x) ∂m) atTop
      (𝓝 (∫ x, b (gradient F x) * Real.exp (-F x) ∂m)) :=
  FunctionalInequalities.Probability.MomentMeasure.tendsto_integral_comp_gradient_mul_exp_neg
    m hα hψ hC1 hLip hlow hlim b

theorem proposition_2_1_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : Measure E)
    [m.IsAddHaarMeasure] {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hμν : Tendsto μ atTop (𝓝 ν))
    {ψ : ℕ → E → ℝ} {L : NNReal} {α β γ C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hψ : ∀ l, ConvexOn ℝ Set.univ (ψ l)) (hC1 : ∀ l, ContDiff ℝ 1 (ψ l))
    (hLip : ∀ l, LipschitzWith L (ψ l))
    (hnorm : ∀ l, ∫ x, Real.exp (-ψ l x) ∂m = 1) (hbar : ∀ l, ∫ x, Real.exp (-ψ l x) • x ∂m = 0)
    (hmap : ∀ l, (m.tilted (-ψ l)).map (gradient (ψ l)) = (μ l : Measure E))
    (hb : ∀ l x, α * ‖x‖ - β ≤ ψ l x ∧ ψ l x ≤ (L : ℝ) * ‖x‖ + γ)
    (hsd : ∀ l x h, ψ l (x + h) + ψ l (x - h) - 2 * ψ l x ≤ C * ‖h‖ ^ 2) :
    ∃ F : E → ℝ, ConvexOn ℝ Set.univ F ∧ LipschitzWith L F ∧ ContDiff ℝ 1 F ∧
      ∫ x, Real.exp (-F x) ∂m = 1 ∧ ∫ x, Real.exp (-F x) • x ∂m = 0 ∧
      (m.tilted (-F)).map (gradient F) = (ν : Measure E) ∧
      LipschitzWith (Real.toNNReal (4 * C)) (gradient F) ∧
      ∀ x h, F (x + h) + F (x - h) - 2 * F x ≤ C * ‖h‖ ^ 2 :=
  FunctionalInequalities.Probability.MomentMeasure.exists_limit_potential m hμν hα hC hψ hC1 hLip
    hnorm hbar hmap hb hsd

#print axioms proposition_2_1_forward
#print axioms proposition_2_1_limit

end KlartagAudit

#print axioms FunctionalInequalities.Analysis.tendsto_gradient_of_tendsto_of_convexOn
#print axioms FunctionalInequalities.Analysis.exists_subseq_tendsto_of_linear_bounds
#print axioms FunctionalInequalities.Analysis.differentiableAt_of_second_difference_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.tendsto_integral_comp_gradient_mul_exp_neg
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_limit_potential
#print axioms FunctionalInequalities.Probability.MomentMeasure.translate_moment_potential
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_translate_centered
#print axioms FunctionalInequalities.Probability.MomentMeasure.inv_le_integral_abs_inner_gradient_of_isotropic

import FunctionalInequalities.KLS.Klartag.LinearGrowth

/-! Klartag arXiv:1309.2767v1, Lemma 2.2, restated with Klartag's "centered" hypotheses (7):
convex `ψ`, `∫ e^{-ψ} = 1` and barycenter `∫ x e^{-ψ(x)} dx = 0` for an additive Haar measure;
conclusion (9) with `‖·‖_ψ` the gauge of `K(ψ) = {x ; ψ(x) ≤ 2n + inf ψ}`. Fradelizi's input (10)
is restated separately. -/
set_option autoImplicit false
open MeasureTheory

namespace KlartagAudit

theorem lemma_2_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : Measure E)
    [m.IsAddHaarMeasure] {ψ : E → ℝ} (hψ : ConvexOn ℝ Set.univ ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂m = 1) (hbar : ∫ x, Real.exp (-ψ x) • x ∂m = 0) (x : E) :
    (Module.finrank ℝ E : ℝ) *
        gauge {y | ψ y ≤ 2 * (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y} x + ψ 0 -
          2 * (Module.finrank ℝ E : ℝ) ≤ ψ x :=
  FunctionalInequalities.Probability.MomentMeasure.linear_growth_of_centered m hψ hnorm hbar x

theorem fradelizi_10 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : Measure E)
    [m.IsAddHaarMeasure] {ψ : E → ℝ} (hψ : ConvexOn ℝ Set.univ ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂m = 1) (hbar : ∫ x, Real.exp (-ψ x) • x ∂m = 0) :
    ψ 0 ≤ (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y :=
  (FunctionalInequalities.Probability.MomentMeasure.le_finrank_add_iInf_of_centered
    m hψ hnorm hbar).2

#print axioms lemma_2_2
#print axioms fradelizi_10

end KlartagAudit

#print axioms FunctionalInequalities.Probability.MomentMeasure.linear_growth_of_le_finrank_add_iInf

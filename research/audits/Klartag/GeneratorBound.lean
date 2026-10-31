module

public import FunctionalInequalities.KLS.Klartag.GeneratorBound

/-! Klartag arXiv:1309.2767v1, Lemma 4.4, for the operator (56): restated with its exact
hypotheses (`C²` potential with positive definite Hessian, gradient values in `K`, condition (51))
and the explicit constant `A = max {0, n - inf_{y ∈ K} ∇ρ(y)·y}`. -/

@[expose] public section
set_option autoImplicit false
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace KlartagAudit

theorem lemma_4_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ψ ρ : E → ℝ} (hψ : ContDiff ℝ 2 ψ) {K : Set E}
    (hPD : ∀ x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ x v v)
    (hK : ∀ x, gradient ψ x ∈ K)
    (h51 : BddBelow ((fun y => ⟪gradient ρ y, y⟫) '' K)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, hessianInverseOperator ψ ρ ψ x ≤ A :=
  FunctionalInequalities.Probability.MomentMeasure.exists_hessianInverseOperator_self_le
    hψ hPD hK h51

#print axioms lemma_4_4

end KlartagAudit

#print axioms FunctionalInequalities.Probability.MomentMeasure.hessianInverseOperator_self_le

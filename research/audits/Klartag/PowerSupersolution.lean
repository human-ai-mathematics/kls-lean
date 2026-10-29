import FunctionalInequalities.KLS.Klartag.PowerSupersolution

/-! Klartag arXiv:1309.2767v1, Lemma 5.2, dual form of Section 5: the statement is restated
with its exact hypotheses (open `K`, `φ` smooth on `K` with positive definite Hessian, `ρ`
convex and `C²` on `K`, the dual transport equation (66) on `K`) and conclusion
`L(f^ε) + ε f^ε ≥ 0` for `f = ⟪(∇²φ)⁻¹θ, θ⟫` and the operator (67). -/
set_option autoImplicit false
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Topology

namespace KlartagAudit

theorem lemma_5_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsOpen K) {φ ρ : E → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ K) (hρ : ContDiffOn ℝ 2 ρ K) (hρc : ConvexOn ℝ K ρ)
    (hPD : ∀ y ∈ K, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v)
    (hEq : ∀ y ∈ K, logDetHessian φ (stdOrthonormalBasis ℝ E) y =
      ⟪y, gradient φ y⟫ - φ y - ρ y)
    (θ : E) {ε : ℝ} (hε : 0 < ε) {x : E} (hx : x ∈ K) :
    0 ≤ nondivergenceOperator (fun y => inverseHessianEntry φ (stdOrthonormalBasis ℝ E) y)
        (fun y i => ⟪y, stdOrthonormalBasis ℝ E i⟫)
        (fun y => ⟪Ring.inverse (hessianOperator φ y) θ, θ⟫ ^ ε) x +
      ε * ⟪Ring.inverse (hessianOperator φ x) θ, θ⟫ ^ ε :=
  FunctionalInequalities.Probability.MomentMeasure.inverseHessian_rpow_supersolution
    hK hφ hρ hρc hPD hEq θ hε hx

#print axioms lemma_5_2

end KlartagAudit

#print axioms FunctionalInequalities.Probability.MomentMeasure.inverseHessian_rpow_supersolution
#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_contDiff_eventuallyEq_germ
#print axioms FunctionalInequalities.Analysis.BakryEmery.nondivergenceOperator_congr
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianOperator_congr_of_eventuallyEq
#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_congr_of_eventuallyEq
#print axioms FunctionalInequalities.Analysis.BakryEmery.inverseHessianEntry_congr_of_eventuallyEq
#print axioms FunctionalInequalities.Analysis.BakryEmery.logDetHessian_congr_of_eventuallyEq
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_dualTransport_rhs
#print axioms FunctionalInequalities.Analysis.BakryEmery.dualTransport_first_derivative
#print axioms FunctionalInequalities.Analysis.BakryEmery.dualTransport_second_derivative

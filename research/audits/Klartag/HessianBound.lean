module

public import FunctionalInequalities.KLS.Klartag.HessianBound
public import FunctionalInequalities.Analysis.Convex.SecondOrder.Difference

/-! Maximum-principle Hessian bound supporting Klartag arXiv:1309.2767v1, Theorem 1.1 (a
different proof, with constant `3R²` in place of `2R²`; not Theorem 1.1 itself): restated with
its exact hypotheses (smooth `φ` with positive definite Hessian solving
`log det ∇²φ = -φ + V(∇φ)` in the standard orthonormal basis, `∇φ(E) ⊆ K ⊆ B(0, R)` with `K`
open, `V` smooth on an open `U ⊇ closure K` and convex on `K`, `Δφ` bounded above, `φ` coercive)
and conclusion `∇²φ[v, v] ≤ 3R² ‖v‖²`. -/

@[expose] public section
set_option autoImplicit false
open Filter FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff

namespace KlartagAudit

theorem hessian_le_three_mul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K U : Set E} (hK : IsOpen K) (hU : IsOpen U) (hKU : closure K ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) (hc : ConvexOn ℝ K V)
    (hRange : Set.range (gradient φ) ⊆ K) {R : ℝ} (hR : ∀ y ∈ K, ‖y‖ ≤ R)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hbound : ∃ C : ℝ, ∀ x, ∑ i, bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i)
      (stdOrthonormalBasis ℝ E i) ≤ C)
    (hcoer : Tendsto φ (cocompact E) atTop) (x v : E) :
    bilinearIteratedFDerivTwo ℝ φ x v v ≤ 3 * R ^ 2 * ‖v‖ ^ 2 := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by decide)
  have hPSD : ∀ w : E, 0 ≤ bilinearIteratedFDerivTwo ℝ φ x w w := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hPD x w hw).le
  have htrace :=
    FunctionalInequalities.Probability.MomentMeasure.trace_hessian_add_sq_le hφ hK hU hKU hV hc
      hRange hR hMA hPD hbound hcoer x
  calc
    bilinearIteratedFDerivTwo ℝ φ x v v ≤
        (∑ i, bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i)
          (stdOrthonormalBasis ℝ E i)) * ‖v‖ ^ 2 :=
      bilinearIteratedFDerivTwo_le_trace_mul_norm_sq hφ2 x hPSD v
    _ ≤ 3 * R ^ 2 * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ‖gradient φ x‖]) (by positivity)

#print axioms hessian_le_three_mul_sq

end KlartagAudit

#print axioms FunctionalInequalities.Probability.MomentMeasure.hessianInverseOperator_fderiv_apply
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.trace_sub_two_mul_sq_le_hessianInverseOperator
#print axioms FunctionalInequalities.Probability.MomentMeasure.trace_hessian_add_sq_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianInverseOperator_sum
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianInverseOperator_sub_const_mul
#print axioms FunctionalInequalities.Analysis.BakryEmery.sum_inverseHessianEntry_mul_hessian_hessian
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianInverseOperator_nonpos_of_isLocalMax
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_le_trace_mul_norm_sq
#print axioms FunctionalInequalities.Analysis.secondDifference_le_of_bilinearIteratedFDerivTwo_le

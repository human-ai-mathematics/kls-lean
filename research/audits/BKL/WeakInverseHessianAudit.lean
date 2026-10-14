import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakInverseHessian

/-! Audit client for the weak inverse-Hessian generator identities (Letwin arXiv:2607.24164v1 (2.2), weak `C^{1,1}`
counterpart) and the inverse-Hessian integrability interface of `Analysis/Matrix/Piola.lean`: the exact original
statements, the generator symmetry they give for compactly supported `C²` tests, and an actual compactly supported
Lipschitz test derivative against inverse-Hessian entries. Canonical imports only. -/

noncomputable section
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis
open scoped Topology RealInnerProductSpace

namespace WeakInverseHessianAudit

theorem exact_original_statement_1 {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x, η x * (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact integral_mul_generator_eq_neg_energy hu hG hV hF hdet hw hGw hη hηc

theorem exact_original_statement_2 {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x, w x * (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact integral_mul_generator_eq_neg_energy' hu hG hV hF hdet hw hGw hη hηc

theorem actual_compact_test_generator_symmetry {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x, η x * (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
    ∫ x, w x * (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact (integral_mul_generator_eq_neg_energy hu hG hV hF hdet hw hGw hη hηc).trans
    (integral_mul_generator_eq_neg_energy' hu hG hV hF hdet hw hGw hη hηc).symm

theorem exact_integrability_interface {n : ℕ}
    {u F f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : NNReal} (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hf : Measurable f) (hfc : HasCompactSupport f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (i j : Fin n) :
    Integrable (fun x => (hessianMatrix u x)⁻¹ i j * f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact integrable_inv_hessianMatrix_mul_of_bounded_compact hG hF hdet hf hfc hC i j

/-- The derivative of a compactly supported Lipschitz test is integrable against every inverse-Hessian entry, with
no global bound on the gradient of `u` beyond its Lipschitz constant. -/
theorem lipschitz_compact_test_derivative_integrable {n : ℕ}
    {u F ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : NNReal} (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    {Lψ : NNReal} (hψ : LipschitzWith Lψ ψ) (hψc : HasCompactSupport ψ) (i j : Fin n)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => (hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x v)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  refine integrable_inv_hessianMatrix_mul_of_bounded_compact hG hF hdet
    ((ContinuousLinearMap.apply ℝ ℝ v).measurable.comp (measurable_fderiv ℝ ψ))
    (hψc.fderiv_apply ℝ v) (C := (Lψ : ℝ) * ‖v‖) ?_ i j
  intro x
  exact ((fderiv ℝ ψ x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hψ) (norm_nonneg v))

#print axioms FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy
#print axioms FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy'
#print axioms FunctionalInequalities.Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact
#print axioms exact_original_statement_1
#print axioms exact_original_statement_2
#print axioms actual_compact_test_generator_symmetry
#print axioms exact_integrability_interface
#print axioms lipschitz_compact_test_derivative_integrable

end WeakInverseHessianAudit

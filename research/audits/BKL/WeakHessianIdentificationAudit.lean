import FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
import FunctionalInequalities.Analysis.BakryEmery.WeakHessian

noncomputable section

open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace ContDiff

namespace WeakHessianIdentificationAudit

theorem frozen_matrix_identification {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    Matrix.toEuclideanLin (hessianMatrix u x) =
      (fderiv ℝ (gradient u) x).toLinearMap := by
  exact hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hu hx

theorem frozen_symmetry {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    (hessianMatrix u x).IsHermitian := by
  exact hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx

/-- A supplied gradient derivative, rather than a classical C² Hessian, represents the matrix. -/
theorem supplied_gradient_derivative {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hT : HasFDerivAt (gradient u) T x) :
    Matrix.toEuclideanLin (hessianMatrix u x) = T.toLinearMap := by
  rw [hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hu hT.differentiableAt,
    hT.fderiv]

/-- The actual R0 consumer: a gradient Lipschitz constant bounds the Hessian in matrix order. -/
theorem upper_bound_of_lipschitz_gradient {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {G : NNReal} (hu : ContDiff ℝ 1 u)
    (hG : LipschitzWith G (gradient u)) (hx : DifferentiableAt ℝ (gradient u) x) :
    ((G : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef := by
  let T := fderiv ℝ (gradient u) x
  have hmat := hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hu hx
  have hH := hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx
  have hsym : T.toLinearMap.IsSymmetric := by
    have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
    rw [hmat] at hs
    exact hs
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hone : Matrix.toLin b.toBasis b.toBasis (1 : Matrix (Fin n) (Fin n) ℝ) =
      LinearMap.id := Matrix.toLin_one _
  have hop : Matrix.toEuclideanLin
      ((G : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x) =
      (G : ℝ) • LinearMap.id - T.toLinearMap := by
    have hmat' := hmat
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at hmat'
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, map_sub, map_smul, hone, hmat']
  rw [← Matrix.isPositive_toEuclideanLin_iff, hop]
  constructor
  · intro v w
    change ⟪(G : ℝ) • v - T v, w⟫ = ⟪v, (G : ℝ) • w - T w⟫
    rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    have hsw : ⟪T v, w⟫ = ⟪v, T w⟫ := hsym v w
    rw [hsw]
  · intro v
    change 0 ≤ ⟪(G : ℝ) • v - T v, v⟫
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hnorm : ‖T‖ ≤ (G : ℝ) := norm_fderiv_le_of_lipschitz ℝ hG
    have hv := (T.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
    have hi := real_inner_le_norm (T v) v
    have hq := mul_le_mul_of_nonneg_right hv (norm_nonneg v)
    nlinarith

#print axioms hessianMatrix_toEuclideanLin_of_differentiableAt_gradient
#print axioms hessianMatrix_isHermitian_of_differentiableAt_gradient
#print axioms frozen_matrix_identification
#print axioms frozen_symmetry
#print axioms supplied_gradient_derivative
#print axioms upper_bound_of_lipschitz_gradient

end WeakHessianIdentificationAudit

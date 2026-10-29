import FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak

/-! Total Hessian identification and weak coordinate calculus through their shared module. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FunctionalInequalities FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein

namespace SourceLayout

/-- The shared matrix retains the original row-direction and column-dual representation. -/
theorem gradient_derivative_matrix_representation {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    gradientDerivativeMatrix L =
      fun r s =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
          (L (EuclideanSpace.basisFun (Fin n) ℝ r))
          (EuclideanSpace.basisFun (Fin n) ℝ s) := rfl

/-- No smoothness premise or positive-dimension assumption enters the total identification. -/
theorem total_hessian_coordinates {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = gradientDerivativeMatrix (fderiv ℝ (gradient u) x) :=
  hessianMatrix_eq_gradientDerivativeMatrix u x

/-- Differentiability of the gradient at one point suffices for coordinate differentiation. -/
theorem weak_hessian_coordinate {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {i j : Fin n}
    (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) = hessianMatrix u x i j :=
  hessian_coord_of_gradient_diff hx

#print axioms SourceLayout.total_hessian_coordinates
#print axioms SourceLayout.weak_hessian_coordinate
#print axioms SourceLayout.gradient_derivative_matrix_representation

end SourceLayout

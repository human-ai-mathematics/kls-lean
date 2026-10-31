module

public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import Lean
meta import Lean

/-! Total coordinate Hessians without the inverse-Hessian diffusion layer. -/

@[expose] public section
set_option autoImplicit false
open FunctionalInequalities
namespace SourceLayout

theorem total_hessian {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Probability.Stein.hessianMatrix f x =
      Probability.Stein.gradientDerivativeMatrix (fderiv ℝ (gradient f) x) :=
  Probability.Stein.hessianMatrix_eq_gradientDerivativeMatrix f x

#print axioms SourceLayout.total_hessian
open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `FunctionalInequalities.Analysis.BakryEmery.hessianInverseOperator then
    throwError "Coordinate Hessians must not import inverse-Hessian diffusion"
end SourceLayout

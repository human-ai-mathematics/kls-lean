import FunctionalInequalities.Analysis.BakryEmery.Hessian.Diffusion

/-! Original source equation of the inverse-Hessian generator. -/
set_option autoImplicit false
open FunctionalInequalities
namespace SourceLayout

theorem inverse_hessian_generator_equation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (φ V f : E → ℝ) (x : E) :
    Analysis.BakryEmery.hessianInverseOperator φ V f x =
      Analysis.BakryEmery.nondivergenceOperator
        (fun y => Analysis.BakryEmery.inverseHessianEntry φ (stdOrthonormalBasis ℝ E) y)
        (fun y i => fderiv ℝ V (gradient φ y) (stdOrthonormalBasis ℝ E i)) f x := rfl

#print axioms SourceLayout.inverse_hessian_generator_equation
end SourceLayout

module

public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates

/-!
# Pointwise linearity of the classical elliptic expression

CNS1984 Lemma5.1 pp385–387 uses trace(A Hess u)+Du(b)+a*u. Its actual
Hessian/gradient/value linearity is generated from local C2 data, without
coefficient regularity, symmetry or ellipticity. Dimension zero is included.
-/

@[expose] public section
noncomputable section
namespace FunctionalInequalities.Analysis
open Probability.Stein

/-- The same scalar combination governs all three terms of the operator. -/
theorem elliptic_operator_linear_combination {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin n)) (a c d : ℝ) {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    Matrix.trace (A * hessianMatrix (fun y => c * u y + d * v y) x) +
          (fderiv ℝ (fun y => c * u y + d * v y) x) b +
        a * (c * u x + d * v x) =
      c * (Matrix.trace (A * hessianMatrix u x) + (fderiv ℝ u x) b + a * u x) +
        d * (Matrix.trace (A * hessianMatrix v x) + (fderiv ℝ v x) b + a * v x) := by
  have hdu := hu.differentiableAt (by norm_num)
  have hdv := hv.differentiableAt (by norm_num)
  have hD : fderiv ℝ (fun y => c * u y + d * v y) x = c • fderiv ℝ u x + d • fderiv ℝ v x :=
    ((hdu.hasFDerivAt.const_mul c).add (hdv.hasFDerivAt.const_mul d)).fderiv
  rw [hessianMatrix_add_of_contDiffAt (contDiffAt_const.mul hu) (contDiffAt_const.mul hv),
    hessianMatrix_const_mul_of_contDiffAt c hu, hessianMatrix_const_mul_of_contDiffAt d hv, hD,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

end FunctionalInequalities.Analysis

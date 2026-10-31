module

public import FunctionalInequalities.Analysis.Elliptic.Operator
public import FunctionalInequalities.Analysis.Convex.Quadratic
@[expose] public section

noncomputable section
open scoped RealInnerProductSpace
namespace FunctionalInequalities.Analysis.OperatorLinearityAudit
open FunctionalInequalities.Probability.Stein
lemma actual_quadratic_affine_operator :
    let u : EuclideanSpace ℝ (Fin 1) → ℝ := quadraticAt (2 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 0
    let v : EuclideanSpace ℝ (Fin 1) → ℝ := quadraticAt 0 0 (EuclideanSpace.single 0 1) 0
    let x : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
    Matrix.trace
            ((2 : Matrix (Fin 1) (Fin 1) ℝ) * hessianMatrix (fun y => 4 * u y - 2 * v y) x) +
          (fderiv ℝ (fun y => 4 * u y - 2 * v y) x) (EuclideanSpace.single 0 3) -
        5 * (4 * u x - 2 * v x) =
      24 := by
  intro u v x
  have hu : ContDiff ℝ 2 u := contDiff_quadraticAt_all _ _ _ _
  have hv : ContDiff ℝ 2 v := contDiff_quadraticAt_all _ _ _ _
  have h :=
    elliptic_operator_linear_combination (2 : Matrix (Fin 1) (Fin 1) ℝ)
      (EuclideanSpace.single 0 3) (-5) 4 (-2) hu.contDiffAt hv.contDiffAt (x := x)
  have hH2 : (2 : Matrix (Fin 1) (Fin 1) ℝ).IsHermitian := Matrix.isHermitian_natCast 2
  have hH0 : (0 : Matrix (Fin 1) (Fin 1) ℝ).IsHermitian := by simp
  have hLu :
    Matrix.trace ((2 : Matrix (Fin 1) (Fin 1) ℝ) * hessianMatrix u x) +
          (fderiv ℝ u x) (EuclideanSpace.single 0 3) +
        (-5) * u x =
      5 := by
    dsimp only [u]
    rw [hessianMatrix_quadraticAt hH2, ← inner_gradient_left, gradient_quadraticAt hH2]
    norm_num [x, quadraticAt, Matrix.trace, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_one, Matrix.ofNat_apply, PiLp.inner_apply]
  have hLv :
    Matrix.trace ((2 : Matrix (Fin 1) (Fin 1) ℝ) * hessianMatrix v x) +
          (fderiv ℝ v x) (EuclideanSpace.single 0 3) +
        (-5) * v x =
      -2 := by
    dsimp only [v]
    rw [hessianMatrix_quadraticAt hH0, ← inner_gradient_left, gradient_quadraticAt hH0]
    norm_num [x, quadraticAt, Matrix.trace, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_one, Matrix.ofNat_apply, PiLp.inner_apply]
  rw [hLu, hLv] at h
  have hf : (fun y => 4 * u y - 2 * v y) = (fun y => 4 * u y + (-2) * v y) := by funext y; ring
  rw [hf]
  convert h using 1 <;> ring

lemma true_fin_zero_operator (a c d : ℝ) (x : EuclideanSpace ℝ (Fin 0)) :
    Matrix.trace
            ((0 : Matrix (Fin 0) (Fin 0) ℝ) * hessianMatrix (fun _ => c * 7 + d * (-2)) x) +
          (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 0) => c * 7 + d * (-2)) x) 0 +
        a * (c * 7 + d * (-2)) =
      c * (a * 7) + d * (a * (-2)) := by
  have h :=
    elliptic_operator_linear_combination (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 a c d (u := fun _ =>
      7) (v := fun _ => -2) (x := x) contDiffAt_const contDiffAt_const
  simpa using h
end FunctionalInequalities.Analysis.OperatorLinearityAudit
#print axioms
  FunctionalInequalities.Analysis.OperatorLinearityAudit.actual_quadratic_affine_operator
#print axioms FunctionalInequalities.Analysis.OperatorLinearityAudit.true_fin_zero_operator

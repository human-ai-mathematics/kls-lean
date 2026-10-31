module

public import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
public import FunctionalInequalities.Analysis.IteratedDerivative.Bootstrap.LinearEquation
public import FunctionalInequalities.Analysis.Matrix.DeterminantDerivative

/-!
# Finite-regularity linearization of the moment Monge–Ampère equation

Letwin arXiv:2607.24164v1, (2.4), used in the smoothness argument of Lemma 2.2;
Gilbarg–Trudinger, Classics 2001, Lemma 17.16, pp. 463–464.
Only C³ regularity of the given potential and C¹ regularity of the target potential are needed.
-/

@[expose] public section

noncomputable section
namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms
open Set Metric
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped NNReal ContDiff BigOperators Matrix.Norms.Elementwise


variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/--
Genuine local finite-order Hessian regularity, shared by the C3 differentiable-Hessian source and
the local C4 classical source. -/
theorem contDiffAt_hessianMatrix {n : ℕ} {k : ℕ∞ω} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ (k + 2) u x) :
    ContDiffAt ℝ k (hessianMatrix u) x := by
  have hD1 : ContDiffAt ℝ (k + 1) (fderiv ℝ u) x := hu.fderiv_right (by norm_num [add_assoc])
  have hD2 : ContDiffAt ℝ k (fderiv ℝ (fderiv ℝ u)) x := hD1.fderiv_right le_rfl
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact (hD2.clm_apply contDiffAt_const).clm_apply contDiffAt_const

/-- The Hessian matrix of a C³ function is differentiable. -/
theorem differentiable_hessianMatrix_of_contDiff_three {u : E → ℝ} (hu : ContDiff ℝ 3 u) :
    Differentiable ℝ (hessianMatrix u) := by
  intro x
  exact (contDiffAt_hessianMatrix (k:=1) hu.contDiffAt).differentiableAt (by norm_num)

/-- Coordinate derivative of the Hessian matrix, with only C³ data. -/
theorem fderiv_hessianMatrix_apply_of_contDiff_three {u : E → ℝ} (hu : ContDiff ℝ 3 u)
    (x e : E) (i j : Fin n) :
    (fderiv ℝ (hessianMatrix u) x e) i j =
      fderiv ℝ (fun y => hessianMatrix u y i j) x e := by
  have hM := differentiable_hessianMatrix_of_contDiff_three hu x
  rw [fderiv_apply (differentiableAt_pi.mp hM i) j, fderiv_apply hM i]
  rfl

/-- For a C³ potential, each coordinate derivative satisfies the linear elliptic equation
with inverse-Hessian leading coefficient, drift −∇W(∇u), and zero-order coefficient 1. -/
theorem coordinate_linear_equation_of_mongeAmpere {u W : E → ℝ}
    (hu : ContDiff ℝ 3 u) (hW : ContDiff ℝ 1 W)
    (hp : ∀ x, (hessianMatrix u x).PosDef)
    (heq : ∀ x, Real.log (hessianMatrix u x).det = -u x + W (gradient u x))
    (k : Fin n) (x : E) :
    (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
      fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ k))) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
      (∑ i, (-gradient W (gradient u x) i) *
        fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ k)) x
          (EuclideanSpace.basisFun (Fin n) ℝ i)) +
      fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) = 0 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hD1 : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hD2 : Differentiable ℝ (fderiv ℝ (fderiv ℝ u)) :=
    (hD1.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hsym := hD1.contDiffAt (x := x) |>.isSymmSndFDerivAt (by simp)
  have hlog := fderiv_logDet_comp_apply
    (differentiable_hessianMatrix_of_contDiff_three hu x) (hp x).det_pos.ne'
    (EuclideanSpace.basisFun (Fin n) ℝ k)
  have hfun : (fun y => Real.log (hessianMatrix u y).det) = fun y => -u y + W (gradient u y) :=
    funext heq
  have hrhs : fderiv ℝ (fun y => -u y + W (gradient u y)) x
      (EuclideanSpace.basisFun (Fin n) ℝ k) =
      -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
        ∑ i, hessianMatrix u x k i * gradient W (gradient u x) i := by
    rw [fderiv_fun_add (f := fun y => -u y) (g := fun y => W (gradient u y))
      ((hu.differentiable (by norm_num) x).neg)
      (((hW.differentiable one_ne_zero) (gradient u x)).comp x
        ((contDiff_gradient hu (m := 2) (by norm_num)).differentiable (by norm_num) x)),
      fderiv_fun_neg, add_apply, neg_apply]
    exact congrArg (fun z : ℝ => -fderiv ℝ u x
      (EuclideanSpace.basisFun (Fin n) ℝ k) + z) (chain_coordinate hu2 hW x k)
  rw [hfun, hrhs] at hlog
  have hlead : Matrix.trace ((hessianMatrix u x)⁻¹ *
      fderiv ℝ (hessianMatrix u) x (EuclideanSpace.basisFun (Fin n) ℝ k)) =
      ∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ k))) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [fderiv_hessianMatrix_apply_of_contDiff_three hu]
    have hentry : (fun y => hessianMatrix u y j i) =
        fun y => fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
      funext y
      exact (hu2.contDiffAt (x := y)).isSymmSndFDerivAt (by simp) _ _
    rw [hentry, fderiv_hessian_entry_apply (hD2 x),
      fderiv_fderiv_directional_apply hu2 (hD2 x)]
    exact congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.basisFun (Fin n) ℝ j))
      (hsym (EuclideanSpace.basisFun (Fin n) ℝ k) (EuclideanSpace.basisFun (Fin n) ℝ i))

  rw [hlead] at hlog
  have hdrift : (∑ i, (-gradient W (gradient u x) i) *
        fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ k)) x
          (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      -(∑ i, hessianMatrix u x k i * gradient W (gradient u x) i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_directional_eq hu2]
    change (-gradient W (gradient u x) i) * hessianMatrix u x k i = _
    ring
  rw [hdrift]
  linarith

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Filter
open scoped Matrix.Norms.Elementwise Topology
open FunctionalInequalities.Probability.Stein

/-- Actual classical Hessian source for Savin Proposition4.1 proof(10)-(11).
C4 and the local determinant equation concern this GIVEN classical function;
no linearized identities are inputs and no C2 of the generated C1 UNIT U is claimed. -/
theorem classical_hessian_trace_identities {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ} (hu : ContDiffAt ℝ 4 u x) (hc : c ≠ 0)
    (heq : ∀ᶠ y in 𝓝 x, (hessianMatrix u y).det = c) :
    (∀ v : EuclideanSpace ℝ (Fin n),
        ((hessianMatrix u x)⁻¹ * fderiv ℝ (hessianMatrix u) x v).trace = 0) ∧
      ∀ v w : EuclideanSpace ℝ (Fin n),
        ((hessianMatrix u x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ (hessianMatrix u) y w) x v).trace =
          ((hessianMatrix u x)⁻¹ * fderiv ℝ (hessianMatrix u) x v * (hessianMatrix u x)⁻¹ *
              fderiv ℝ (hessianMatrix u) x w).trace := by
  exact trace_identities_of_eventually_det_const (contDiffAt_hessianMatrix (k := 2) hu) hc heq

end FunctionalInequalities.Analysis

import FunctionalInequalities.Analysis.Newtonian.Truncation.Basic
import FunctionalInequalities.Analysis.Cutoff.RadialLipschitz

/-!
# Derivative error of the truncated Newtonian kernel

For the smooth truncation `truncatedNewtonianKernel n eps` of the kernel of Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12):

* `exists_newtonian_truncation_derivative_error_cap`: one constant `B > 0`, valid in every dimension
  `n ≥ 2` and at every radius `eps > 0`, with
  `|∂ᵢΓ_eps(x) - ∂ᵢΓ(x)| ≤ |∂ᵢΓ(x)| + (B / eps) |Γ(x)|` for `x ≠ 0`;
* `fderiv_truncatedNewtonianKernel_eq_of_far`: the derivatives agree on `‖x‖ > 2 eps`.

These are the pointwise inputs of the cutoff argument in the proof of Lemma 4.1.
-/

noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

private theorem truncation_derivative_error_le_of_lipschitz {n : ℕ} (hn : 2 ≤ n)
    {eps B : ℝ} (heps : 0 < eps) (hB : 0 ≤ B)
    (hlip : LipschitzWith (Real.toNNReal (B/eps))
      (fun y : EuclideanSpace ℝ (Fin n) => 1-Real.smoothTransition (2-‖y‖/eps)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (i : Fin n) :
    |fderiv ℝ (truncatedNewtonianKernel n eps) x (EuclideanSpace.basisFun (Fin n) ℝ i)-
      fderiv ℝ (newtonianKernel n) x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
      |fderiv ℝ (newtonianKernel n) x (EuclideanSpace.basisFun (Fin n) ℝ i)| +
        (B/eps)*|newtonianKernel n x| := by
  let chi : EuclideanSpace ℝ (Fin n) → ℝ := fun y => 1-Real.smoothTransition (2-‖y‖/eps)
  let e := EuclideanSpace.basisFun (Fin n) ℝ i
  have hp : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2-s)) :=
    FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff.1
  have hr : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖/eps) x :=
    (contDiffAt_norm ℝ hx).div_const eps
  have hchi : DifferentiableAt ℝ chi x :=
    (contDiffAt_const.sub (hp.contDiffAt.comp x hr)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (newtonianKernel n) x :=
    (hasFDerivAt_newtonianKernel hn x hx).differentiableAt
  have heq : fderiv ℝ (truncatedNewtonianKernel n eps) x e =
      newtonianKernel n x*fderiv ℝ chi x e+chi x*fderiv ℝ (newtonianKernel n) x e := by
    change fderiv ℝ (fun y => newtonianKernel n y*chi y) x e = _
    rw [fderiv_fun_mul hg hchi]
    simp only [add_apply,smul_apply,smul_eq_mul]
  have hnorm : ‖fderiv ℝ chi x‖ ≤ B/eps := by
    simpa only [Real.coe_toNNReal (B/eps) (div_nonneg hB heps.le)] using
      norm_fderiv_le_of_lipschitz ℝ hlip
  have happly : |fderiv ℝ chi x e| ≤ B/eps := by
    have he : ‖e‖=1 := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i
    calc
      _ ≤ ‖fderiv ℝ chi x‖*‖e‖ := (fderiv ℝ chi x).le_opNorm e
      _ ≤ _ := by rw [he,mul_one];exact hnorm
  have hsmall : |chi x-1| ≤ 1 := by
    have hlo := Real.smoothTransition.nonneg (2-‖x‖/eps)
    have hhi := Real.smoothTransition.le_one (2-‖x‖/eps)
    dsimp [chi]
    rw [show 1-Real.smoothTransition (2-‖x‖/eps)-1 = -Real.smoothTransition (2-‖x‖/eps) by ring,
      abs_neg,abs_of_nonneg hlo]
    exact hhi
  change |fderiv ℝ (truncatedNewtonianKernel n eps) x e-fderiv ℝ (newtonianKernel n) x e| ≤ _
  rw [heq]
  calc
    _ = |newtonianKernel n x*fderiv ℝ chi x e+(chi x-1)*fderiv ℝ (newtonianKernel n) x e| := by congr 1;ring
    _ ≤ |newtonianKernel n x| *|fderiv ℝ chi x e| +|chi x-1| *|fderiv ℝ (newtonianKernel n) x e| := by
      simpa only [abs_mul] using abs_add_le (newtonianKernel n x*fderiv ℝ chi x e)
        ((chi x-1)*fderiv ℝ (newtonianKernel n) x e)
    _ ≤ |newtonianKernel n x| *(B/eps)+1*|fderiv ℝ (newtonianKernel n) x e| := by gcongr
    _ = _ := by ring

/-- A single actual smooth-profile cap controls derivative errors in every
source dimension and at every positive cutoff radius. -/
theorem exists_newtonian_truncation_derivative_error_cap :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ), 2 ≤ n → ∀ eps : ℝ, 0 < eps →
      ∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → ∀ i : Fin n,
      |fderiv ℝ (truncatedNewtonianKernel n eps) x (EuclideanSpace.basisFun (Fin n) ℝ i)-
        fderiv ℝ (newtonianKernel n) x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
        |fderiv ℝ (newtonianKernel n) x (EuclideanSpace.basisFun (Fin n) ℝ i)| +
          (B/eps)*|newtonianKernel n x| := by
  obtain ⟨B,hB,_,hcomp⟩ := exists_lipschitz_radial_cutoff_cap
  refine ⟨B,hB,?_⟩
  intro n hn eps heps x hx i
  exact truncation_derivative_error_le_of_lipschitz hn heps hB.le (hcomp n eps heps) x hx i

/-- Outside the closed `2 eps` ball the actual derivatives agree by local
equality of the scalar kernels. No boundary value is assumed. -/
theorem fderiv_truncatedNewtonianKernel_eq_of_far {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    (x : EuclideanSpace ℝ (Fin n)) (hx : 2*eps < ‖x‖) :
    fderiv ℝ (truncatedNewtonianKernel n eps) x = fderiv ℝ (newtonianKernel n) x := by
  have he : truncatedNewtonianKernel n eps =ᶠ[𝓝 x] newtonianKernel n := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact truncatedNewtonianKernel_eq_of_far heps y hy.le
  exact he.fderiv_eq

end FunctionalInequalities.Analysis

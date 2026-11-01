module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates

/-!
# One-dimensional smoothness for the moment Monge–Ampère equation

Letwin arXiv:2607.24164v1, Lemma 2.2, one-dimensional smoothness support. The scalar equation
u'' = exp(−u + W(u')) is a smooth autonomous first-order system for (u, u').
The second theorem identifies the actual gradient and Hessian in EuclideanSpace ℝ (Fin 1).
The solution is given; no existence or higher-dimensional regularity is asserted.
-/

@[expose] public section

section
open Set Metric
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

/-- One-dimensional smooth bootstrap for the moment Monge–Ampère equation.
The scalar potential is given; existence and coordinate identification are separate. -/
theorem contDiff_infty_of_positive_second_derivative_log_eq {u V : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ x, 0 < deriv (deriv u) x)
    (heq : ∀ x, Real.log (deriv (deriv u) x) = -u x + V (deriv u x)) : ContDiff ℝ ∞ u := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hdu : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hODE (x : ℝ) : deriv (deriv u) x = Real.exp (-u x + V (deriv u x)) := by
    rw [← heq x, Real.exp_log (hpos x)]
  let γ : ℝ → ℝ × ℝ := fun x => (u x, deriv u x)
  let F : ℝ → (ℝ × ℝ) → (ℝ × ℝ) := fun _ p => (p.2, Real.exp (-p.1 + V p.2))
  have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
    (contDiff_snd.snd).prodMk (((contDiff_snd.fst).neg.add (hV.comp (contDiff_snd.snd))).exp)
  have hγ (x : ℝ) : HasDerivAt γ (F x (γ x)) x := by
    have h :=
      ((hu1.differentiable one_ne_zero x).hasDerivAt).prodMk
        ((hdu.differentiable one_ne_zero x).hasDerivAt)
    rw [hODE x] at h
    exact h
  have hγsmooth : ContDiff ℝ ∞ γ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hI : ContDiffOn ℝ ∞ γ (Icc (x - 1) (x + 1)) :=
      ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤) (f := F) (u := univ) hF.contDiffOn
        (fun t _ => (hγ t).hasDerivWithinAt) (fun _ _ => mem_univ _)
    exact hI.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
  exact hγsmooth.fst
end FunctionalInequalities.Analysis


section
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery

/--
Smoothness of a given one-dimensional moment Monge-Ampere solution, with the actual coordinate
Hessian and gradient. -/
theorem contDiff_infty_of_mongeAmpere_one {u W : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ ∞ W) (hpos : ∀ x, (hessianMatrix u x).PosDef)
    (heq : ∀ x, Real.log (hessianMatrix u x).det = -u x + W (gradient u x)) : ContDiff ℝ ∞ u := by
  let b := EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
  let e : ℝ → EuclideanSpace ℝ (Fin 1) := fun t => t • b
  have hexpand (x : EuclideanSpace ℝ (Fin 1)) : x = (x 0) • b := by
    simpa only [Fin.sum_univ_one, EuclideanSpace.basisFun_repr, b] using
      ((EuclideanSpace.basisFun (Fin 1) ℝ).sum_repr x).symm
  have heC : ContDiff ℝ ∞ e := contDiff_id.smul contDiff_const
  have he (t : ℝ) : HasDerivAt e b t := by
    simpa only [e, id_eq, one_smul] using (hasDerivAt_id t).smul_const b
  let ψ : ℝ → ℝ := u ∘ e
  let V : ℝ → ℝ := W ∘ e
  have hψ : ContDiff ℝ 2 ψ := hu.comp (heC.of_le (WithTop.coe_le_coe.mpr le_top))
  have hV : ContDiff ℝ ∞ V := hW.comp heC
  have hdu : deriv ψ = fun t => fderiv ℝ u (e t) b := by
    funext t
    exact (((hu.differentiable (by simp) (e t)).hasFDerivAt).comp_hasDerivAt t (he t)).deriv
  have hddu (t : ℝ) : deriv (deriv ψ) t = hessianMatrix u (e t) 0 0 := by
    rw [hdu]
    have h :=
      ((differentiable_fderiv_apply hu b (e t)).hasFDerivAt.comp_hasDerivAt t (he t)).deriv
    exact h.trans (bilinearIteratedFDerivTwo_eq_fderiv_apply hu (e t) b b).symm
  have hg (t : ℝ) : gradient u (e t) = deriv ψ t • b := by
    rw [hexpand (gradient u (e t))]
    congr 1
    calc
      (gradient u (e t)) 0 = fderiv ℝ u (e t) b := by
        rw [← EuclideanSpace.inner_basisFun_real]
        exact inner_gradient_left
      _ = deriv ψ t := (congrFun hdu t).symm
  have hψsmooth : ContDiff ℝ ∞ ψ :=
    FunctionalInequalities.Analysis.contDiff_infty_of_positive_second_derivative_log_eq hψ hV
      (fun t => by rw [hddu]; exact (hpos (e t)).diag_pos)
      (fun t => by
        rw [hddu, ← Matrix.det_fin_one (hessianMatrix u (e t))]
        simpa only [ψ, V, Function.comp_apply, hg] using heq (e t))
  have hp : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 1) => x 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff
  convert hψsmooth.comp hp using 1
  funext x
  exact congrArg u (hexpand x)

end FunctionalInequalities.Analysis

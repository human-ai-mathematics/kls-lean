module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import FunctionalInequalities.Analysis.IteratedDerivative.HolderTransport

/-!
# Second derivatives under a linear change of variables

Supporting the linear change of coordinates in Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Lemma 6.1, p. 88, which reduces a
constant-coefficient elliptic operator to the Laplacian. For a continuous linear equivalence
`T : E ≃L[ℝ] F` and `C²` `f : F → ℝ`, with the Hessian taken as the nested Fréchet derivative
`fderiv ℝ (fderiv ℝ ·)`:

* `hessian_comp_equiv`: the Hessian of `f ∘ T` at `x` is `(Hess f (T x)).bilinearComp T T`;
* `hessian_eq_inverse_pullback`: conversely, `Hess f y` is the pullback of `Hess (f ∘ T)` at
  `T⁻¹ y` by `T⁻¹`;
* `norm_hessian_comp_equiv_le`, `norm_hessian_le_inverse_pullback`: the corresponding operator-norm
  bounds with factors `‖T‖²` and `‖T⁻¹‖²`.

These are exact identities and norm bounds; no Schauder estimate is asserted.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The second Fréchet derivative of `f ∘ T` under a continuous linear equivalence `T`. -/
theorem hessian_comp_equiv (T : E ≃L[ℝ] F) (f : F → ℝ)
    (hf : ContDiff ℝ 2 f) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z : E => f (T z))) x =
      (fderiv ℝ (fderiv ℝ f) (T x)).bilinearComp
        T.toContinuousLinearMap T.toContinuousLinearMap := by
  have hfirst :
      fderiv ℝ (fun z : E => f (T z)) =
        fun z => (fderiv ℝ f (T z)).comp T.toContinuousLinearMap := by
    funext z
    exact
      ((hf.differentiable (by decide) (T z)).hasFDerivAt.comp z
          T.toContinuousLinearMap.hasFDerivAt).fderiv
  let C : (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E F ℝ).flip T.toContinuousLinearMap
  have hsecond :=
    C.hasFDerivAt.comp x
      (((hf.fderiv_right (m := 1) (by decide)).differentiable_one (T x)).hasFDerivAt.comp x
        T.toContinuousLinearMap.hasFDerivAt)
  rw [hfirst]
  exact hsecond.fderiv.trans (by
    ext v w
    rfl)

/-- The Hessian of `f` is the inverse pullback of the Hessian of `f ∘ T`; no Hessian field is
supplied as a premise. -/
theorem hessian_eq_inverse_pullback (T : E ≃L[ℝ] F) (f : F → ℝ)
    (hf : ContDiff ℝ 2 f) (y : F) :
    fderiv ℝ (fderiv ℝ f) y =
      (fderiv ℝ (fderiv ℝ (fun z : E => f (T z))) (T.symm y)).bilinearComp
        T.symm.toContinuousLinearMap T.symm.toContinuousLinearMap := by
  have h :=
    hessian_comp_equiv T.symm (fun z : E => f (T z))
      (hf.comp T.contDiff) y
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

/-- Operator-norm bound for the Hessian of `f ∘ T`, with the factor `‖T‖²`. -/
theorem norm_hessian_comp_equiv_le (T : E ≃L[ℝ] F) (f : F → ℝ)
    (hf : ContDiff ℝ 2 f) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun z : E => f (T z))) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (T x)‖ * ‖T.toContinuousLinearMap‖ ^ 2 := by
  calc
    ‖fderiv ℝ (fderiv ℝ (fun z : E => f (T z))) x‖ =
        ‖(fderiv ℝ (fderiv ℝ f) (T x)).bilinearComp
          T.toContinuousLinearMap T.toContinuousLinearMap‖ := by
            rw [hessian_comp_equiv T f hf x]
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) (T x)‖ *
          ‖T.toContinuousLinearMap‖ ^ 2 :=
      norm_bilinearComp_self_le _ _

/-- Operator-norm bound for the Hessian of `f` through `f ∘ T`, with the factor `‖T⁻¹‖²`. -/
theorem norm_hessian_le_inverse_pullback (T : E ≃L[ℝ] F) (f : F → ℝ)
    (hf : ContDiff ℝ 2 f) (y : F) :
    ‖fderiv ℝ (fderiv ℝ f) y‖ ≤
      ‖fderiv ℝ (fderiv ℝ (fun z : E => f (T z))) (T.symm y)‖ *
        ‖T.symm.toContinuousLinearMap‖ ^ 2 := by
  calc
    ‖fderiv ℝ (fderiv ℝ f) y‖ =
        ‖(fderiv ℝ (fderiv ℝ (fun z : E => f (T z))) (T.symm y)).bilinearComp
          T.symm.toContinuousLinearMap T.symm.toContinuousLinearMap‖ := by
            rw [hessian_eq_inverse_pullback T f hf y]
    _ ≤ ‖fderiv ℝ (fderiv ℝ (fun z : E => f (T z))) (T.symm y)‖ *
          ‖T.symm.toContinuousLinearMap‖ ^ 2 :=
      norm_bilinearComp_self_le _ _

end FunctionalInequalities.Analysis

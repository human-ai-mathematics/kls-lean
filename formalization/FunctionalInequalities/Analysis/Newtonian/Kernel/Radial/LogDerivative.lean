import FunctionalInequalities.Analysis.Newtonian.Kernel.Radial.Derivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Off-origin derivatives of the logarithm of the norm

The planar case of the radial calculus for the Newtonian kernel of Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12)–(2.14).
In a real inner-product space and at `x ≠ 0`:

* `hasFDerivAt_log_norm_of_ne_zero`: `y ↦ log ‖y‖` has derivative `‖x‖^(-2) ⟪x, ·⟫`;
* `bilinearIteratedFDerivTwo_log_norm`: its actual second Fréchet derivative
  `‖x‖^(-2) ⟪u,v⟫ - 2 ‖x‖^(-4) ⟪x,u⟫ ⟪x,v⟫`.

Only classical derivatives away from the origin are computed.
-/

noncomputable section

open Filter
open scoped Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual logarithmic radial derivative away from the origin, including the
planar Newtonian kernel. -/
theorem hasFDerivAt_log_norm_of_ne_zero (x : E) (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => Real.log ‖y‖) (‖x‖^(-2:ℝ) • innerSL ℝ x) x := by
  have hn : HasFDerivAt (fun y : E => ‖y‖) (‖x‖^(-1:ℝ) • innerSL ℝ x) x := by
    simpa only [Real.rpow_one,one_mul,show (1:ℝ)-2 = -1 by norm_num] using
      hasFDerivAt_norm_rpow_of_ne_zero x 1 hx
  have hh := hn.log (norm_ne_zero_iff.mpr hx)
  have hc : ‖x‖⁻¹*‖x‖^(-1:ℝ) = ‖x‖^(-2:ℝ) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add (norm_pos_iff.mpr hx)]
    norm_num
  exact hh.congr_fderiv (by rw [smul_smul,hc])

/-- Actual Hessian of log(norm), as a bilinear form away from zero. -/
theorem bilinearIteratedFDerivTwo_log_norm (x u v : E) (hx : x ≠ 0) :
    bilinearIteratedFDerivTwo ℝ (fun y : E => Real.log ‖y‖) x u v =
      ‖x‖^(-2:ℝ)*⟪u,v⟫ - 2*‖x‖^(-4:ℝ)*⟪x,u⟫*⟪x,v⟫ := by
  let G : E → E →L[ℝ] ℝ := fun y => ‖y‖^(-2:ℝ) • innerSL ℝ y
  have he : fderiv ℝ (fun y : E => Real.log ‖y‖) =ᶠ[𝓝 x] G := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (hasFDerivAt_log_norm_of_ne_zero y hy).fderiv
  have hG := (hasFDerivAt_norm_rpow_of_ne_zero x (-2) hx).smul
    ((innerSL ℝ (E := E)).hasFDerivAt)
  change HasFDerivAt G _ x at hG
  change (fderiv ℝ (fderiv ℝ (fun y : E => Real.log ‖y‖)) x u) v = _
  rw [he.fderiv_eq,hG.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,innerSL_apply_apply,smul_eq_mul]
  change ‖x‖^(-2:ℝ)*⟪u,v⟫ + ((-2:ℝ)*‖x‖^((-2:ℝ)-2)*⟪x,u⟫)*⟪x,v⟫ = _
  norm_num
  ring

end FunctionalInequalities.Analysis

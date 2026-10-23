/-
The off-origin first-derivative proof adapts Mathlib Analysis/InnerProductSpace/NormPow:
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Authors: Floris van Doorn, Heather Macbeth
The second-derivative assembly below is new.
-/
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Off-origin derivatives of radial powers

Radial calculus behind the Newtonian kernel of Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12)–(2.14), used in Chapter 4.
In a real inner-product space and at a point `x ≠ 0`:

* `hasFDerivAt_norm_rpow_of_ne_zero`: `y ↦ ‖y‖ ^ p` has derivative `p ‖x‖^(p-2) ⟪x, ·⟫` for every
  real exponent `p`, including the negative Newtonian exponents excluded by Mathlib's global
  `hasFDerivAt_norm_rpow` (which assumes `1 < p`);
* `bilinearIteratedFDerivTwo_norm_rpow`: its actual second Fréchet derivative
  `p ‖x‖^(p-2) ⟪u,v⟫ + p (p-2) ‖x‖^(p-4) ⟪x,u⟫ ⟪x,v⟫`.

Only classical derivatives away from the origin are computed; nothing is claimed at `x = 0`.
-/

noncomputable section

open Filter
open scoped Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Off-origin radial-power derivative for arbitrary real exponent, including
negative Newtonian exponents. Proof follows the nonzero branch of Mathlib's
`hasFDerivAt_norm_rpow`, whose public global statement assumes p>1. -/
theorem hasFDerivAt_norm_rpow_of_ne_zero (x : E) (p : ℝ) (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖^p) ((p*‖x‖^(p-2)) • innerSL ℝ x) x := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert! (hasStrictFDerivAt_norm_sq x).rpow_const (p := p/2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _),← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  ring_nf

/-- Actual second Frechet derivative of the radial power, without assuming
any derivative identity. This is the Hessian calculation for GT2001 Chapter4. -/
theorem bilinearIteratedFDerivTwo_norm_rpow (x u v : E) (p : ℝ) (hx : x ≠ 0) :
    bilinearIteratedFDerivTwo ℝ (fun y : E => ‖y‖^p) x u v =
      p*‖x‖^(p-2)*⟪u,v⟫ + p*(p-2)*‖x‖^(p-4)*⟪x,u⟫*⟪x,v⟫ := by
  let G : E → E →L[ℝ] ℝ := fun y => (p*‖y‖^(p-2)) • innerSL ℝ y
  have he : fderiv ℝ (fun y : E => ‖y‖^p) =ᶠ[𝓝 x] G := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (hasFDerivAt_norm_rpow_of_ne_zero y p hy).fderiv
  have hG := ((hasFDerivAt_norm_rpow_of_ne_zero x (p-2) hx).const_mul p).smul
    ((innerSL ℝ (E := E)).hasFDerivAt)
  change HasFDerivAt G _ x at hG
  change (fderiv ℝ (fderiv ℝ (fun y : E => ‖y‖^p)) x u) v = _
  rw [he.fderiv_eq,hG.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,innerSL_apply_apply,smul_eq_mul]
  change p*‖x‖^(p-2)*⟪u,v⟫ + (p*((p-2)*‖x‖^(p-2-2)*⟪x,u⟫))*⟪x,v⟫ = _
  have hp : p-2-2 = p-4 := by ring
  rw [hp]
  ring

end FunctionalInequalities.Analysis

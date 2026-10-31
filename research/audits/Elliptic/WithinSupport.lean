module

public import FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Clients of `convex_support_of_hasFDerivWithinAt`

* `|·|` on `Ici 0` at the boundary point `0`: the derivative exists only WITHIN `Ici 0` (Mathlib
  `not_differentiableAt_abs_zero`), and the generic theorem gives the support line `y ↦ y`.
* A constant on the one-point space `ℝ⁰ = EuclideanSpace ℝ (Fin 0)`.
* A constant on `ULift.{1} ℝ`, a normed space in universe `1` (the theorem keeps `Type*`).
-/

@[expose] public section

open Set

namespace FunctionalInequalities.Analysis

/--
**Boundary within derivative.** `|·|` is not differentiable at `0`, has derivative `id` within `Ici
0` at `0`,
and the generic support gives `|0| + (y - 0) ≤ |y|` for `y ≥ 0`. -/
theorem abs_boundary_within_support_client :
    ¬DifferentiableAt ℝ (fun x : ℝ => |x|) 0 ∧
      HasFDerivWithinAt (fun x : ℝ => |x|) (ContinuousLinearMap.id ℝ ℝ) (Ici 0) 0 ∧
        ∀ y : ℝ, 0 ≤ y → |(0 : ℝ)| + ContinuousLinearMap.id ℝ ℝ (y - 0) ≤ |y| := by
  have hd : HasFDerivWithinAt (fun x : ℝ => |x|) (ContinuousLinearMap.id ℝ ℝ) (Ici 0) 0 :=
    (hasFDerivWithinAt_id (0 : ℝ) (Ici 0)).congr (fun x hx => abs_of_nonneg hx) abs_zero
  have hfun : (fun x : ℝ => |x|) = norm := funext fun x => (Real.norm_eq_abs x).symm
  have hconv : ConvexOn ℝ (Ici (0 : ℝ)) (fun x : ℝ => |x|) := by
    rw [hfun]
    exact convexOn_norm (convex_Ici 0)
  exact
    ⟨not_differentiableAt_abs_zero, hd, fun y hy =>
      convex_support_of_hasFDerivWithinAt hconv hd self_mem_Ici hy⟩

/-- **`ℝ⁰` constant.** On `EuclideanSpace ℝ (Fin 0)` the constant `3` with derivative `0`. -/
theorem fin_zero_constant_support_client (y : EuclideanSpace ℝ (Fin 0)) :
    (fun _ : EuclideanSpace ℝ (Fin 0) => (3 : ℝ)) 0 +
        (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) (y - 0) ≤
      (fun _ : EuclideanSpace ℝ (Fin 0) => (3 : ℝ)) y :=
  convex_support_of_hasFDerivWithinAt (convexOn_const 3 convex_univ)
    (hasFDerivWithinAt_const 3 0 univ) (mem_univ 0) (mem_univ y)

/-- **Universe `1`.** The theorem applies to `ULift.{1} ℝ`. -/
theorem ulift_constant_support_client (y : ULift.{1} ℝ) :
    (fun _ : ULift.{1} ℝ => (1 : ℝ)) 0 + (0 : ULift.{1} ℝ →L[ℝ] ℝ) (y - 0) ≤
      (fun _ : ULift.{1} ℝ => (1 : ℝ)) y :=
  convex_support_of_hasFDerivWithinAt (convexOn_const 1 convex_univ)
    (hasFDerivWithinAt_const 1 0 univ) (mem_univ 0) (mem_univ y)

end FunctionalInequalities.Analysis

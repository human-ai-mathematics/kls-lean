module

public import FunctionalInequalities.Analysis.Newtonian.Kernel.Radial.LogDerivative
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hessians of the radial Newtonian kernel expressions

The two branches of the fundamental solution of Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12), on `EuclideanSpace ℝ (Fin
n)`:

* `powerKernel n omega x = (n (2 - n) omega)⁻¹ ‖x‖^(2-n)`, with the unit-ball volume left as a
  free positive parameter `omega`, and `logKernel x = (2π)⁻¹ log ‖x‖` in the plane;
* `bilinear_powerKernel` (`n ≥ 3`) and `bilinear_logKernel` (`n = 2`): the actual second Fréchet
  derivatives off the origin, `(n omega)⁻¹ (‖x‖^(-n) ⟪u,v⟫ - n ‖x‖^(-n-2) ⟪x,u⟫ ⟪x,v⟫)`, matching
  GT's second-derivative formula for `Γ` (with `omega = 2π / 2 = π` in the plane).

These are pointwise classical derivative identities away from `0`; the normalized kernel with the
actual unit-ball volume is assembled in `Analysis/Newtonian/Kernel/Basic.lean`.
-/

@[expose] public section

noncomputable section

open scoped Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- The GT2001 (2.12) power expression, with its unit-ball constant left as
an explicit parameter. Statements below concern classical derivatives off zero. -/
def powerKernel (n : ℕ) (omega : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / ((n : ℝ) * (2 - n) * omega)) * ‖x‖ ^ ((2 : ℝ) - n)

/-- The planar GT2001 (2.12) expression, normalized by the actual constant pi. -/
def logKernel (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log ‖x‖

private theorem bilinear_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x u v : E) (c : ℝ) (hf : ContDiffAt ℝ 2 f x) :
    bilinearIteratedFDerivTwo ℝ (fun y => c * f y) x u v =
      c * bilinearIteratedFDerivTwo ℝ f x u v := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ 2 (c • f) x) ![u, v] = _
  rw [iteratedFDeriv_const_smul_apply hf]
  rfl

/-- Actual Hessian of the higher-dimensional power kernel, GT2001 (2.13).
The parameter omega can subsequently be set to the volume of the unit ball. -/
theorem bilinear_powerKernel {n : ℕ} (hn : 3 ≤ n) {omega : ℝ} (hw : 0 < omega)
    (x u v : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    bilinearIteratedFDerivTwo ℝ (powerKernel n omega) x u v =
      (1 / ((n : ℝ) * omega)) *
        (‖x‖ ^ (-(n : ℝ)) * ⟪u, v⟫ - (n : ℝ) * ‖x‖ ^ (-(n : ℝ) - 2) * ⟪x, u⟫ * ⟪x, v⟫) := by
  have hc : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ ((2 : ℝ) - n)) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
  change
    bilinearIteratedFDerivTwo ℝ
        (fun y => (1 / ((n : ℝ) * (2 - n) * omega)) * ‖y‖ ^ ((2 : ℝ) - n)) x u v =
      _
  rw [bilinear_const_mul _ x u v _ hc, bilinearIteratedFDerivTwo_norm_rpow x u v _ hx]
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn2 : (2 : ℝ) - n ≠ 0 := by linarith
  have h1 : (2 : ℝ) - n - 2 = -(n : ℝ) := by ring
  have h2 : (2 : ℝ) - n - 4 = -(n : ℝ) - 2 := by ring
  rw [h1, h2]
  field_simp [hn0, hn2, hw.ne']
  ring

/-- Actual planar Hessian, GT2001 (2.13) at n=2. -/
theorem bilinear_logKernel (x u v : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    bilinearIteratedFDerivTwo ℝ logKernel x u v =
      (1 / (2 * Real.pi)) * (‖x‖ ^ (-2 : ℝ) * ⟪u, v⟫ - 2 * ‖x‖ ^ (-4 : ℝ) * ⟪x, u⟫ * ⟪x, v⟫) := by
  have hc : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 2) => Real.log ‖y‖) x :=
    (contDiffAt_norm ℝ hx).log (norm_ne_zero_iff.mpr hx)
  change bilinearIteratedFDerivTwo ℝ (fun y => (1 / (2 * Real.pi)) * Real.log ‖y‖) x u v = _
  rw [bilinear_const_mul _ x u v _ hc, bilinearIteratedFDerivTwo_log_norm x u v hx]

end FunctionalInequalities.Analysis

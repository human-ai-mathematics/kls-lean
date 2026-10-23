import FunctionalInequalities.Analysis.Harmonic.BallHolder
import Mathlib.Tactic.FinCases

/-!
# Audit: harmonic reproduction and Hessian bounds on a planar quadratic

Real clients of the harmonic part of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Classics 2001 (ISBN 3-540-41160-7), Theorem 4.6, p. 60, and the derivative estimates
of Theorem 2.10 / (2.31) (`FunctionalInequalities/Analysis/Harmonic/`), on the nonzero trace-free
planar quadratic `q(x) = x₀² - x₁²` on `ℝ²`:

* `quadratic_smooth`, `quadratic_hessian`, `quadratic_hessian_nonzero`, `quadratic_laplacian`,
  `quadratic_bound`: `q` is smooth, its Hessian is the constant `diag(2, -2)` (so `D²q(e₀, e₀) = 2`),
  `Δq = 0`, and `|q| ≤ 8` on `B₂(0)`;
* `quadratic_reproduces`: `q = annularKernel 2 (1/8) ⋆ harmonicLocalization 2 q` on `B₁(0)`
  (`local_harmonic_reproduces`, planar logarithmic kernel);
* `quadratic_derivative_caps`: the second and third derivative caps of
  `local_harmonic_derivative_caps` with `M = 8` (the third derivative of `q` is `0`);
* `quadratic_holder_client`: `ball_harmonic_hessian_holder` with `c = 0`, `R = 1`, `α = 1/2`, `M = 8`.

The harmonicity and the value bound are proved, not assumed; the constants are the theorems'
constants, chosen before `q`.
-/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Convolution
namespace HarmonicKernelAudit
open FunctionalInequalities.Analysis
/-- The Euclidean plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The `i`-th coordinate as a continuous linear functional. -/
def coordinate (i : Fin 2) : E →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i

/-- The trace-free quadratic `x₀² - x₁²`. -/
def quadratic (x : E) : ℝ := coordinate 0 x * coordinate 0 x - coordinate 1 x * coordinate 1 x

/-- The constant Hessian `diag(2, -2)` of `quadratic`, as a nested continuous linear map. -/
def quadraticHessian : E →L[ℝ] E →L[ℝ] ℝ :=
  (coordinate 0).smulRight (coordinate 0) + (coordinate 0).smulRight (coordinate 0) -
    ((coordinate 1).smulRight (coordinate 1) + (coordinate 1).smulRight (coordinate 1))

theorem quadratic_smooth : ContDiff ℝ ∞ quadratic :=
  ((coordinate 0).contDiff.mul (coordinate 0).contDiff).sub
    ((coordinate 1).contDiff.mul (coordinate 1).contDiff)

theorem quadratic_fderiv : fderiv ℝ quadratic = fun x => quadraticHessian x := by
  funext x
  have hh := (((coordinate 0).hasFDerivAt (x := x)).mul ((coordinate 0).hasFDerivAt)).sub
    (((coordinate 1).hasFDerivAt).mul ((coordinate 1).hasFDerivAt))
  change fderiv ℝ (fun i : E => coordinate 0 i * coordinate 0 i - coordinate 1 i * coordinate 1 i) x = _
  simpa only [ Pi.mul_def, Pi.sub_def, quadraticHessian, map_sub, map_add,
    sub_apply, add_apply,
    ContinuousLinearMap.smulRight_apply] using hh.fderiv

theorem quadratic_hessian (x : E) : fderiv ℝ (fderiv ℝ quadratic) x = quadraticHessian := by
  rw [quadratic_fderiv]
  exact quadraticHessian.fderiv

theorem quadratic_hessian_nonzero :
    fderiv ℝ (fderiv ℝ quadratic) 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) = 2 := by
  rw [quadratic_hessian]
  norm_num [quadraticHessian, coordinate]

theorem quadratic_laplacian (x : E) : Laplacian.laplacian quadratic x = 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis quadratic
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [iteratedFDeriv_two_apply, quadratic_hessian]
  norm_num [Fin.sum_univ_two, EuclideanSpace.basisFun_apply, quadraticHessian, coordinate]

theorem quadratic_bound : ∀ x ∈ ball (0 : E) 2, |quadratic x| ≤ 8 := by
  intro x hx
  have hx' : ‖x‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hx
  have h0 : |coordinate 0 x| ≤ ‖x‖ := by
    simpa only [coordinate, PiLp.proj_apply, Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  have h1 : |coordinate 1 x| ≤ ‖x‖ := by
    simpa only [coordinate, PiLp.proj_apply, Real.norm_eq_abs] using PiLp.norm_apply_le x 1
  have hs0 : |coordinate 0 x| * |coordinate 0 x| ≤ 4 := by nlinarith [abs_nonneg (coordinate 0 x)]
  have hs1 : |coordinate 1 x| * |coordinate 1 x| ≤ 4 := by nlinarith [abs_nonneg (coordinate 1 x)]
  change |coordinate 0 x * coordinate 0 x - coordinate 1 x * coordinate 1 x| ≤ 8
  exact (abs_sub (coordinate 0 x * coordinate 0 x) (coordinate 1 x * coordinate 1 x)).trans
    (by simpa only [abs_mul, show (4 : ℝ) + 4 = 8 by norm_num] using add_le_add hs0 hs1)

private theorem quadratic_c2 : ContDiffOn ℝ 2 quadratic (ball (0 : E) 2) :=
  (quadratic_smooth.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).contDiffOn

/-- Nonzero-Hessian client of the derived reproducing identity. -/
theorem quadratic_reproduces : ∀ x ∈ ball (0 : E) 1,
    quadratic x = (annularKernel 2 (1 / 8) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      harmonicLocalization 2 quadratic) x :=
  local_harmonic_reproduces (by norm_num) quadratic_c2 (fun x _ => quadratic_laplacian x)

/-- An invocation of both the second and the third derivative bounds. The Hessian entry above is
`2`; the third derivative bound is invoked on the quadratic itself, whose third derivative is `0`. -/
theorem quadratic_derivative_caps : ∃ C2 C3 : ℝ, 0 < C2 ∧ 0 < C3 ∧
    ∀ x ∈ ball (0 : E) 1, ‖fderiv ℝ (fderiv ℝ quadratic) x‖ ≤ C2 * 8 ∧
      ‖iteratedFDeriv ℝ 3 quadratic x‖ ≤ C3 * 8 := by
  obtain ⟨C1, C2, C3, _, hC2, hC3, hcaps⟩ := local_harmonic_derivative_caps (by norm_num : 2 ≤ 2)
  refine ⟨C2, C3, hC2, hC3, ?_⟩
  intro x hx
  have hh := (hcaps quadratic quadratic_c2 (fun y _ => quadratic_laplacian y) 8 quadratic_bound).2 x hx
  refine ⟨hh.2.1, ?_⟩
  rw [← norm_iteratedFDeriv_fderiv (n := 2), ← norm_iteratedFDeriv_fderiv (n := 1),
    norm_iteratedFDeriv_one]
  exact hh.2.2

/-- The same quadratic is a client of the scaled `R⁻²` / `R^{-(2+α)}` ball estimate. -/
theorem quadratic_holder_client : ∃ C : ℝ, 0 < C ∧
    ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
      ‖fderiv ℝ (fderiv ℝ quadratic) x - fderiv ℝ (fderiv ℝ quadratic) y‖ ≤
        C * 8 * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hcaps⟩ := ball_harmonic_hessian_holder (by norm_num : 2 ≤ 2)
  refine ⟨C, hC, ?_⟩
  have hh := hcaps (1 / 2) (by norm_num) (by norm_num) quadratic 0 1 (by norm_num)
    (by simpa only [mul_one] using quadratic_c2)
    (fun y _ => quadratic_laplacian y) 8 (by simpa only [mul_one] using quadratic_bound)
  simpa only [one_div, inv_one, Real.one_rpow, mul_one] using hh.2
end HarmonicKernelAudit

#print axioms HarmonicKernelAudit.quadratic_smooth
#print axioms HarmonicKernelAudit.quadratic_fderiv
#print axioms HarmonicKernelAudit.quadratic_hessian
#print axioms HarmonicKernelAudit.quadratic_hessian_nonzero
#print axioms HarmonicKernelAudit.quadratic_laplacian
#print axioms HarmonicKernelAudit.quadratic_bound
#print axioms HarmonicKernelAudit.quadratic_reproduces
#print axioms HarmonicKernelAudit.quadratic_derivative_caps
#print axioms HarmonicKernelAudit.quadratic_holder_client
#print axioms FunctionalInequalities.Analysis.ball_harmonic_hessian_holder
#print axioms FunctionalInequalities.Analysis.local_harmonic_hessian_holder
#print axioms FunctionalInequalities.Analysis.local_harmonic_derivative_caps
#print axioms FunctionalInequalities.Analysis.local_harmonic_reproduces
#print axioms FunctionalInequalities.Analysis.local_harmonic_contDiffOn
#print axioms FunctionalInequalities.Analysis.compact_harmonic_reproduces
#print axioms FunctionalInequalities.Analysis.integral_mul_laplacian_symm
#print axioms FunctionalInequalities.Analysis.convolution_derivative_caps

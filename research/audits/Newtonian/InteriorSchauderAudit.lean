module

public import FunctionalInequalities.Analysis.Newtonian.Schauder.Interior

/-!
# Audit: GT Theorem 4.6 (Hessian form) on a planar Poisson solution

Real client of `poisson_interior_hessian_holder`
(`FunctionalInequalities/Analysis/Newtonian/Schauder/Interior.lean`;
Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001, Theorem
4.6, p. 60) with
`n = 2`, `α = 1/2`, `c = 0`, `R = 1`, on the nonharmonic quadratic `u(x) = x₀² + x₁²`:

* `sumSquares_smooth`, `sumSquares_hessian`, `sumSquares_hessian_nonzero`: `u` is smooth with
  constant Hessian
  `diag(2, 2)`, so `D²u(e₀, e₀) = 2`;
* `sumSquares_laplacian`, `sumSquares_bound`: `Δu = 4` everywhere and `|u| ≤ 8` on `B₂(0)`;
* `sumSquares_interior_client`: the theorem with `U = 8`, the constant source `f = 4` (`M = 4`) and
  Hölder cap
  `H = 0`, giving `‖D²u‖ ≤ 12 C` and `‖D²u(x) - D²u(y)‖ ≤ 12 C ‖x - y‖^{1/2}` on `B₁(0)`.

Every hypothesis of the theorem is proved, not assumed; the constant `C` is the theorem's constant,
chosen before
`c`, `R` and the data.
-/

@[expose] public section

noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace InteriorSchauderAudit

open FunctionalInequalities.Analysis

/-- The Euclidean plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The `i`-th coordinate as a continuous linear functional. -/
def coordinate (i : Fin 2) : E →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i

/-- The quadratic `x₀² + x₁²`. -/
def sumSquares (x : E) : ℝ := coordinate 0 x * coordinate 0 x + coordinate 1 x * coordinate 1 x

/-- The constant Hessian `diag(2, 2)` of `sumSquares`, as a nested continuous linear map. -/
def sumSquaresHessian : E →L[ℝ] E →L[ℝ] ℝ :=
  (coordinate 0).smulRight (coordinate 0) + (coordinate 0).smulRight (coordinate 0) +
    ((coordinate 1).smulRight (coordinate 1) + (coordinate 1).smulRight (coordinate 1))

theorem sumSquares_smooth : ContDiff ℝ ∞ sumSquares :=
  ((coordinate 0).contDiff.mul (coordinate 0).contDiff).add
    ((coordinate 1).contDiff.mul (coordinate 1).contDiff)

theorem sumSquares_fderiv : fderiv ℝ sumSquares = fun x => sumSquaresHessian x := by
  funext x
  have hh :=
    (((coordinate 0).hasFDerivAt (x := x)).mul ((coordinate 0).hasFDerivAt)).add
      (((coordinate 1).hasFDerivAt).mul ((coordinate 1).hasFDerivAt))
  change
    fderiv ℝ (fun i : E => coordinate 0 i * coordinate 0 i + coordinate 1 i * coordinate 1 i)
        x =
      _
  simpa only [Pi.mul_def, Pi.add_def, sumSquaresHessian, map_add, add_apply,
    ContinuousLinearMap.smulRight_apply] using hh.fderiv

theorem sumSquares_hessian (x : E) : fderiv ℝ (fderiv ℝ sumSquares) x = sumSquaresHessian := by
  rw [sumSquares_fderiv]
  exact sumSquaresHessian.fderiv

theorem sumSquares_hessian_nonzero :
    fderiv ℝ (fderiv ℝ sumSquares) 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) =
      2 := by
  rw [sumSquares_hessian]
  norm_num [sumSquaresHessian, coordinate]

theorem sumSquares_laplacian (x : E) : Laplacian.laplacian sumSquares x = 4 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis sumSquares
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [iteratedFDeriv_two_apply, sumSquares_hessian]
  norm_num [Fin.sum_univ_two, EuclideanSpace.basisFun_apply, sumSquaresHessian, coordinate]

theorem sumSquares_bound : ∀ x ∈ ball (0 : E) (2 * 1), |sumSquares x| ≤ 8 := by
  intro x hx
  have hx' : ‖x‖ < 2 := by simpa only [mem_ball, dist_zero_right, mul_one] using hx
  have h0 : |coordinate 0 x| ≤ ‖x‖ := by
    simpa only [coordinate, PiLp.proj_apply, Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  have h1 : |coordinate 1 x| ≤ ‖x‖ := by
    simpa only [coordinate, PiLp.proj_apply, Real.norm_eq_abs] using PiLp.norm_apply_le x 1
  have hs0 : |coordinate 0 x| * |coordinate 0 x| ≤ 4 := by nlinarith [abs_nonneg (coordinate 0 x)]
  have hs1 : |coordinate 1 x| * |coordinate 1 x| ≤ 4 := by nlinarith [abs_nonneg (coordinate 1 x)]
  change |coordinate 0 x * coordinate 0 x + coordinate 1 x * coordinate 1 x| ≤ 8
  exact (abs_add_le _ _).trans
    (by simpa only [abs_mul, show (4 : ℝ) + 4 = 8 by norm_num] using add_le_add hs0 hs1)

theorem half_pos' : (0 : ℝ≥0) < 1 / 2 := by rw [← NNReal.coe_lt_coe]; norm_num

theorem half_lt_one : (1 / 2 : ℝ≥0) < 1 := by rw [← NNReal.coe_lt_coe]; norm_num

/--
GT 2001 Theorem 4.6 (Hessian form) for `u = x₀² + x₁²`, `Δu = 4`, on `B₁(0) ⊂ B₂(0)` with `α = 1/2`.
-/
theorem sumSquares_interior_client :
    ∃ C : ℝ,
      0 < C ∧
        (∀ x ∈ ball (0 : E) 1, ‖fderiv ℝ (fderiv ℝ sumSquares) x‖ ≤ C * 12) ∧
          ∀ x ∈ ball (0 : E) 1,
            ∀ y ∈ ball (0 : E) 1,
              ‖fderiv ℝ (fderiv ℝ sumSquares) x - fderiv ℝ (fderiv ℝ sumSquares) y‖ ≤
                C * 12 * ‖x - y‖ ^ (((1 / 2 : ℝ≥0)) : ℝ) := by
  obtain ⟨C, hC, hest⟩ :=
    poisson_interior_hessian_holder (by norm_num : 2 ≤ 2) half_pos' half_lt_one
  refine ⟨C, hC, ?_⟩
  have hc2 : ContDiffOn ℝ 2 sumSquares (ball (0 : E) (2 * 1)) :=
    (sumSquares_smooth.of_le
        (by
          change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hf : ∀ y ∈ ball (0 : E) (2 * 1), |(fun _ : E => (4 : ℝ)) y| ≤ 4 := fun y _ => by norm_num
  have hH : HolderOnWith 0 (1 / 2) (fun _ : E => (4 : ℝ)) (ball (0 : E) (2 * 1)) :=
    (HolderWith.const (C := 0) (r := 1 / 2) (y := (4 : ℝ))).holderOnWith _
  have h :=
    hest 0 1 one_pos sumSquares (fun _ => 4) 8 4 0 hc2 (fun x _ => sumSquares_laplacian x)
      sumSquares_bound hf hH
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have := h.1 x hx
    simp only [Real.one_rpow, NNReal.coe_zero, mul_zero, add_zero, mul_one] at this
    linarith
  · have := h.2 x hx y hy
    simp only [Real.one_rpow, NNReal.coe_zero, add_zero, mul_one] at this
    norm_num at this ⊢
    linarith

end InteriorSchauderAudit

#print axioms InteriorSchauderAudit.sumSquares_smooth
#print axioms InteriorSchauderAudit.sumSquares_fderiv
#print axioms InteriorSchauderAudit.sumSquares_hessian
#print axioms InteriorSchauderAudit.sumSquares_hessian_nonzero
#print axioms InteriorSchauderAudit.sumSquares_laplacian
#print axioms InteriorSchauderAudit.sumSquares_bound
#print axioms InteriorSchauderAudit.sumSquares_interior_client
#print axioms FunctionalInequalities.Analysis.poisson_interior_hessian_holder

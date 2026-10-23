import FunctionalInequalities.Analysis.IteratedDerivative.ConstantCoefficientSchauder

/-!
# Audit: GT Lemma 6.1 (interior form) for `2 D₀₀ + D₀₁ + D₁₀ + 2 D₁₁` on a planar solution

Real client of `constant_coefficient_interior_hessian_holder`
(`FunctionalInequalities/Analysis/IteratedDerivative/ConstantCoefficientSchauder.lean`;
Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001, Lemma
6.1, p. 88) with `n = 2`, `A = !![2, 1; 1, 2]` (ellipticity constants `λ = 1`, `Λ = 3`), `α = 1/2`,
`c = 0`, `R = 1`, on the saddle `u(x) = x₀ x₁`, whose Hessian `!![0, 1; 1, 0]` is seen only by the
off-diagonal entries of `A`:

* `matrixA_isSymm`, `matrixA_quadratic_bounds`: `A` is symmetric with `‖ξ‖² ≤ ξᵀAξ ≤ 3‖ξ‖²`
  (`ξᵀAξ = (ξ₀ + ξ₁)² + ξ₀² + ξ₁²`);
* `product_smooth`, `product_hessian`, `product_hessian_nonzero`: `u` is smooth with constant
  Hessian and `D²u(e₀, e₁) = 1`;
* `product_equation`, `product_bound`: `Σ_{ij} A_{ij} D_{ij} u = 2` everywhere and `|u| ≤ 4` on
  `B₂(0)`;
* `product_constant_coefficient_client`: the theorem with `U = 4`, the constant source `f = 2`
  (`M = 2`) and Hölder cap `H = 0`, giving `‖D²u‖ ≤ 6 C` and
  `‖D²u(x) - D²u(y)‖ ≤ 6 C ‖x - y‖^{1/2}` on `B₁(0)`.

Every hypothesis of the theorem is proved, not assumed; the constant `C` is the theorem's constant,
chosen before `A`, `c`, `R` and the data.
-/

noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace ConstantCoefficientAudit

open FunctionalInequalities.Analysis

/-- The Euclidean plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The `i`-th coordinate as a continuous linear functional. -/
def coordinate (i : Fin 2) : E →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i

/-- The coefficient matrix `!![2, 1; 1, 2]`. -/
def matrixA : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

/-- The saddle `x₀ x₁`. -/
def product (x : E) : ℝ := coordinate 0 x * coordinate 1 x

/-- The constant Hessian `!![0, 1; 1, 0]` of `product`, as a nested continuous linear map. -/
def productHessian : E →L[ℝ] E →L[ℝ] ℝ :=
  (coordinate 0).smulRight (coordinate 1) + (coordinate 1).smulRight (coordinate 0)

theorem matrixA_isSymm : matrixA.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem matrixA_quadratic_bounds : ∀ ξ : E, 1 * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, matrixA i j * ξ i * ξ j ∧
    ∑ i, ∑ j, matrixA i j * ξ i * ξ j ≤ 3 * ‖ξ‖ ^ 2 := by
  intro ξ
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, matrixA, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> nlinarith [sq_nonneg (ξ 0 + ξ 1), sq_nonneg (ξ 0 - ξ 1)]

theorem product_smooth : ContDiff ℝ ∞ product :=
  (coordinate 0).contDiff.mul (coordinate 1).contDiff

theorem product_fderiv : fderiv ℝ product = fun x => productHessian x := by
  funext x
  have hh := ((coordinate 0).hasFDerivAt (x := x)).mul ((coordinate 1).hasFDerivAt)
  change fderiv ℝ (fun i : E => coordinate 0 i * coordinate 1 i) x = _
  simpa only [Pi.mul_def, productHessian, add_apply, ContinuousLinearMap.smulRight_apply] using hh.fderiv

theorem product_hessian (x : E) : fderiv ℝ (fderiv ℝ product) x = productHessian := by
  rw [product_fderiv]
  exact productHessian.fderiv

theorem product_hessian_nonzero :
    fderiv ℝ (fderiv ℝ product) 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) = 1 := by
  rw [product_hessian]
  norm_num [productHessian, coordinate]

theorem product_equation (x : E) : ∑ i, ∑ j, matrixA i j * fderiv ℝ (fderiv ℝ product) x
    (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j) = 2 := by
  simp only [product_hessian]
  norm_num [Fin.sum_univ_two, matrixA, EuclideanSpace.basisFun_apply, productHessian, coordinate]

theorem product_bound : ∀ x ∈ ball (0 : E) (2 * 1), |product x| ≤ 4 := by
  intro x hx
  have hx' : ‖x‖ < 2 := by simpa only [mem_ball, dist_zero_right, mul_one] using hx
  have h0 : |coordinate 0 x| ≤ ‖x‖ := by
    simpa only [coordinate, PiLp.proj_apply, Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  have h1 : |coordinate 1 x| ≤ ‖x‖ := by
    simpa only [coordinate, PiLp.proj_apply, Real.norm_eq_abs] using PiLp.norm_apply_le x 1
  change |coordinate 0 x * coordinate 1 x| ≤ 4
  rw [abs_mul]
  nlinarith [abs_nonneg (coordinate 0 x), abs_nonneg (coordinate 1 x), norm_nonneg x]

theorem half_pos' : (0 : ℝ≥0) < 1 / 2 := by rw [← NNReal.coe_lt_coe]; norm_num

theorem half_lt_one : (1 / 2 : ℝ≥0) < 1 := by rw [← NNReal.coe_lt_coe]; norm_num

/-- GT 2001 Lemma 6.1 (interior form) for `u = x₀ x₁`, `A = !![2, 1; 1, 2]`, `Σ A_{ij} D_{ij} u = 2`, on
`B₁(0) ⊂ B₂(0)` with `α = 1/2`. -/
theorem product_constant_coefficient_client : ∃ C : ℝ, 0 < C ∧
    (∀ x ∈ ball (0 : E) 1, ‖fderiv ℝ (fderiv ℝ product) x‖ ≤ C * 6) ∧
    ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
      ‖fderiv ℝ (fderiv ℝ product) x - fderiv ℝ (fderiv ℝ product) y‖ ≤
        C * 6 * ‖x - y‖ ^ (((1 / 2 : ℝ≥0)) : ℝ) := by
  obtain ⟨C, hC, hest⟩ := constant_coefficient_interior_hessian_holder (by norm_num : 2 ≤ 2) half_pos'
    half_lt_one (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) ≤ 3)
  refine ⟨C, hC, ?_⟩
  have hc2 : ContDiffOn ℝ 2 product (ball (0 : E) (2 * 1)) :=
    (product_smooth.of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hf : ∀ y ∈ ball (0 : E) (2 * 1), |(fun _ : E => (2 : ℝ)) y| ≤ 2 := fun y _ => by norm_num
  have hH : HolderOnWith 0 (1 / 2) (fun _ : E => (2 : ℝ)) (ball (0 : E) (2 * 1)) :=
    (HolderWith.const (C := 0) (r := 1 / 2) (y := (2 : ℝ))).holderOnWith _
  have h := hest matrixA matrixA_isSymm matrixA_quadratic_bounds 0 1 one_pos product (fun _ => 2) 4 2 0
    hc2 (fun x _ => product_equation x) product_bound hf hH
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have := h.1 x hx
    simp only [Real.one_rpow, NNReal.coe_zero, mul_zero, add_zero, mul_one] at this
    linarith
  · have := h.2 x hx y hy
    simp only [Real.one_rpow, NNReal.coe_zero, add_zero, mul_one] at this
    norm_num at this ⊢
    linarith

end ConstantCoefficientAudit

#print axioms ConstantCoefficientAudit.matrixA_isSymm
#print axioms ConstantCoefficientAudit.matrixA_quadratic_bounds
#print axioms ConstantCoefficientAudit.product_smooth
#print axioms ConstantCoefficientAudit.product_fderiv
#print axioms ConstantCoefficientAudit.product_hessian
#print axioms ConstantCoefficientAudit.product_hessian_nonzero
#print axioms ConstantCoefficientAudit.product_equation
#print axioms ConstantCoefficientAudit.product_bound
#print axioms ConstantCoefficientAudit.product_constant_coefficient_client
#print axioms FunctionalInequalities.Analysis.constant_coefficient_interior_hessian_holder
#print axioms FunctionalInequalities.Analysis.poisson_interior_hessian_holder

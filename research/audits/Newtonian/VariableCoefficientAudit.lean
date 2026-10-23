import FunctionalInequalities.Analysis.IteratedDerivative.VariableCoefficientSchauder

/-!
# Audit: GT Theorem 6.2 (interior a priori form) for `(1 + x₀²/8) Δ + 1` on a planar quadratic

Real client of `variable_coefficient_interior_hessian_holder`
(`FunctionalInequalities/Analysis/IteratedDerivative/VariableCoefficientSchauder.lean`;
Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001,
Theorem 6.2, pp. 90–92) with `n = 2`, the variable principal coefficients
`a(x) = (1 + x₀²/8) · Id` (ellipticity constants `λ = 1`, `Λ = 2`, Hölder constant `K = 1` with
exponent `α = 1/2` on `closedBall 0 2`), no first-order term (`Kb = 0`), `c = 0`, `R = 1`, on the
quadratic `v(x) = x₀²`, whose Hessian is the constant `2 e₀ ⊗ e₀`, so that
`Σ_{ij} aⁱʲ D_{ij} v + v = 2 + (5/4) x₀² =: g`:

* `coefficient_symm`, `coefficient_elliptic`, `coefficient_holder`: symmetry, the quadratic-form
  bounds `‖ξ‖² ≤ ξᵀ a(x) ξ ≤ 2 ‖ξ‖²` and the `1/2`-Hölder bound `|a(x) - a(y)| ≤ ‖x - y‖^{1/2}` on
  `closedBall 0 2`;
* `square_smooth`, `square_hessian`, `square_hessian_nonzero`: `v` is smooth with constant
  Hessian and `D²v(e₀, e₀) = 2`;
* `square_equation`, `square_bound`, `source_bound`, `source_holder`: the equation on the whole
  plane, `|v| ≤ 4`, `|g| ≤ 7` and `[g]_{1/2} ≤ 10` on `closedBall 0 2`;
* `square_variable_coefficient_client`: the theorem with `V = 4`, `M = 7`, `H = 10`, the trivial
  a priori Hessian bounds `N = ‖D²v‖`, `N2 = 0`, giving `‖D²v‖ ≤ 21 C` and
  `‖D²v(x) - D²v(y)‖ ≤ 21 C ‖x - y‖^{1/2}` on `ball 0 1`.

Every hypothesis of the theorem is proved, not assumed; the constant `C` is the theorem's constant,
chosen before the centre, the radius, the coefficients and the data.
-/

noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace VariableCoefficientAudit

open FunctionalInequalities.Analysis

/-- The Euclidean plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The `i`-th coordinate as a continuous linear functional. -/
def coordinate (i : Fin 2) : E →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i

/-- The principal coefficients `a(x) = (1 + x₀²/8) · Id`. -/
def coefficient (i j : Fin 2) (x : E) : ℝ := if i = j then 1 + coordinate 0 x ^ 2 / 8 else 0

/-- The quadratic `x₀²`. -/
def square (x : E) : ℝ := coordinate 0 x * coordinate 0 x

/-- The constant Hessian `2 e₀ ⊗ e₀` of `square`, as a nested continuous linear map. -/
def squareHessian : E →L[ℝ] E →L[ℝ] ℝ :=
  (coordinate 0).smulRight (coordinate 0) + (coordinate 0).smulRight (coordinate 0)

/-- The right-hand side `g = 2 + (5/4) x₀²`. -/
def source (x : E) : ℝ := 2 + 5 / 4 * coordinate 0 x ^ 2

theorem coordinate_abs_le (x : E) (i : Fin 2) : |coordinate i x| ≤ ‖x‖ := by
  simpa only [coordinate, PiLp.proj_apply, Real.norm_eq_abs] using PiLp.norm_apply_le x i

theorem coordinate_sq_le {x : E} (hx : x ∈ closedBall (0 : E) (2 * 1)) :
    coordinate 0 x ^ 2 ≤ 4 := by
  have hx' : ‖x‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right, mul_one] using hx
  have h := coordinate_abs_le x 0
  nlinarith [abs_nonneg (coordinate 0 x), sq_abs (coordinate 0 x)]

theorem coefficient_symm : ∀ x ∈ closedBall (0 : E) (2 * 1), ∀ i j,
    coefficient i j x = coefficient j i x := by
  intro x _ i j
  by_cases h : i = j
  · subst h; rfl
  · simp [coefficient, h, Ne.symm h]

theorem coefficient_elliptic : ∀ x ∈ closedBall (0 : E) (2 * 1), ∀ ξ : E,
    1 * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, coefficient i j x * ξ i * ξ j ∧
      ∑ i, ∑ j, coefficient i j x * ξ i * ξ j ≤ 2 * ‖ξ‖ ^ 2 := by
  intro x hx ξ
  have h4 := coordinate_sq_le hx
  have h0 : 0 ≤ coordinate 0 x ^ 2 := sq_nonneg _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, coefficient, Fin.isValue, if_true, Fin.zero_eq_one_iff,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false]
  constructor <;> nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1)]

/-- Distances in `closedBall 0 2` are at most twice their square root. -/
theorem norm_sub_le_two_mul_sqrt {x y : E} (hx : x ∈ closedBall (0 : E) (2 * 1))
    (hy : y ∈ closedBall (0 : E) (2 * 1)) :
    ‖x - y‖ ≤ 2 * ‖x - y‖ ^ (((1 / 2 : ℝ≥0)) : ℝ) := by
  have hx' : ‖x‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right, mul_one] using hx
  have hy' : ‖y‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right, mul_one] using hy
  have hd : ‖x - y‖ ≤ 4 := (norm_sub_le x y).trans (by linarith)
  have hs : ‖x - y‖ ^ (((1 / 2 : ℝ≥0)) : ℝ) = Real.sqrt ‖x - y‖ := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [hs]
  have h1 := Real.sq_sqrt (norm_nonneg (x - y))
  have h2 := Real.sqrt_nonneg ‖x - y‖
  nlinarith

theorem coordinate_sub_abs_le (x y : E) : |coordinate 0 x - coordinate 0 y| ≤ ‖x - y‖ := by
  rw [← map_sub]
  exact coordinate_abs_le (x - y) 0

theorem sq_sub_sq_abs_le {x y : E} (hx : x ∈ closedBall (0 : E) (2 * 1))
    (hy : y ∈ closedBall (0 : E) (2 * 1)) :
    |coordinate 0 x ^ 2 - coordinate 0 y ^ 2| ≤ 4 * ‖x - y‖ := by
  have hx' : ‖x‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right, mul_one] using hx
  have hy' : ‖y‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right, mul_one] using hy
  have h1 := coordinate_abs_le x 0
  have h2 := coordinate_abs_le y 0
  have h3 := coordinate_sub_abs_le x y
  rw [sq_sub_sq, abs_mul]
  calc |coordinate 0 x + coordinate 0 y| * |coordinate 0 x - coordinate 0 y|
      ≤ 4 * ‖x - y‖ := by
        apply mul_le_mul _ h3 (abs_nonneg _) (by norm_num)
        calc |coordinate 0 x + coordinate 0 y| ≤ |coordinate 0 x| + |coordinate 0 y| :=
              abs_add_le _ _
          _ ≤ 4 := by linarith

theorem coefficient_holder : ∀ i j, ∀ x ∈ closedBall (0 : E) (2 * 1),
    ∀ y ∈ closedBall (0 : E) (2 * 1),
    |coefficient i j x - coefficient i j y| ≤ 1 * ‖x - y‖ ^ (((1 / 2 : ℝ≥0)) : ℝ) := by
  intro i j x hx y hy
  by_cases h : i = j
  · subst h
    simp only [coefficient, if_true, one_mul]
    have h1 := sq_sub_sq_abs_le hx hy
    have h2 := norm_sub_le_two_mul_sqrt hx hy
    calc |1 + coordinate 0 x ^ 2 / 8 - (1 + coordinate 0 y ^ 2 / 8)|
        = |coordinate 0 x ^ 2 - coordinate 0 y ^ 2| / 8 := by
          rw [show 1 + coordinate 0 x ^ 2 / 8 - (1 + coordinate 0 y ^ 2 / 8) =
            (coordinate 0 x ^ 2 - coordinate 0 y ^ 2) / 8 by ring, abs_div]
          norm_num
      _ ≤ _ := by linarith
  · simp [coefficient, h]
    positivity

theorem square_smooth : ContDiff ℝ ∞ square :=
  (coordinate 0).contDiff.mul (coordinate 0).contDiff

theorem square_fderiv : fderiv ℝ square = fun x => squareHessian x := by
  funext x
  have hh := ((coordinate 0).hasFDerivAt (x := x)).mul ((coordinate 0).hasFDerivAt)
  change fderiv ℝ (fun i : E => coordinate 0 i * coordinate 0 i) x = _
  simpa only [Pi.mul_def, squareHessian, add_apply, ContinuousLinearMap.smulRight_apply] using
    hh.fderiv

theorem square_hessian (x : E) : fderiv ℝ (fderiv ℝ square) x = squareHessian := by
  rw [square_fderiv]
  exact squareHessian.fderiv

theorem square_hessian_nonzero :
    fderiv ℝ (fderiv ℝ square) 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) = 2 := by
  rw [square_hessian]
  norm_num [squareHessian, coordinate]

theorem square_equation (x : E) : (∑ i, ∑ j, coefficient i j x * fderiv ℝ (fderiv ℝ square) x
    (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j)) +
    (∑ i, (fun _ : Fin 2 => fun _ : E => (0:ℝ)) i x *
      fderiv ℝ square x (EuclideanSpace.basisFun (Fin 2) ℝ i)) + square x = source x := by
  simp only [square_hessian]
  norm_num [Fin.sum_univ_two, coefficient, EuclideanSpace.basisFun_apply, squareHessian,
    coordinate, square, source]
  ring

theorem square_bound : ∀ x ∈ closedBall (0 : E) (2 * 1), |square x| ≤ 4 := by
  intro x hx
  have h := coordinate_sq_le hx
  change |coordinate 0 x * coordinate 0 x| ≤ 4
  rw [abs_mul, ← sq_abs (coordinate 0 x)] at *
  nlinarith [abs_nonneg (coordinate 0 x), sq_abs (coordinate 0 x)]

theorem source_bound : ∀ x ∈ closedBall (0 : E) (2 * 1), |source x| ≤ 7 := by
  intro x hx
  have h := coordinate_sq_le hx
  have h0 : 0 ≤ coordinate 0 x ^ 2 := sq_nonneg _
  rw [source, abs_of_nonneg (by positivity)]
  linarith

theorem source_holder : HolderOnWith (Real.toNNReal 10) (1 / 2) source (closedBall (0 : E) (2 * 1)) := by
  apply holderOnWith_of_dist_le (by norm_num)
  intro x hx y hy
  rw [Real.dist_eq, dist_eq_norm]
  have h1 := sq_sub_sq_abs_le hx hy
  have h2 := norm_sub_le_two_mul_sqrt hx hy
  calc |source x - source y| = 5 / 4 * |coordinate 0 x ^ 2 - coordinate 0 y ^ 2| := by
        rw [show source x - source y = 5 / 4 * (coordinate 0 x ^ 2 - coordinate 0 y ^ 2) by
          simp only [source]; ring, abs_mul]
        norm_num
    _ ≤ 10 * ‖x - y‖ ^ (((1 / 2 : ℝ≥0)) : ℝ) := by linarith

theorem half_pos' : (0 : ℝ≥0) < 1 / 2 := by rw [← NNReal.coe_lt_coe]; norm_num

theorem half_lt_one : (1 / 2 : ℝ≥0) < 1 := by rw [← NNReal.coe_lt_coe]; norm_num

/-- GT 2001 Theorem 6.2 (interior a priori form) for `v = x₀²`, `a = (1 + x₀²/8) Id`, `b = 0`,
`g = 2 + (5/4) x₀²`, on `B₁(0) ⊂ B̄₂(0)` with `α = 1/2`. -/
theorem square_variable_coefficient_client : ∃ C : ℝ, 0 < C ∧
    (∀ x ∈ ball (0 : E) 1, ‖fderiv ℝ (fderiv ℝ square) x‖ ≤ C * 21) ∧
    ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
      ‖fderiv ℝ (fderiv ℝ square) x - fderiv ℝ (fderiv ℝ square) y‖ ≤
        C * 21 * ‖x - y‖ ^ (((1 / 2 : ℝ≥0)) : ℝ) := by
  obtain ⟨C, hC, hest⟩ := variable_coefficient_interior_hessian_holder (by norm_num : 2 ≤ 2)
    half_pos' half_lt_one (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) ≤ 2)
    (by norm_num : (0:ℝ) ≤ 1) (le_refl (0:ℝ))
  refine ⟨C, hC, ?_⟩
  have hc2 : ContDiff ℝ 2 square :=
    square_smooth.of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hb : ∀ i, ∀ x ∈ closedBall (0 : E) (2 * 1),
      |(fun _ : Fin 2 => fun _ : E => (0:ℝ)) i x| ≤ 0 := fun i x _ => by simp
  have hbH : ∀ i, ∀ x ∈ closedBall (0 : E) (2 * 1), ∀ y ∈ closedBall (0 : E) (2 * 1),
      |(fun _ : Fin 2 => fun _ : E => (0:ℝ)) i x - (fun _ : Fin 2 => fun _ : E => (0:ℝ)) i y| ≤
        0 * ‖x - y‖ ^ (((1 / 2 : ℝ≥0)) : ℝ) := fun i x _ y _ => by simp
  have hN : ∀ x ∈ closedBall (0 : E) (2 * 1), ‖fderiv ℝ (fderiv ℝ square) x‖ ≤ ‖squareHessian‖ :=
    fun x _ => by rw [square_hessian]
  have hN2 : ∀ x ∈ closedBall (0 : E) (2 * 1), ∀ y ∈ closedBall (0 : E) (2 * 1),
      ‖fderiv ℝ (fderiv ℝ square) x - fderiv ℝ (fderiv ℝ square) y‖ ≤
        0 * ‖x - y‖ ^ (((1 / 2 : ℝ≥0)) : ℝ) := fun x _ y _ => by
    rw [square_hessian, square_hessian, sub_self, ContinuousLinearMap.opNorm_zero, zero_mul]
  have h := hest 0 1 one_pos le_rfl coefficient (fun _ _ => 0) coefficient_symm
    coefficient_elliptic coefficient_holder hb hbH square source 4 ‖squareHessian‖ 0 7
    (Real.toNNReal 10) hc2 hN hN2 (fun x _ => square_equation x) square_bound source_bound
    source_holder
  have h10 : ((Real.toNNReal 10 : ℝ≥0) : ℝ) = 10 := Real.coe_toNNReal _ (by norm_num)
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have := h.1 x hx
    rw [Real.one_rpow, h10] at this
    linarith
  · have := h.2 x hx y hy
    rw [Real.one_rpow, Real.one_rpow, h10] at this
    norm_num at this ⊢
    linarith

end VariableCoefficientAudit

#print axioms VariableCoefficientAudit.coordinate_abs_le
#print axioms VariableCoefficientAudit.coordinate_sq_le
#print axioms VariableCoefficientAudit.coefficient_symm
#print axioms VariableCoefficientAudit.coefficient_elliptic
#print axioms VariableCoefficientAudit.norm_sub_le_two_mul_sqrt
#print axioms VariableCoefficientAudit.coordinate_sub_abs_le
#print axioms VariableCoefficientAudit.sq_sub_sq_abs_le
#print axioms VariableCoefficientAudit.coefficient_holder
#print axioms VariableCoefficientAudit.square_smooth
#print axioms VariableCoefficientAudit.square_fderiv
#print axioms VariableCoefficientAudit.square_hessian
#print axioms VariableCoefficientAudit.square_hessian_nonzero
#print axioms VariableCoefficientAudit.square_equation
#print axioms VariableCoefficientAudit.square_bound
#print axioms VariableCoefficientAudit.source_bound
#print axioms VariableCoefficientAudit.source_holder
#print axioms VariableCoefficientAudit.square_variable_coefficient_client
#print axioms FunctionalInequalities.Analysis.variable_coefficient_interior_hessian_holder
#print axioms FunctionalInequalities.Analysis.constant_coefficient_interior_hessian_holder
#print axioms FunctionalInequalities.Analysis.exists_absorption_constant
#print axioms FunctionalInequalities.Analysis.exists_hessian_interpolation_constant

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import FunctionalInequalities.Analysis.Convex.Subgradient.Basic

/-!
# Second differences and Lipschitz gradients

A convex differentiable function with `u(x+h) + u(x−h) − 2u(x) ≤ C‖h‖²` has a quadratic upper bound, a co-coercive
gradient and a `4C`-Lipschitz gradient (final step of the `C^{1,1}` estimate of the weak moment-map route to Letwin
arXiv:2607.24164v1).
-/

noncomputable section

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Quadratic upper bound from a second-difference bound** (weak Letwin route, C^{1,1} estimate): a differentiable convex `u` with `u(x+h) + u(x−h) − 2u(x) ≤ C‖h‖²` satisfies
`u y ≤ u x + ⟪∇u x, y − x⟫ + C ‖y − x‖²`. -/
theorem le_add_inner_gradient_add_mul_sq_of_second_difference_le {u : E → ℝ} {C : ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u)
    (hsd : ∀ x h : E, u (x + h) + u (x - h) - 2 * u x ≤ C * ‖h‖ ^ 2) (x y : E) :
    u y ≤ u x + ⟪gradient u x, y - x⟫ + C * ‖y - x‖ ^ 2 := by
  let h : E := y - x
  have hgrad := gradient_le_increment hconv x (-h) (hdiff x)
  have hgrad' : u (x - h) ≥ u x - ⟪gradient u x, h⟫ := by
    have hgrad'' : -⟪gradient u x, h⟫ ≤ u (x - h) - u x := by
      simpa only [inner_neg_right, sub_eq_add_neg] using hgrad
    linarith
  have hsd' := hsd x h
  have hmain :
      u (x + h) ≤ u x + ⟪gradient u x, h⟫ + C * ‖h‖ ^ 2 := by
    linarith
  simpa only [h, add_sub_cancel] using hmain

end InnerProduct

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section CocoerciveGradient

open scoped RealInnerProductSpace

/-! Co-coercivity of the gradient. -/

/-- **Co-coercivity: a quadratic upper bound gives a Lipschitz gradient** (weak Letwin route, C^{1,1}
estimate): if a differentiable convex `u` satisfies
`u y ≤ u x + ⟪∇u x, y − x⟫ + C ‖y − x‖²` for all `x, y` with `C > 0`, then
`‖∇u x − ∇u y‖ ≤ 2C ‖x − y‖`. -/
theorem norm_gradient_sub_le_of_quadratic_upper_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {u : E → ℝ} {C : ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) (hC : 0 < C)
    (hq : ∀ x y : E, u y ≤ u x + ⟪gradient u x, y - x⟫ + C * ‖y - x‖ ^ 2) (x y : E) :
    ‖gradient u x - gradient u y‖ ≤ 2 * C * ‖x - y‖ := by
  have hstar : ∀ a b : E,
      u a - ⟪gradient u a, a⟫ ≤
        u b - ⟪gradient u a, b⟫ -
          ‖gradient u b - gradient u a‖ ^ 2 / (4 * C) := by
    intro a b
    let d : E := gradient u b - gradient u a
    let r : ℝ := 1 / (2 * C)
    let w : E := b - r • d
    have hmin0 :
        ⟪gradient u a, w - a⟫ ≤ u (a + (w - a)) - u a :=
      gradient_le_increment hconv a (w - a) (hdiff a)
    have haw : a + (w - a) = w := by
      abel
    rw [haw] at hmin0
    have hmin_inner :
        ⟪gradient u a, w - a⟫ =
          ⟪gradient u a, w⟫ - ⟪gradient u a, a⟫ := by
      rw [inner_sub_right]
    have hmin :
        u a - ⟪gradient u a, a⟫ ≤ u w - ⟪gradient u a, w⟫ := by
      linarith [hmin0, hmin_inner]
    have hupper :
        u w - ⟪gradient u a, w⟫ ≤
          u b - ⟪gradient u a, b⟫ +
            ⟪d, w - b⟫ + C * ‖w - b‖ ^ 2 := by
      calc
        u w - ⟪gradient u a, w⟫ ≤
            (u b + ⟪gradient u b, w - b⟫ + C * ‖w - b‖ ^ 2) -
              ⟪gradient u a, w⟫ := sub_le_sub_right (hq b w) _
        _ = u b - ⟪gradient u a, b⟫ +
              ⟪d, w - b⟫ + C * ‖w - b‖ ^ 2 := by
          dsimp [d]
          simp only [inner_sub_left, inner_sub_right]
          ring
    have hwz : w - b = -(r • d) := by
      dsimp [w]
      abel
    have hwz' : w - b = (-r) • d := by
      simpa only [neg_smul] using hwz
    have hr : 0 ≤ r := by
      dsimp [r]
      exact le_of_lt (one_div_pos.mpr (by nlinarith [hC]))
    have hnorm : ‖w - b‖ ^ 2 = r ^ 2 * ‖d‖ ^ 2 := by
      rw [hwz, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      ring
    have hdot : ⟪d, w - b⟫ = -r * ‖d‖ ^ 2 := by
      rw [hwz', real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hstar' :
        u a - ⟪gradient u a, a⟫ ≤
          u b - ⟪gradient u a, b⟫ - ‖d‖ ^ 2 / (4 * C) := by
      calc
        u a - ⟪gradient u a, a⟫ ≤ u w - ⟪gradient u a, w⟫ := hmin
        _ ≤ u b - ⟪gradient u a, b⟫ +
              ⟪d, w - b⟫ + C * ‖w - b‖ ^ 2 := hupper
        _ = u b - ⟪gradient u a, b⟫ - ‖d‖ ^ 2 / (4 * C) := by
          rw [hdot, hnorm]
          dsimp [r]
          field_simp [ne_of_gt hC]; ring
    simpa [d] using hstar'
  have hxy := hstar x y
  have hyx := hstar y x
  have hnorm_rev :
      ‖gradient u y - gradient u x‖ ^ 2 =
        ‖gradient u x - gradient u y‖ ^ 2 := by
    have heq :
        gradient u y - gradient u x = -(gradient u x - gradient u y) := by
      abel
    rw [heq, norm_neg]
  rw [hnorm_rev] at hxy
  have hi :
      ⟪gradient u x - gradient u y, x - y⟫ =
        ⟪gradient u x, x⟫ + ⟪gradient u y, y⟫ -
          ⟪gradient u x, y⟫ - ⟪gradient u y, x⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hdiv :
      ‖gradient u x - gradient u y‖ ^ 2 / (4 * C) +
          ‖gradient u x - gradient u y‖ ^ 2 / (4 * C) =
        ‖gradient u x - gradient u y‖ ^ 2 / (2 * C) := by
    field_simp [ne_of_gt hC]; ring
  have hmono :
      ‖gradient u x - gradient u y‖ ^ 2 / (2 * C) ≤
        ⟪gradient u x - gradient u y, x - y⟫ := by
    have hsum := add_le_add hxy hyx
    linarith [hsum, hdiv, hi]
  have hinner :
      ⟪gradient u x - gradient u y, x - y⟫ ≤
        ‖gradient u x - gradient u y‖ * ‖x - y‖ :=
    real_inner_le_norm _ _
  have h2C : 0 < 2 * C := by
    nlinarith [hC]
  have hmul :
      ‖gradient u x - gradient u y‖ ^ 2 ≤
        ⟪gradient u x - gradient u y, x - y⟫ * (2 * C) :=
    (div_le_iff₀ h2C).mp hmono
  have hprod :
      ⟪gradient u x - gradient u y, x - y⟫ * (2 * C) ≤
        (‖gradient u x - gradient u y‖ * ‖x - y‖) * (2 * C) :=
    mul_le_mul_of_nonneg_right hinner (le_of_lt h2C)
  by_cases ha : ‖gradient u x - gradient u y‖ = 0
  · rw [ha]
    positivity
  · have ha_pos : 0 < ‖gradient u x - gradient u y‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
    have hsq :
        ‖gradient u x - gradient u y‖ *
            ‖gradient u x - gradient u y‖ ≤
          ‖gradient u x - gradient u y‖ * (2 * C * ‖x - y‖) := by
      calc
        ‖gradient u x - gradient u y‖ *
            ‖gradient u x - gradient u y‖ =
            ‖gradient u x - gradient u y‖ ^ 2 := by ring
        _ ≤ ⟪gradient u x - gradient u y, x - y⟫ * (2 * C) := hmul
        _ ≤ (‖gradient u x - gradient u y‖ * ‖x - y‖) * (2 * C) := hprod
        _ = ‖gradient u x - gradient u y‖ * (2 * C * ‖x - y‖) := by
          ring
    exact le_of_mul_le_mul_left hsq ha_pos

end CocoerciveGradient

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section SecondDifferenceLipschitz



/-! Lipschitz gradient from a second-difference bound. -/

/-- **A second-difference bound gives a Lipschitz gradient**: a differentiable convex function with
`u(x + h) + u(x − h) − 2 u(x) ≤ C ‖h‖²` for all `x, h` has a `4C`-Lipschitz gradient. -/
theorem lipschitzWith_gradient_of_second_difference_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {u : E → ℝ} {C : ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) (hC : 0 ≤ C)
    (hsd : ∀ x h : E, u (x + h) + u (x - h) - 2 * u x ≤ C * ‖h‖ ^ 2) :
    LipschitzWith (Real.toNNReal (4 * C)) (gradient u) := by
  have hlineconv (x h : E) :
      ConvexOn ℝ Set.univ (u ∘ fun t : ℝ => x + t • h) := by
    refine ⟨convex_univ, ?_⟩
    intro a _ha b _hb p q hp hq hpq
    have hu := hconv.2 (x := x + a • h) (y := x + b • h)
      (Set.mem_univ _) (Set.mem_univ _) hp hq hpq
    have heq :
        p • (x + a • h) + q • (x + b • h) =
          x + (p • a + q • b) • h := by
      calc
        p • (x + a • h) + q • (x + b • h) =
            (p + q) • x + (p • a + q • b) • h := by
              module
        _ = x + (p • a + q • b) • h := by
          rw [hpq, one_smul]
    rw [heq] at hu
    simpa only [Function.comp_apply] using hu
  have hfirst (x h : E) :
      inner ℝ (gradient u x) h ≤ u (x + h) - u x := by
    have hld₀ :=
      ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const h).const_add x
    have hld : HasDerivAt (fun t : ℝ => x + t • h) h 0 := by
      simpa only [id_eq, one_smul ℝ h] using hld₀
    have hu0 :
        HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • h) := by
      simpa only [zero_smul, add_zero] using
        (hdiff (x + (0 : ℝ) • h)).hasFDerivAt
    have hcomp := hu0.comp_hasDerivAt (0 : ℝ) hld
    have hderiv :
        deriv (u ∘ fun t : ℝ => x + t • h) 0 =
          inner ℝ (gradient u x) h := by
      rw [hcomp.deriv]
      change (fderiv ℝ u x) h =
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) h
      simp only [InnerProductSpace.toDual_symm_apply]
    have hm :=
      (hlineconv x h).deriv_le_slope (x := 0) (y := 1)
        (Set.mem_univ _) (Set.mem_univ _) (by norm_num) hcomp.differentiableAt
    rw [hderiv] at hm
    simpa [slope, Function.comp_def] using hm
  have hupper (x h : E) :
      u (x + h) - u x - inner ℝ (gradient u x) h ≤ C * ‖h‖ ^ 2 := by
    have hh := hfirst x (-h)
    have hh' :
        -inner ℝ (gradient u x) h ≤ u (x - h) - u x := by
      simpa [sub_eq_add_neg] using hh
    linarith [hsd x h, hh']
  by_cases hCzero : C = 0
  · have heq0 (x h : E) :
        u (x + h) = u x + inner ℝ (gradient u x) h := by
      have hl := hfirst x h
      have hu := hupper x h
      have hu' :
          u (x + h) - u x - inner ℝ (gradient u x) h ≤ 0 := by
        rw [hCzero, zero_mul] at hu
        exact hu
      linarith only [hl, hu']
    have haff (x z : E) :
        u z = u x + inner ℝ (gradient u x) (z - x) := by
      have hh := heq0 x (z - x)
      have hx : x + (z - x) = z := by
        abel
      rw [hx] at hh
      exact hh
    have hinner (x y h : E) :
        inner ℝ (gradient u x) h = inner ℝ (gradient u y) h := by
      have e₁ := haff x (x + h)
      have hx : (x + h) - x = h := by
        abel
      rw [hx] at e₁
      have e₂ := haff y (x + h)
      have hxy : (x + h) - y = (x - y) + h := by
        abel
      rw [hxy, inner_add_right] at e₂
      have e₃ := haff x y
      have e₃' :
          u y = u x - inner ℝ (gradient u x) (x - y) := by
        calc
          u y = u x + inner ℝ (gradient u x) (y - x) := e₃
          _ = u x - inner ℝ (gradient u x) (x - y) := by
            rw [show y - x = -(x - y) by abel]
            rw [inner_neg_right]
            ring
      have e₄ := haff y x
      have hdir :
          inner ℝ (gradient u x) (x - y) =
            inner ℝ (gradient u y) (x - y) := by
        have hax :
            inner ℝ (gradient u x) (x - y) = u x - u y := by
          calc
            inner ℝ (gradient u x) (x - y) =
                u x - (u x - inner ℝ (gradient u x) (x - y)) := by
                  ring
            _ = u x - u y := by rw [← e₃']
        have hbx :
            inner ℝ (gradient u y) (x - y) = u x - u y := by
          calc
            inner ℝ (gradient u y) (x - y) =
                (u y + inner ℝ (gradient u y) (x - y)) - u y := by
                  ring
            _ = u x - u y := by rw [e₄]
        exact hax.trans hbx.symm
      have e₂' :
          u (x + h) =
            u x - inner ℝ (gradient u x) (x - y) +
              (inner ℝ (gradient u x) (x - y) +
                inner ℝ (gradient u y) h) := by
        rw [e₃'] at e₂
        rw [← hdir] at e₂
        exact e₂
      have e₂'' :
          u x + inner ℝ (gradient u x) h =
            u x + inner ℝ (gradient u y) h := by
        calc
          u x + inner ℝ (gradient u x) h = u (x + h) := by
            exact e₁.symm
          _ = u x - inner ℝ (gradient u x) (x - y) +
              (inner ℝ (gradient u x) (x - y) +
                inner ℝ (gradient u y) h) := e₂'
          _ = u x + inner ℝ (gradient u y) h := by
            ring
      exact add_left_cancel e₂''
    have hgrad_eq (x y : E) : gradient u x = gradient u y := by
      have hh := hinner x y (gradient u x - gradient u y)
      have hz :
          inner ℝ (gradient u x - gradient u y)
              (gradient u x - gradient u y) = 0 := by
        calc
          inner ℝ (gradient u x - gradient u y)
              (gradient u x - gradient u y) =
              inner ℝ (gradient u x) (gradient u x - gradient u y) -
                inner ℝ (gradient u y) (gradient u x - gradient u y) := by
                  rw [inner_sub_left]
          _ = 0 := sub_eq_zero.mpr hh
      let v : E := gradient u x - gradient u y
      have hz' : inner ℝ v v = 0 := by
        exact hz
      have hn : ‖v‖ ^ 2 = 0 := by
        calc
          ‖v‖ ^ 2 = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
          _ = 0 := hz'
      have hzero : v = 0 :=
        norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
      exact sub_eq_zero.mp hzero
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    rw [hgrad_eq x y]
    simp [hCzero]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hcoercive (x y : E) :
        ‖gradient u x - gradient u y‖ ^ 2 ≤
          4 * C * inner ℝ (gradient u x - gradient u y) (x - y) := by
      let d : E := gradient u x - gradient u y
      let t : ℝ := (2 * C)⁻¹
      let z : E := y + t • d
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hmin := hfirst x (z - x)
      have hmin' :
          inner ℝ (gradient u x) (y - x) +
              inner ℝ (gradient u x) (t • d) ≤ u z - u x := by
        have hz : x + (z - x) = z := by
          abel
        rw [hz] at hmin
        have hz' : z - x = (y - x) + t • d := by
          dsimp [z]
          abel
        rw [hz', inner_add_right] at hmin
        exact hmin
      have hu :
          u z - u y - inner ℝ (gradient u y) (t • d) ≤
            C * ‖t • d‖ ^ 2 := by
        change u (y + t • d) - u y - inner ℝ (gradient u y) (t • d) ≤
          C * ‖t • d‖ ^ 2
        exact hupper y (t • d)
      have hyx := hfirst y (x - y)
      have hyx' :
          inner ℝ (gradient u y) (x - y) ≤ u x - u y := by
        have hx : y + (x - y) = x := by
          abel
        rw [hx] at hyx
        exact hyx
      have hneg :
          inner ℝ (gradient u x) (y - x) =
            -inner ℝ (gradient u x) (x - y) := by
        rw [show y - x = -(x - y) by abel]
        rw [inner_neg_right]
      rw [hneg] at hmin'
      have h₁ :
          inner ℝ (gradient u x) (t • d) -
              inner ℝ (gradient u y) (t • d) =
            inner ℝ d (t • d) := by
        rw [inner_sub_left]
      have h₂ :
          inner ℝ (gradient u x) (x - y) -
              inner ℝ (gradient u y) (x - y) =
            inner ℝ d (x - y) := by
        rw [inner_sub_left]
      have hgap :
          inner ℝ d (t • d) - C * ‖t • d‖ ^ 2 ≤
            inner ℝ d (x - y) := by
        linarith only [hmin', hu, hyx', h₁, h₂]
      have hself : inner ℝ d d = ‖d‖ ^ 2 :=
        real_inner_self_eq_norm_sq d
      have hdt :
          inner ℝ d (t • d) - C * ‖t • d‖ ^ 2 =
            ‖d‖ ^ 2 / (4 * C) := by
        rw [inner_smul_right, hself, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht]
        dsimp [t]
        field_simp [ne_of_gt hCpos]
        ring
      have hgap' :
          ‖d‖ ^ 2 / (4 * C) ≤ inner ℝ d (x - y) := by
        rw [← hdt]
        exact hgap
      have hmul :
          ‖d‖ ^ 2 ≤ 4 * C * inner ℝ d (x - y) := by
        calc
          ‖d‖ ^ 2 = 4 * C * (‖d‖ ^ 2 / (4 * C)) := by
            field_simp [ne_of_gt hCpos]
          _ ≤ 4 * C * inner ℝ d (x - y) :=
            mul_le_mul_of_nonneg_left hgap' (by linarith)
      exact hmul
    have hnorm (x y : E) :
        ‖gradient u x - gradient u y‖ ≤
          4 * C * ‖x - y‖ := by
      let d : E := gradient u x - gradient u y
      have hco :
          ‖d‖ ^ 2 ≤ 4 * C * inner ℝ d (x - y) := by
        dsimp [d]
        exact hcoercive x y
      have hcs := real_inner_le_norm d (x - y)
      have hmulcs :
          4 * C * inner ℝ d (x - y) ≤
            4 * C * (‖d‖ * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hcs (by linarith)
      have hmul :
          ‖d‖ * (‖d‖ - 4 * C * ‖x - y‖) ≤ 0 := by
        nlinarith [hco, hmulcs]
      by_cases hdzero : ‖d‖ = 0
      · change ‖d‖ ≤ 4 * C * ‖x - y‖
        rw [hdzero]
        positivity
      · have hdpos : 0 < ‖d‖ :=
          lt_of_le_of_ne (norm_nonneg d) (Ne.symm hdzero)
        by_contra hn
        have hnot : 4 * C * ‖x - y‖ < ‖d‖ := lt_of_not_ge hn
        have hprod :
            0 < ‖d‖ * (‖d‖ - 4 * C * ‖x - y‖) :=
          mul_pos hdpos (sub_pos.mpr hnot)
        linarith
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have h4C : 0 ≤ 4 * C := by
      linarith
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal (4 * C) h4C]
    exact hnorm x y

end SecondDifferenceLipschitz

end FunctionalInequalities.Analysis

section PenalizedMaximumBound

open Set
open scoped RealInnerProductSpace

/-! Second differences at maximisers of a penalized second difference (weak Letwin route, C^{1,1} estimate). -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma sd_support [FiniteDimensional ℝ E] {f : E → ℝ}
    (hc : ConvexOn ℝ univ f) (hf : Differentiable ℝ f) (x y : E) :
    fderiv ℝ f x (y - x) ≤ f y - f x := by
  have hp : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (y - x)) := by
    simpa only [zero_smul, add_zero] using (hf x).hasFDerivAt
  have hl := hd.comp_hasDerivAt 0 hp
  have hc' : ConvexOn ℝ univ (fun t : ℝ => f (x + t • (y - x))) := by
    simpa only [Set.preimage_univ, Function.comp_def,
      AffineMap.lineMap_apply_module', add_comm] using
      hc.comp_affineMap (AffineMap.lineMap x y)
  simpa only [slope_def_field, zero_smul, add_zero, one_smul,
    add_sub_cancel, sub_zero, div_one] using
    hc'.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hl

private lemma sd_stationary [FiniteDimensional ℝ E] {u : E → ℝ}
    (hu : Differentiable ℝ u) (x h : E) (η : ℝ)
    (hm : ∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
      u (x + h) + u (x - h) - 2 * u x - η * u x) :
    gradient u (x + h) + gradient u (x - h) - (2 : ℝ) • gradient u x =
      η • gradient u x := by
  let T := InnerProductSpace.toDual ℝ E
  have ha : HasFDerivAt (fun y => u (y + h))
      (T (gradient u (x + h))) x := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      ((hu (x + h)).hasGradientAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).add_const h))
  have hb : HasFDerivAt (fun y => u (y - h))
      (T (gradient u (x - h))) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      ((hu (x - h)).hasGradientAt.hasFDerivAt.comp x
        (hasFDerivAt_sub_const h))
  have hd := ((ha.add hb).sub
    ((hu x).hasGradientAt.hasFDerivAt.const_mul 2)).sub
      ((hu x).hasGradientAt.hasFDerivAt.const_mul η)
  have hm' : IsLocalMax
      (fun y => u (y + h) + u (y - h) - 2 * u y - η * u y) x :=
    Filter.Eventually.of_forall hm
  have hz := hm'.hasFDerivAt_eq_zero hd
  apply ext_inner_right ℝ
  intro v
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hz
  simp only [T, add_apply, sub_apply, smul_apply, smul_eq_mul,
    zero_apply, InnerProductSpace.toDual_apply_apply] at he
  simpa only [inner_sub_left, inner_add_left, real_inner_smul_left] using
    (sub_eq_zero.mp he)

private lemma sd_midpoint {V : E → ℝ} {κ : ℝ}
    (hs : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (p w : E) :
    κ * ‖w‖ ^ 2 ≤ V (p + w) + V (p - w) - 2 * V p := by
  have he : (1 / 2 : ℝ) • (p + w) + (1 / 2 : ℝ) • (p - w) = p := by
    module
  have hc := hs.2 (mem_univ (p + w)) (mem_univ (p - w))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  rw [he] at hc
  simp only [smul_eq_mul, norm_add_sq_real, norm_sub_sq_real] at hc
  nlinarith

private lemma sd_quadratic (κ q H B : ℝ) (hk : 0 < κ)
    (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hq : κ * q ^ 2 ≤ 2 * H * q + B) :
    q ≤ 2 * H / κ + Real.sqrt (B / κ) := by
  have hs := Real.sq_sqrt (div_nonneg hB hk.le)
  have hp := Real.sqrt_nonneg (B / κ)
  have hd : 0 ≤ 2 * H / κ := div_nonneg (by positivity) hk.le
  have he : κ * (2 * H / κ) = 2 * H := by
    field_simp
  have hb : κ * (B / κ) = B := by
    field_simp
  by_contra hn
  have hh : 2 * H / κ + Real.sqrt (B / κ) < q := lt_of_not_ge hn
  have hprod := mul_pos (sub_pos.mpr hh)
    (show 0 < q - 2 * H / κ + Real.sqrt (B / κ) by linarith)
  have hquad : q ^ 2 ≤ (2 * H / κ) * q + B / κ := by
    nlinarith
  nlinarith [mul_nonneg hd (show 0 ≤ q - 2 * H / κ by linarith)]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in
private lemma sd_penalized_estimate {u V : E → ℝ}
    (hconv : ConvexOn ℝ univ u) (hu : Differentiable ℝ u)
    (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    {C : ℝ} (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C)
    (n : ℕ) (h x₀ : E) {η : ℝ} (hη : 0 < η)
    (hmaximum : ∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
      u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀)
    (hcomparison :
      (V (gradient u (x₀ + h)) - u (x₀ + h)) +
        (V (gradient u (x₀ - h)) - u (x₀ - h)) -
        2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
    u (x₀ + h) + u (x₀ - h) - 2 * u x₀ ≤
      4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * (n + C) / κ) := by
  let a := gradient u (x₀ + h)
  let b := gradient u (x₀ - h)
  let c := gradient u x₀
  let p := (1 / 2 : ℝ) • (a + b)
  let w := (1 / 2 : ℝ) • (a - b)
  let D := u (x₀ + h) + u (x₀ - h) - 2 * u x₀

  have hstationary : a + b - (2 : ℝ) • c = η • c :=
    sd_stationary hu x₀ h η hmaximum
  have hp : p - c = (η / 2) • c := by
    have ht : p - c = (1 / 2 : ℝ) • (a + b - (2 : ℝ) • c) := by
      dsimp [p]
      module
    rw [ht, hstationary]
    module

  have ha := sd_support hconv hu (x₀ + h) x₀
  have hb := sd_support hconv hu (x₀ - h) x₀
  rw [show x₀ - (x₀ + h) = -h by abel,
    (hu (x₀ + h)).hasGradientAt.hasFDerivAt.fderiv,
    InnerProductSpace.toDual_apply_apply] at ha
  rw [show x₀ - (x₀ - h) = h by abel,
    (hu (x₀ - h)).hasGradientAt.hasFDerivAt.fderiv,
    InnerProductSpace.toDual_apply_apply] at hb
  change ⟪a, -h⟫ ≤ u x₀ - u (x₀ + h) at ha
  change ⟪b, h⟫ ≤ u x₀ - u (x₀ - h) at hb
  have hn : ‖w‖ = (1 / 2 : ℝ) * ‖a - b‖ := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hD : D ≤ 2 * ‖h‖ * ‖w‖ := by
    have hi := real_inner_le_norm (a - b) h
    rw [inner_sub_left] at hi
    rw [inner_neg_right] at ha
    dsimp [D]
    rw [hn]
    nlinarith only [ha, hb, hi]

  have hconvV : ConvexOn ℝ univ V := by
    have hn' : ConvexOn ℝ univ (fun y : E => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he :
        (fun y => V y - κ / 2 * ‖y‖ ^ 2) +
          (fun y => (κ / 2) • ‖y‖ ^ 2) = V := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  have hpa : p + w = a := by
    dsimp [p, w]
    module
  have hpb : p - w = b := by
    dsimp [p, w]
    module
  have hmid := sd_midpoint hstrong p w
  rw [hpa, hpb] at hmid
  have hs := sd_support hconvV hV c p
  rw [hp, map_smul, smul_eq_mul] at hs
  have hc : -C ≤ fderiv ℝ V c c :=
    (neg_le_neg (hC x₀)).trans (neg_abs_le _)
  have he := mul_le_mul_of_nonneg_left hc hη.le
  have hcomp : V a + V b - 2 * V c ≤ D + η * (n : ℝ) := by
    dsimp [a, b, c, D]
    linarith only [hcomparison]
  have hgap : κ * ‖w‖ ^ 2 ≤ D + η * ((n : ℝ) + C) := by
    nlinarith only [hmid, hs, he, hcomp]
  have hCnonneg : 0 ≤ C :=
    (abs_nonneg (fderiv ℝ V (gradient u x₀) (gradient u x₀))).trans (hC x₀)
  have hB : 0 ≤ η * ((n : ℝ) + C) := by
    positivity
  have hquad : κ * ‖w‖ ^ 2 ≤
      2 * ‖h‖ * ‖w‖ + η * ((n : ℝ) + C) := by
    linarith only [hgap, hD]
  have hq := sd_quadratic κ ‖w‖ ‖h‖ (η * ((n : ℝ) + C))
    hκ (norm_nonneg h) hB hquad
  have ht := hD.trans (mul_le_mul_of_nonneg_left hq
    (show 0 ≤ 2 * ‖h‖ by positivity))
  have he' :
      2 * ‖h‖ * (2 * ‖h‖ / κ + Real.sqrt (η * ((n : ℝ) + C) / κ)) =
        4 * ‖h‖ ^ 2 / κ +
          2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) := by
    ring
  rw [he'] at ht
  exact ht

/-- **Second-difference bound from penalised maxima** (weak Letwin route, algebraic part): let `u` be convex and
differentiable, bounded below, and `V` differentiable with `V − (κ/2)‖·‖²` convex. Suppose that for every
`η > 0` the penalised second difference `Δ²ₕu − η u` has a maximiser `x₀` at which the log-density
`F := V ∘ ∇u − u` satisfies the comparison `F(x₀ + h) + F(x₀ − h) − 2 F(x₀) ≤ η n`. Then
`u(x + h) + u(x − h) − 2 u(x) ≤ 4 ‖h‖² / κ` everywhere. -/
theorem secondDifference_le_of_penalized_maxima {u V : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hu : Differentiable ℝ u) (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2)) {C : ℝ}
    (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C) {m : ℝ} (hm : ∀ x, m ≤ u x)
    (n : ℕ) (h : E)
    (hmax : ∀ η > 0, ∃ x₀ : E,
      (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
        u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
      (V (gradient u (x₀ + h)) - u (x₀ + h)) + (V (gradient u (x₀ - h)) - u (x₀ - h)) -
        2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
    ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ 4 * ‖h‖ ^ 2 / κ := by
  intro x
  have hb : ∀ η > 0, u (x + h) + u (x - h) - 2 * u x ≤
      4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) +
        η * (u x - m) := by
    intro η hη
    obtain ⟨x₀, hmaximum, hcomparison⟩ := hmax η hη
    have hD := sd_penalized_estimate hconv hu hV hκ hstrong hC
      n h x₀ hη hmaximum hcomparison
    have hx := hmaximum x
    have hlower := mul_le_mul_of_nonneg_left (hm x₀) hη.le
    linarith only [hD, hx, hlower]
  have hc : Continuous (fun η : ℝ =>
      4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) +
        η * (u x - m)) :=
    (continuous_const.add
      (continuous_const.mul
        (Real.continuous_sqrt.comp
          ((continuous_id.mul continuous_const).div_const κ)))).add
      (continuous_id.mul continuous_const)
  have hl : Filter.Tendsto
      (fun η : ℝ =>
        4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) +
          η * (u x - m))
      (nhdsWithin 0 (Ioi 0)) (nhds (4 * ‖h‖ ^ 2 / κ)) := by
    simpa only [zero_mul, zero_div, Real.sqrt_zero, mul_zero, add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
  apply ge_of_tendsto hl
  exact Filter.Eventually.mono self_mem_nhdsWithin (fun η hη => hb η hη)

end FiniteDimensional

end InnerProduct

end FunctionalInequalities.Analysis

end PenalizedMaximumBound

section CenteredDifference

open Set Filter
open scoped Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

theorem fderiv_centeredDifference {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y) =
      fun y => fderiv ℝ u (y + h) + fderiv ℝ u (y - h) -
        (fderiv ℝ u y + fderiv ℝ u y) := by
  funext y
  have hp : DifferentiableAt ℝ (fun z => u (z + h)) y :=
    (hu (y + h)).comp y (differentiableAt_id.add_const h)
  have hm : DifferentiableAt ℝ (fun z => u (z - h)) y :=
    (hu (y - h)).comp y (differentiableAt_id.sub_const h)
  simp only [two_mul]
  rw [fderiv_fun_sub (hp.fun_add hm) ((hu y).fun_add (hu y)),
    fderiv_fun_add hp hm, fderiv_fun_add (hu y) (hu y),
    fderiv_comp_add_right]
  simpa only [sub_eq_add_neg] using
    congrArg
      (fun q => fderiv ℝ u (y + h) + q - (fderiv ℝ u y + fderiv ℝ u y))
      (fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := y) (-h))

theorem gradient_centeredDifference {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Differentiable ℝ u)
    (h x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x =
      gradient u (x + h) + gradient u (x - h) - 2 • gradient u x := by
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (fun y => u (y + h) + u (y - h) - 2 * u y) x) = _
  rw [fderiv_centeredDifference hu h]
  simp only [map_sub, map_add, gradient, two_smul]

/-- Consumer adapter for the centered second difference used in the weak
Letwin Hessian increment estimate. C1 and the gradient Lipschitz bound suffice. -/
theorem centeredDifference_contDiff_lipschitz_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    (h : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (fun x => u (x + h) + u (x - h) - 2 * u x) ∧
      LipschitzWith (4 * G)
        (gradient (fun x => u (x + h) + u (x - h) - 2 * u x)) := by
  have hdu : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hcp : ContDiff ℝ 1
      (fun x : EuclideanSpace ℝ (Fin n) => x + h) :=
    contDiff_id.add contDiff_const
  have hcm : ContDiff ℝ 1
      (fun x : EuclideanSpace ℝ (Fin n) => x - h) :=
    contDiff_id.sub contDiff_const
  have hp : ContDiff ℝ 1 (fun x => u (x + h)) := by
    simpa only [Function.comp_def] using hu.comp hcp
  have hm : ContDiff ℝ 1 (fun x => u (x - h)) := by
    simpa only [Function.comp_def] using hu.comp hcm
  have htwo : ContDiff ℝ 1 (fun x => 2 * u x) := by
    simpa only [two_mul] using hu.add hu
  have hC1 :
      ContDiff ℝ 1 (fun x => u (x + h) + u (x - h) - 2 * u x) :=
    (hp.add hm).sub htwo
  have htp : LipschitzWith (1 : NNReal)
      (fun x : EuclideanSpace ℝ (Fin n) => x + h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_add_right, le_refl]
  have htm : LipschitzWith (1 : NNReal)
      (fun x : EuclideanSpace ℝ (Fin n) => x - h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_sub_right, le_refl]
  have hGp : LipschitzWith G (fun x => gradient u (x + h)) := by
    simpa only [Function.comp_def, mul_one] using hG.comp htp
  have hGm : LipschitzWith G (fun x => gradient u (x - h)) := by
    simpa only [Function.comp_def, mul_one] using hG.comp htm
  have hG2 : LipschitzWith (2 * G)
      (fun x => (2 : ℕ) • gradient u x) := by
    simpa only [two_mul, two_smul] using hG.add hG
  have hgrad : LipschitzWith (G + G + 2 * G)
      (fun x => gradient u (x + h) + gradient u (x - h) -
        (2 : ℕ) • gradient u x) :=
    (hGp.add hGm).sub hG2
  have hfun :
      (fun x => gradient u (x + h) + gradient u (x - h) -
        (2 : ℕ) • gradient u x) =
      gradient (fun x => u (x + h) + u (x - h) - 2 * u x) := by
    funext x
    exact (gradient_centeredDifference hdu h x).symm
  have hconst : G + G + 2 * G = 4 * G := by
    ring
  rw [hconst, hfun] at hgrad
  exact ⟨hC1, hgrad⟩


/-- The centered difference bounds required by the Hessian-increment
energy estimate, with no differentiability or sign assumption on D. -/
theorem centeredDifference_nonneg_le {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u)
    {D : ℝ} (h : EuclideanSpace ℝ (Fin n))
    (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    (∀ x, 0 ≤ u (x + h) + u (x - h) - 2 * u x ∧
      u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) ∧
      0 ≤ D * ‖h‖ ^ 2 := by
  have hlower : ∀ x, 0 ≤ u (x + h) + u (x - h) - 2 * u x := by
    intro x
    have hmid :
        (1 / 2 : ℝ) • (x + h) + (1 / 2 : ℝ) • (x - h) = x := by
      apply PiLp.ext
      intro i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [← mul_add, add_add_sub_cancel, ← two_mul, ← mul_assoc]
      norm_num
    have hj :=
      hconv.2 (mem_univ (x + h)) (mem_univ (x - h))
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)
    simp only [hmid, smul_eq_mul] at hj
    apply sub_nonneg.mpr
    calc
      2 * u x = u x + u x := two_mul (u x)
      _ ≤ ((1 / 2 : ℝ) * u (x + h) + (1 / 2 : ℝ) * u (x - h)) +
          ((1 / 2 : ℝ) * u (x + h) + (1 / 2 : ℝ) * u (x - h)) :=
        add_le_add hj hj
      _ = u (x + h) + u (x - h) := by
        rw [add_add_add_comm, ← add_mul, ← add_mul]
        norm_num
  exact ⟨fun x => ⟨hlower x, hw x⟩,
    le_trans (hlower (0 : EuclideanSpace ℝ (Fin n))) (hw 0)⟩

end FunctionalInequalities.Analysis

end CenteredDifference

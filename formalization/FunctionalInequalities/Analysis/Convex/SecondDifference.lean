import Mathlib

/-!
# Second differences and Lipschitz gradients

A convex differentiable function with `u(x+h) + u(x−h) − 2u(x) ≤ C‖h‖²` has a quadratic upper bound, a co-coercive
gradient and a `4C`-Lipschitz gradient (final step of the `C^{1,1}` estimate of the weak moment-map route to Letwin
arXiv:2607.24164v1). Proof bodies: GPT (Letwin sub-controller tasks L-T4a, L-T4b, W0T4); statements by Claude and the
Letwin sub-controller; placement: Claude.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

private lemma gradient_le_increment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : E → ℝ} (hc : ConvexOn ℝ Set.univ u)
    (z v : E) (hz : DifferentiableAt ℝ u z) :
    ⟪gradient u z, v⟫ ≤ u (z + v) - u z := by
  have hd :
      HasFDerivAt u ((InnerProductSpace.toDual ℝ E) (gradient u z))
        ((AffineMap.lineMap (k := ℝ) z (z + v)) (0 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero] using hz.hasGradientAt.hasFDerivAt
  have hl :
      HasDerivAt (u ∘ ⇑(AffineMap.lineMap (k := ℝ) z (z + v)))
        ⟪gradient u z, v⟫ (0 : ℝ) := by
    simpa only [add_sub_cancel_left, InnerProductSpace.toDual_apply_apply] using
      hd.comp_hasDerivAt 0
        (AffineMap.hasDerivAt_lineMap (a := z) (b := z + v) (x := (0 : ℝ)))
  have hcl :
      ConvexOn ℝ Set.univ (u ∘ ⇑(AffineMap.lineMap (k := ℝ) z (z + v))) := by
    simpa only [Set.preimage_univ] using
      ConvexOn.comp_affineMap (AffineMap.lineMap (k := ℝ) z (z + v)) hc
  simpa only [slope_def_field, Function.comp_apply,
    AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, sub_zero, div_one] using
    hcl.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
      (zero_lt_one : (0 : ℝ) < 1) hl

/-- **Quadratic upper bound from a second-difference bound** (weak Letwin route, C^{1,1} step N9,
support for T4): a differentiable convex `u` with `u(x+h) + u(x−h) − 2u(x) ≤ C‖h‖²` satisfies
`u y ≤ u x + ⟪∇u x, y − x⟫ + C ‖y − x‖²`. -/
theorem le_add_inner_gradient_add_mul_sq_of_second_difference_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {u : E → ℝ} {C : ℝ}
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

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section LT4BCocoerciveGradient

open scoped RealInnerProductSpace

/-! Co-coercivity of the gradient (task L-T4b). -/

/-- **Co-coercivity: a quadratic upper bound gives a Lipschitz gradient** (weak Letwin route, C^{1,1}
step N9, support for T4): if a differentiable convex `u` satisfies
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

end LT4BCocoerciveGradient

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section W0T4SecondDifferenceLipschitz



/-! Lipschitz gradient from a second-difference bound (task W0T4). -/

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

end W0T4SecondDifferenceLipschitz

end FunctionalInequalities.Analysis

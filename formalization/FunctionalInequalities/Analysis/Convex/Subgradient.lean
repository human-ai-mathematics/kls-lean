import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Subgradients of convex functions

Pointwise subgradients are written inline, `∀ y, u x + ⟪p, y - x⟫ ≤ u y`. A differentiable convex function on a
finite-dimensional space is `C¹` (`contDiff_one_of_convexOn_of_differentiable`), and the subgradients of a convex
Lipschitz function lie in every closed convex set containing its a.e. gradient
(`subgradient_mem_of_ae_gradient_mem`). Weak moment-map route to Letwin arXiv:2607.24164v1, Theorem 1.2 (nodes N4,
N7 of build/reviews/2026-10-12-bkl-claude-goal/routes/letwin-weak-route.md). Proof bodies: GPT (BKL
Claude-controller goal, Letwin sub-controller tasks L-T5b, L-T11a); statements by the Letwin sub-controller;
placement: Claude.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section ConvexC1

/-- **A differentiable convex function on a finite-dimensional space is `C¹`** (weak Letwin
route, step N7): convexity makes the derivative map continuous. -/
theorem contDiff_one_of_convexOn_of_differentiable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) :
    ContDiff ℝ 1 u := by
  have hline (x w : E) :
      HasDerivAt (fun t : ℝ => u (x + t • w)) (fderiv ℝ u x w) 0 := by
    have hp : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hu : HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • w) := by
      simpa only [zero_smul, add_zero] using (hdiff x).hasFDerivAt
    exact hu.comp_hasDerivAt 0 hp

  -- The supporting hyperplane inequality follows from convexity on each line.
  have hsupport (x y : E) :
      fderiv ℝ u x (y - x) ≤ u y - u x := by
    have hc : ConvexOn ℝ Set.univ
        (fun t : ℝ => u (x + t • (y - x))) := by
      simpa only [Set.preimage_univ, Function.comp_def,
        AffineMap.lineMap_apply_module', add_comm] using
        hconv.comp_affineMap (AffineMap.lineMap x y)
    simpa only [slope_def_field, zero_smul, add_zero, one_smul,
      add_sub_cancel, sub_zero, div_one] using
      hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
        zero_lt_one (hline x (y - x))

  have hbound (x w : E) (t : ℝ) (ht : 0 < t) :
      fderiv ℝ u x w ≤ (u (x + t • w) - u x) / t := by
    apply (le_div_iff₀ ht).2
    have h := hsupport x (x + t • w)
    simpa only [add_sub_cancel_left, map_smul, smul_eq_mul, mul_comm] using h

  -- For fixed direction, positive difference quotients give continuous upper bounds.
  have hupper (w x : E) (a : ℝ) (ha : fderiv ℝ u x w < a) :
      ∀ᶠ z in nhds x, fderiv ℝ u z w < a := by
    have hlim :
        Filter.Tendsto (fun t : ℝ => (u (x + t • w) - u x) / t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ u x w)) := by
      simpa only [zero_add, zero_smul, add_zero, smul_eq_mul,
        div_eq_mul_inv, mul_comm] using
        (hline x w).tendsto_slope_zero.mono_left
          (nhdsGT_le_nhdsNE (0 : ℝ))
    have hev := (hlim.eventually_lt_const ha).and
      (self_mem_nhdsWithin :
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t)
    obtain ⟨t, ht, htpos⟩ := hev.exists
    have hc : Continuous (fun z : E => (u (z + t • w) - u z) / t) :=
      ((hdiff.continuous.comp (continuous_id.add continuous_const)).sub
        hdiff.continuous).div_const t
    exact (hc.continuousAt.eventually_lt continuousAt_const ht).mono
      (fun z hz => lt_of_le_of_lt (hbound z w t htpos) hz)

  -- Applying the upper bound to the negative direction also gives a lower bound.
  have heval (w : E) : Continuous (fun x => fderiv ℝ u x w) := by
    apply continuous_iff_continuousAt.2
    intro x
    apply tendsto_order.2
    constructor
    · intro a ha
      have hn : fderiv ℝ u x (-w) < -a := by
        simpa only [map_neg] using neg_lt_neg ha
      exact (hupper (-w) x (-a) hn).mono fun z hz => by
        simpa only [map_neg, neg_lt_neg_iff] using hz
    · intro a ha
      exact hupper w x a ha

  -- In finite dimension, continuity on a basis gives continuity in operator norm.
  apply contDiff_one_iff_fderiv.2
  refine ⟨hdiff, ?_⟩
  let b := Module.finBasis ℝ E
  let L : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ) :=
    (b.constr ℝ).trans LinearMap.toContinuousLinearMap
  have hL : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have heq (x : E) :
      L (fun i => fderiv ℝ u x (b i)) = fderiv ℝ u x := by
    apply ContinuousLinearMap.ext
    intro w
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f w)
      (b.constr_self ℝ (fderiv ℝ u x).toLinearMap)
  exact (hL.comp (continuous_pi (fun i => heval (b i)))).congr heq

end ConvexC1

section SubgradientRange

private lemma gradient_le_increment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : E → ℝ} (hc : ConvexOn ℝ univ u)
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
      ConvexOn ℝ univ (u ∘ ⇑(AffineMap.lineMap (k := ℝ) z (z + v))) := by
    simpa only [preimage_univ] using
      ConvexOn.comp_affineMap (AffineMap.lineMap (k := ℝ) z (z + v)) hc
  simpa only [slope_def_field, Function.comp_apply,
    AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, sub_zero, div_one] using
    hcl.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1)
      (zero_lt_one : (0 : ℝ) < 1) hl

/-- **Subgradients of a convex Lipschitz function lie in the closed convex range of its a.e.
gradient** (weak Letwin route, step N4: `∂u(x) ⊆ K̄` for the weak moment map, whose gradient lies
a.e. in the target `K`): if `u` is convex and Lipschitz on a finite-dimensional inner product space,
`K` is closed and convex and `∇u(x) ∈ K` for a.e. `x`, then every subgradient `p` of `u` at every
point `x` (`u(x) + ⟪p, y − x⟫ ≤ u(y)` for all `y`) lies in `K`. -/
theorem subgradient_mem_of_ae_gradient_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K)
    {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ K := by
  by_contra hpn
  obtain ⟨f, s, hps, hsep⟩ :=
    geometric_hahn_banach_point_closed hKc hK hpn
  let θ : E := (InnerProductSpace.toDual ℝ E).symm f
  have hθ : ∀ q : E, ⟪q, θ⟫ = f q := by
    intro q
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply

  -- The differentiability points with gradient in K form a dense set.
  have hdense : Dense {z | DifferentiableAt ℝ u z ∧ gradient u z ∈ K} :=
    MeasureTheory.Measure.dense_of_ae
      ((hu.ae_differentiableAt (μ := (volume : Measure E))).and hae)

  -- Convexity gives the bound on the dense set; continuity extends it everywhere.
  have hbound :
      ∀ z ∈ {z | DifferentiableAt ℝ u z ∧ gradient u z ∈ K},
        s ≤ u (z + θ) - u z := by
    intro z hz
    exact (hsep _ hz.2).le.trans
      ((hθ (gradient u z)) ▸ gradient_le_increment hconv z θ hz.1)
  have hb : ∀ z : E, s ≤ u (z + θ) - u z := by
    intro z
    exact hdense.induction hbound
      (isClosed_le continuous_const
        ((hu.continuous.comp (continuous_id.add_const θ)).sub hu.continuous)) z

  have hb' : s ≤ u x - u (x - θ) := by
    simpa only [sub_add_cancel] using hb (x - θ)
  have hp' := hp (x - θ)
  simp only [sub_sub_cancel_left, inner_neg_right, hθ] at hp'
  linarith

end SubgradientRange

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section LT5ASubgradientMaxFormula

open scoped RealInnerProductSpace

/-! Max formula and existence of subgradients (task L-T5a; proof body GPT, statement by the Letwin sub-controller). -/

/-- **Max formula for the one-sided directional derivative of a finite convex function** (weak
Letwin route, step N7 "singleton subdifferential ⇒ C¹"): for a convex `u : E → ℝ` on a
finite-dimensional inner product space, every point `x` and every direction `v`, there is a
subgradient `g` of `u` at `x` whose pairing with `v` is the right derivative
`inf_{t>0} (u(x + t v) - u(x))/t`: it is a subgradient and the difference quotients come
arbitrarily close to `⟪g, v⟫` (they are `≥ ⟪g, v⟫` by the subgradient inequality). -/
theorem exists_subgradient_slope_le_inner_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x v : E) :
    ∃ g : E, (∀ y, u x + ⟪g, y - x⟫ ≤ u y) ∧
      ∀ ε > 0, ∃ t > 0, (u (x + t • v) - u x) / t ≤ ⟪g, v⟫ + ε := by
  let slope : E → ℝ → ℝ := fun w t => (u (x + t • w) - u x) / t
  let p : E → ℝ := fun w =>
    sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
  have hconvex :
      ∀ {z₁ z₂ : E} {a b : ℝ}, z₁ ∈ Set.univ → z₂ ∈ Set.univ →
        0 ≤ a → 0 ≤ b → a + b = 1 →
          u (a • z₁ + b • z₂) ≤ a * u z₁ + b * u z₂ := by
    intro z₁ z₂ a b hz₁ hz₂ ha hb hab
    exact hconv.2 hz₁ hz₂ ha hb hab
  have hslope_mono :
      ∀ {w : E} {a b : ℝ}, 0 < a → a ≤ b → slope w a ≤ slope w b := by
    intro w a b ha hab
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hab0 : 0 ≤ a / b := div_nonneg ha.le hb.le
    have hab1 : 0 ≤ 1 - a / b := sub_nonneg.mpr ((div_le_one hb).2 hab)
    have hsum : a / b + (1 - a / b) = 1 := by
      abel
    have hab' : (a / b) * b = a := div_mul_cancel₀ a (ne_of_gt hb)
    have heq :
        (a / b) • (x + b • w) + (1 - a / b) • x = x + a • w := by
      calc
        (a / b) • (x + b • w) + (1 - a / b) • x =
            (a / b + (1 - a / b)) • x + (a / b * b) • w := by
              module
        _ = x + a • w := by rw [hsum, hab', one_smul]
    have hc := hconvex (z₁ := x + b • w) (z₂ := x) (by simp) (by simp)
      hab0 hab1 hsum
    rw [heq] at hc
    have hc' :
        b * (u (x + a • w) - u x) ≤ a * (u (x + b • w) - u x) := by
      field_simp [ne_of_gt hb] at hc
      nlinarith [hc]
    apply (div_le_div_iff₀ ha hb).2
    nlinarith [hc']
  have hslope_lower :
      ∀ {w : E} {t : ℝ}, 0 < t → u x - u (x - w) ≤ slope w t := by
    intro w t ht
    have htp : 0 < t + 1 := by linarith
    have ha : 0 ≤ t / (t + 1) := div_nonneg ht.le htp.le
    have hb : 0 ≤ (1 : ℝ) / (t + 1) := by positivity
    have hsum : t / (t + 1) + (1 : ℝ) / (t + 1) = 1 := by
      calc
        t / (t + 1) + (1 : ℝ) / (t + 1) =
            (t + 1) / (t + 1) := by
              ring
        _ = 1 := div_self (ne_of_gt htp)
    have hcoef : (1 : ℝ) / (t + 1) * t = t / (t + 1) := by
      ring
    have heq :
        (t / (t + 1)) • (x - w) +
            ((1 : ℝ) / (t + 1)) • (x + t • w) = x := by
      calc
        (t / (t + 1)) • (x - w) +
              ((1 : ℝ) / (t + 1)) • (x + t • w) =
            (t / (t + 1) + (1 : ℝ) / (t + 1)) • x +
              (-(t / (t + 1)) + (1 : ℝ) / (t + 1) * t) • w := by
                module
        _ = x := by rw [hsum, hcoef]; simp
    have hc := hconvex (z₁ := x - w) (z₂ := x + t • w) (by simp) (by simp)
      ha hb hsum
    rw [heq] at hc
    have hc' : t * (u x - u (x - w)) ≤ u (x + t • w) - u x := by
      field_simp [ne_of_gt htp] at hc
      nlinarith [hc]
    apply (le_div_iff₀ ht).2
    nlinarith [hc']
  have hnonempty (w : E) :
      (Set.range (fun t : {t : ℝ // 0 < t} => slope w t)).Nonempty := by
    let t : {t : ℝ // 0 < t} := ⟨1, by norm_num⟩
    exact ⟨slope w t, ⟨t, rfl⟩⟩
  have hbdd (w : E) :
      BddBelow (Set.range (fun t : {t : ℝ // 0 < t} => slope w t)) := by
    refine ⟨u x - u (x - w), ?_⟩
    rintro z ⟨t, rfl⟩
    exact hslope_lower t.property
  have hp_lower : ∀ w : E, u x - u (x - w) ≤ p w := by
    intro w
    change u x - u (x - w) ≤
      sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
    apply le_csInf (hnonempty w)
    rintro z ⟨t, rfl⟩
    exact hslope_lower t.property
  have hp_le : ∀ (w : E) (t : {t : ℝ // 0 < t}), p w ≤ slope w t := by
    intro w t
    change sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t)) ≤ slope w t
    exact csInf_le (hbdd w) ⟨t, rfl⟩
  have hp_zero : p 0 = 0 := by
    apply le_antisymm
    · simpa [slope] using hp_le 0 ⟨1, by norm_num⟩
    · simpa [slope] using hp_lower 0
  have hslope_scale :
      ∀ {w : E} {c t : ℝ}, 0 < c → 0 < t →
        slope (c • w) t = c * slope w (c * t) := by
    intro w c t hc ht
    change
      (u (x + t • (c • w)) - u x) / t =
        c * ((u (x + (c * t) • w) - u x) / (c * t))
    rw [smul_smul, mul_comm t c]
    have hct : 0 < c * t := mul_pos hc ht
    field_simp [ne_of_gt hc, ne_of_gt ht, ne_of_gt hct]
  have hp_scale :
      ∀ {w : E} {c : ℝ}, 0 < c → p (c • w) = c * p w := by
    intro w c hc
    have h₁ : p (c • w) / c ≤ p w := by
      change p (c • w) / c ≤
        sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
      apply le_csInf (hnonempty w)
      rintro z ⟨t, rfl⟩
      let r : {t : ℝ // 0 < t} := ⟨(t : ℝ) / c, div_pos t.property hc⟩
      have harg : c * ((t : ℝ) / c) = (t : ℝ) := by
        field_simp [ne_of_gt hc]
      calc
        p (c • w) / c ≤ slope (c • w) r / c :=
          div_le_div_of_nonneg_right (hp_le (c • w) r) hc.le
        _ = slope w t := by
          rw [hslope_scale hc r.property, harg]
          apply (div_eq_iff (ne_of_gt hc)).2
          ring
    have h₁' : p (c • w) ≤ c * p w := by
      have h := (div_le_iff₀ hc).1 h₁
      simpa [mul_comm] using h
    have h₂ : c * p w ≤ p (c • w) := by
      change c * p w ≤
        sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope (c • w) t))
      apply le_csInf (hnonempty (c • w))
      rintro z ⟨t, rfl⟩
      let r : {t : ℝ // 0 < t} := ⟨c * (t : ℝ), mul_pos hc t.property⟩
      calc
        c * p w ≤ c * slope w r :=
          mul_le_mul_of_nonneg_left (hp_le w r) hc.le
        _ = slope (c • w) t := by
          rw [hslope_scale hc t.property]
    exact le_antisymm h₁' h₂
  have slope_add :
      ∀ {w₁ w₂ : E} {t : ℝ}, 0 < t →
        slope (w₁ + w₂) t ≤
          slope w₁ (2 * t) + slope w₂ (2 * t) := by
    intro w₁ w₂ t ht
    have heq :
        (1 / 2 : ℝ) • (x + (2 * t) • w₁) +
            (1 / 2 : ℝ) • (x + (2 * t) • w₂) =
          x + t • (w₁ + w₂) := by
      module
    have hc := hconvex (z₁ := x + (2 * t) • w₁) (z₂ := x + (2 * t) • w₂)
      (by simp) (by simp)
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    rw [heq] at hc
    dsimp [slope]
    apply (div_le_iff₀ ht).2
    have hid :
        ((u (x + (2 * t) • w₁) - u x) / (2 * t) +
            (u (x + (2 * t) • w₂) - u x) / (2 * t)) * t =
          (u (x + (2 * t) • w₁) + u (x + (2 * t) • w₂) - 2 * u x) / 2 := by
      field_simp [ne_of_gt ht]
      ring
    rw [hid]
    linarith [hc]
  have hexists :
      ∀ (w : E) {ε : ℝ}, 0 < ε →
        ∃ t : {t : ℝ // 0 < t}, slope w t < p w + ε := by
    intro w ε hε
    by_contra hnot
    have hforall : ∀ t : {t : ℝ // 0 < t}, p w + ε ≤ slope w t := by
      intro t
      exact le_of_not_gt (fun hlt => hnot ⟨t, hlt⟩)
    have hp' : p w + ε ≤ p w := by
      change p w + ε ≤
        sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
      apply le_csInf (hnonempty w)
      rintro z ⟨t, rfl⟩
      exact hforall t
    linarith
  have hp_add : ∀ w₁ w₂ : E, p (w₁ + w₂) ≤ p w₁ + p w₂ := by
    intro w₁ w₂
    by_contra h
    have hlt : p w₁ + p w₂ < p (w₁ + w₂) := lt_of_not_ge h
    let ε : ℝ := (p (w₁ + w₂) - p w₁ - p w₂) / 4
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨t₁, ht₁⟩ := hexists w₁ hε
    obtain ⟨t₂, ht₂⟩ := hexists w₂ hε
    have htmin : 0 < min (t₁ : ℝ) (t₂ : ℝ) :=
      lt_min t₁.property t₂.property
    let t : {t : ℝ // 0 < t} :=
      ⟨min (t₁ : ℝ) t₂ / 2, div_pos htmin (by norm_num)⟩
    have h2t₁ : 2 * (t : ℝ) ≤ (t₁ : ℝ) := by
      dsimp [t]
      linarith [min_le_left (t₁ : ℝ) t₂]
    have h2t₂ : 2 * (t : ℝ) ≤ (t₂ : ℝ) := by
      dsimp [t]
      linarith [min_le_right (t₁ : ℝ) t₂]
    have hpos : 0 < 2 * (t : ℝ) := mul_pos (by norm_num) t.property
    have h₁ := hslope_mono (w := w₁) (a := 2 * (t : ℝ)) (b := t₁)
      hpos h2t₁
    have h₂ := hslope_mono (w := w₂) (a := 2 * (t : ℝ)) (b := t₂)
      hpos h2t₂
    have hsum := slope_add (w₁ := w₁) (w₂ := w₂) t.property
    have hp := hp_le (w₁ + w₂) t
    have hbound :
        p (w₁ + w₂) < p w₁ + p w₂ + 2 * ε := by
      calc
        p (w₁ + w₂) ≤ slope (w₁ + w₂) t := hp
        _ ≤ slope w₁ (2 * (t : ℝ)) + slope w₂ (2 * (t : ℝ)) := hsum
        _ ≤ slope w₁ (t₁ : ℝ) + slope w₂ (t₂ : ℝ) := add_le_add h₁ h₂
        _ < (p w₁ + ε) + (p w₂ + ε) := add_lt_add ht₁ ht₂
        _ = p w₁ + p w₂ + 2 * ε := by ring
    dsimp [ε] at hε hbound ⊢
    linarith
  by_cases hv : v = 0
  · let f : E →ₗ.[ℝ] ℝ := (0 : E →ₗ[ℝ] ℝ).toPMap ⊥
    have hf : ∀ z : f.domain, f z ≤ p z := by
      intro z
      have hz : (z : E) = 0 := by
        have hz' : (z : E) ∈ (⊥ : Submodule ℝ E) := by
          exact z.property
        simpa only [Submodule.mem_bot] using hz'
      have hz'' : z = 0 := Subtype.ext hz
      rw [hz'']
      simp [f, hp_zero]
    obtain ⟨ℓ, hℓf, hℓp⟩ :=
      exists_extension_of_le_sublinear f p
        (fun c hc w => hp_scale (w := w) hc)
        (fun w₁ w₂ => hp_add w₁ w₂) hf
    let L : E →L[ℝ] ℝ :=
      { toLinearMap := ℓ
        cont := LinearMap.continuous_of_finiteDimensional ℓ }
    let g : E := (InnerProductSpace.toDual ℝ E).symm L
    have hpair : ∀ w : E, ⟪g, w⟫ = ℓ w := by
      intro w
      change inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = ℓ w
      calc
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = L w :=
          InnerProductSpace.toDual_symm_apply
        _ = ℓ w := rfl
    refine ⟨g, ?_, ?_⟩
    · intro y
      have hp₁ := hp_le (y - x) ⟨1, by norm_num⟩
      have hq : p (y - x) ≤ u y - u x := by
        have hq' := hp₁
        change p (y - x) ≤
          (u (x + 1 • (y - x)) - u x) / 1 at hq'
        rw [one_smul, div_one] at hq'
        have heq : x + (y - x) = y := by abel
        rw [heq] at hq'
        exact hq'
      have hℓ := hℓp (y - x)
      rw [← hpair] at hℓ
      linarith
    · intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      have hg0 : ⟪g, (0 : E)⟫ = 0 := by
        rw [hpair]
        exact ℓ.map_zero
      simp only [hv, smul_zero, add_zero, sub_self, zero_div, hg0, add_zero]
      linarith
  · let f : E →ₗ.[ℝ] ℝ :=
      LinearPMap.mkSpanSingleton v (p v) hv
    have hf : ∀ z : f.domain, f z ≤ p z := by
      intro z
      have hzdom : (z : E) ∈ ℝ ∙ v := z.property
      rcases Submodule.mem_span_singleton.mp hzdom with ⟨c, hc⟩
      let z₀ : f.domain :=
        ⟨v, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩
      have hz : z = c • z₀ := by
        apply Subtype.ext
        change (z : E) = c • v
        exact hc.symm
      have hf₀ : f z₀ = p v := by
        change (LinearPMap.mkSpanSingleton v (p v) hv) ⟨v, _⟩ = p v
        exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hv (p v)
      rw [hz, f.map_smul, hf₀]
      change c * p v ≤ p (c • v)
      rcases lt_trichotomy c 0 with hcneg | rfl | hcpos
      · have hzero : 0 ≤ p (c • v) + p ((-c) • v) := by
          have h := hp_add (c • v) ((-c) • v)
          have hcv : c • v + (-c) • v = 0 := by module
          rw [hcv, hp_zero] at h
          exact h
        have hpc : p (c • v) = (-c) * p (-v) := by
          have heq : c • v = (-c) • (-v) := by module
          rw [heq, hp_scale (w := -v) (c := -c) (neg_pos.mpr hcneg)]
        have hpneg : p ((-c) • v) = (-c) * p v :=
          hp_scale (w := v) (c := -c) (neg_pos.mpr hcneg)
        rw [hpc, hpneg] at hzero
        calc
          c * p v = -((-c) * p v) := by ring
          _ ≤ (-c) * p (-v) := by linarith
          _ = p (c • v) := hpc.symm
      · simp [hp_zero]
      · rw [hp_scale (w := v) (c := c) hcpos]
    obtain ⟨ℓ, hℓf, hℓp⟩ :=
      exists_extension_of_le_sublinear f p
        (fun c hc w => hp_scale (w := w) hc)
        (fun w₁ w₂ => hp_add w₁ w₂) hf
    let L : E →L[ℝ] ℝ :=
      { toLinearMap := ℓ
        cont := LinearMap.continuous_of_finiteDimensional ℓ }
    let g : E := (InnerProductSpace.toDual ℝ E).symm L
    have hpair : ∀ w : E, ⟪g, w⟫ = ℓ w := by
      intro w
      change inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = ℓ w
      calc
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = L w :=
          InnerProductSpace.toDual_symm_apply
        _ = ℓ w := rfl
    have hℓv : ℓ v = p v := by
      let z₀ : f.domain :=
        ⟨v, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩
      have hf₀ : f z₀ = p v := by
        change (LinearPMap.mkSpanSingleton v (p v) hv) ⟨v, _⟩ = p v
        exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hv (p v)
      change ℓ v = p v
      calc
        ℓ v = ℓ (z₀ : E) := rfl
        _ = f z₀ := hℓf z₀
        _ = p v := hf₀
    refine ⟨g, ?_, ?_⟩
    · intro y
      have hp₁ := hp_le (y - x) ⟨1, by norm_num⟩
      have hq : p (y - x) ≤ u y - u x := by
        have hq' := hp₁
        change p (y - x) ≤
          (u (x + 1 • (y - x)) - u x) / 1 at hq'
        rw [one_smul, div_one] at hq'
        have heq : x + (y - x) = y := by abel
        rw [heq] at hq'
        exact hq'
      have hℓ := hℓp (y - x)
      rw [← hpair] at hℓ
      linarith
    · intro ε hε
      obtain ⟨t, ht⟩ := hexists v hε
      refine ⟨(t : ℝ), t.property, ?_⟩
      have hlt : slope v t < p v + ε := ht
      have heq : p v + ε = ⟪g, v⟫ + ε := by
        rw [← hℓv, hpair]
      dsimp [slope] at hlt
      exact le_of_lt (heq ▸ hlt)

end LT5ASubgradientMaxFormula

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section LT14A0ConvexAeDifferentiable

open MeasureTheory Set

/-! Convex functions on open sets are differentiable almost everywhere (task L-T14a0; proof body GPT, statement by the Letwin sub-controller). -/

/-- **A convex function on an open set is differentiable almost everywhere on it** (Rademacher for
convex functions; weak Letwin route, support for the a.e. injectivity of the subgradient map, N5). -/
theorem ConvexOn.ae_differentiableAt_of_isOpen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ConvexOn ℝ U f) :
    ∀ᵐ x ∂μ, x ∈ U → DifferentiableAt ℝ f x := by
  let I := {x : E // x ∈ U}
  have hball : ∀ x : I, ∃ q : ℝ × NNReal,
      0 < q.1 ∧ LipschitzOnWith q.2 f (Metric.ball (x : E) q.1) ∧
        Metric.ball (x : E) q.1 ⊆ U := by
    intro x
    rcases hf.locallyLipschitzOn hU x.property with ⟨K, t, ht, hK⟩
    have hU_nhds : U ∈ nhds (x : E) := hU.mem_nhds x.property
    have hnhds : nhdsWithin (x : E) U = nhds (x : E) :=
      nhdsWithin_eq_nhds.mpr hU_nhds
    have htx : t ∈ nhds (x : E) := by
      rw [← hnhds]
      exact ht
    rcases Metric.mem_nhds_iff.mp
        (Filter.inter_mem htx (hU.mem_nhds x.property)) with ⟨r, hr, hrt⟩
    exact ⟨(r, K), hr, hK.mono (hrt.trans inter_subset_left),
      hrt.trans inter_subset_right⟩
  let q : I → ℝ × NNReal := fun x => Classical.choose (hball x)
  let B : I → Set E := fun x => Metric.ball (x : E) (q x).1
  have hq : ∀ x : I, 0 < (q x).1 ∧ LipschitzOnWith (q x).2 f (B x) ∧ B x ⊆ U := by
    intro x
    exact Classical.choose_spec (hball x)
  have hAE : ∀ x : I, ∀ᵐ y ∂μ, y ∈ B x → DifferentiableAt ℝ f y := by
    intro x
    filter_upwards [(hq x).2.1.ae_differentiableWithinAt_of_mem] with y hy
    intro hyB
    exact (hy hyB).differentiableAt (Metric.isOpen_ball.mem_nhds hyB)
  obtain ⟨T, hT, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable B (fun x => Metric.isOpen_ball)
  have hTcount : Countable T := hT.to_subtype
  have hBU : (⋃ x, B x) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => (hq x).2.2
    · intro y hy
      let x : I := ⟨y, hy⟩
      exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (hq x).1⟩
  have hAEall : ∀ᵐ y ∂μ, ∀ x : T, y ∈ B (x : I) →
      DifferentiableAt ℝ f y := by
    exact ae_all_iff.2 (fun x => hAE (x : I))
  filter_upwards [hAEall] with y hy
  intro hyU
  have hyT : y ∈ ⋃ x ∈ T, B x := by
    rw [hTU, hBU]
    exact hyU
  rcases mem_iUnion₂.mp hyT with ⟨x, hxT, hyx⟩
  exact hy ⟨x, hxT⟩ hyx

end LT14A0ConvexAeDifferentiable

end FunctionalInequalities.Analysis

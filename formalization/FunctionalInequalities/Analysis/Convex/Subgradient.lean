import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Dual
import FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment

/-!
# Subgradients of convex functions

Pointwise subgradients are written inline, `∀ y, u x + ⟪p, y - x⟫ ≤ u y`. A differentiable convex function on a
finite-dimensional space is `C¹` (`contDiff_one_of_convexOn_of_differentiable`), and the subgradients of a convex
Lipschitz function lie in every closed convex set containing its a.e. gradient
(`subgradient_mem_of_ae_gradient_mem`). A differentiable strictly convex function has an injective gradient
(`injective_gradient_of_strictConvexOn`, every finite dimension). Weak moment-map route to Letwin arXiv:2607.24164v1, Theorem 1.2.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section ConvexC1

/-- **A differentiable convex function on a finite-dimensional space is `C¹`** (weak Letwin
route): convexity makes the derivative map continuous. -/
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

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma gradient_le_increment [CompleteSpace E]
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
gradient** (weak Letwin route: `∂u(x) ⊆ K̄` for the weak moment map, whose gradient lies
a.e. in the target `K`): if `u` is convex and Lipschitz on a finite-dimensional inner product space,
`K` is closed and convex and `∇u(x) ∈ K` for a.e. `x`, then every subgradient `p` of `u` at every
point `x` (`u(x) + ⟪p, y − x⟫ ≤ u(y)` for all `y`) lies in `K`. -/
theorem subgradient_mem_of_ae_gradient_mem [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
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

end InnerProduct

end SubgradientRange

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section LT5ASubgradientMaxFormula

open scoped RealInnerProductSpace

/-! Max formula and existence of subgradients. -/

/-- **Max formula for the one-sided directional derivative of a finite convex function** (weak
Letwin route: "singleton subdifferential ⇒ C¹"): for a convex `u : E → ℝ` on a
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

/-! Convex functions on open sets are differentiable almost everywhere. -/

/-- **A convex function on an open set is differentiable almost everywhere on it** (Rademacher for
convex functions; weak Letwin route, support for the a.e. injectivity of the subgradient map). -/
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

section LT5CUniqueSubgradientDifferentiable

open scoped RealInnerProductSpace

/-! A unique subgradient gives differentiability. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma convex_line_slope_mono [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x v : E) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (u (x + a • v) - u x) / a ≤ (u (x + b • v) - u x) / b := by
  have hline : ConvexOn ℝ Set.univ (fun t : ℝ => u (t • v + x)) := by
    simpa only [Set.preimage_univ, Function.comp_def,
      AffineMap.lineMap_apply_module', add_sub_cancel_left] using
      hconv.comp_affineMap (AffineMap.lineMap x (x + v))
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h :=
    hline.slope_mono (show (0 : ℝ) ∈ Set.univ by simp)
      (show a ∈ Set.univ \ {0} by simp [ne_of_gt ha])
      (show b ∈ Set.univ \ {0} by simp [ne_of_gt hb]) hab
  simpa only [slope_def_field, zero_smul, add_zero, sub_zero, add_comm] using h

section FiniteDimensional

variable [FiniteDimensional ℝ E]

private lemma hasFDerivAt_of_convexOn_of_unique_subgradient {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x g : E)
    (hg : ∀ y, u x + ⟪g, y - x⟫ ≤ u y)
    (huniq : ∀ q, (∀ y, u x + ⟪q, y - x⟫ ≤ u y) → q = g) :
    HasFDerivAt u ((InnerProductSpace.toDual ℝ E) g) x := by
  classical
  have hu : Continuous u :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  let R : E → ℝ := fun h => u (x + h) - u x - ⟪g, h⟫
  have hR_nonneg : ∀ h, 0 ≤ R h := by
    intro h
    have hh := hg (x + h)
    have hh' : u x + ⟪g, h⟫ ≤ u (x + h) := by
      simpa only [add_sub_cancel_left] using hh
    dsimp [R]
    linarith
  have hF_cont (t : ℝ) :
      Continuous (fun v : E =>
        (u (x + t • v) - u x) / t - ⟪g, v⟫) := by
    have harg : Continuous (fun v : E => x + t • v) :=
      continuous_const.add (continuous_const.smul continuous_id)
    have hinner : Continuous (fun v : E => ⟪g, v⟫) :=
      continuous_const.inner continuous_id
    exact (((hu.comp harg).sub continuous_const).div_const t).sub hinner
  have hlittle :
      R =o[nhds 0] fun h : E => h := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    by_cases hS : (Metric.sphere (0 : E) 1).Nonempty
    · let S : Set E := Metric.sphere (0 : E) 1
      have hSc : IsCompact S := by
        exact isCompact_sphere (0 : E) 1
      let I := {v : E // v ∈ S}
      let H : ∀ v : I, ∃ q : E,
          (∀ y, u x + ⟪q, y - x⟫ ≤ u y) ∧
            ∀ ε > 0, ∃ t > 0,
              (u (x + t • (v : E)) - u x) / t ≤ ⟪q, (v : E)⟫ + ε :=
        fun v => exists_subgradient_slope_le_inner_add hconv x (v : E)
      let T : I → ℝ := fun v =>
        Classical.choose ((H v).choose_spec.2 (ε / 2) (by linarith))
      have hT_pos (v : I) : 0 < T v := by
        exact (Classical.choose_spec
          ((H v).choose_spec.2 (ε / 2) (by linarith))).1
      have hT_bound (v : I) :
          (u (x + T v • (v : E)) - u x) / T v -
              ⟪g, v⟫ ≤ ε / 2 := by
        have hqg : (H v).choose = g :=
          huniq _ (H v).choose_spec.1
        have hchosen :=
          Classical.choose_spec ((H v).choose_spec.2 (ε / 2) (by linarith))
        have hchosen' :
            (u (x + T v • (v : E)) - u x) / T v ≤
              ⟪g, v⟫ + ε / 2 := by
          simpa only [T, hqg] using hchosen.2
        linarith
      let U : I → Set E := fun v =>
        {w | (u (x + T v • w) - u x) / T v - ⟪g, w⟫ < ε}
      have hU_open : ∀ v : I, IsOpen (U v) := by
        intro v
        exact isOpen_Iio.preimage (hF_cont (T v))
      have hU_cover : S ⊆ ⋃ v : I, U v := by
        intro v hv
        let w : I := ⟨v, hv⟩
        have hw : (w : E) ∈ U w := by
          change (u (x + T w • (w : E)) - u x) / T w -
              ⟪g, w⟫ < ε
          exact (hT_bound w).trans_lt (by linarith)
        exact Set.mem_iUnion.2 ⟨w, hw⟩
      obtain ⟨K, hK⟩ := hSc.elim_finite_subcover U hU_open hU_cover
      have hK_nonempty : K.Nonempty := by
        obtain ⟨v, hv⟩ := hS
        have hv' := hK hv
        rcases Set.mem_iUnion.mp hv' with ⟨w, hv'⟩
        rcases Set.mem_iUnion.mp hv' with ⟨hwK, _⟩
        exact ⟨w, hwK⟩
      obtain ⟨v₀, hv₀⟩ := hK_nonempty
      let K' : Finset ℝ := K.image T
      have hK'_nonempty : K'.Nonempty := by
        refine ⟨T v₀, ?_⟩
        exact Finset.mem_image.mpr ⟨v₀, hv₀, rfl⟩
      let δ : ℝ := K'.min' hK'_nonempty
      have hδ : 0 < δ := by
        have hδmem : δ ∈ K' := by
          dsimp [δ]
          exact Finset.min'_mem K' hK'_nonempty
        rcases Finset.mem_image.mp hδmem with ⟨v, _, heq⟩
        rw [← heq]
        exact hT_pos v
      have hδ_le (v : I) (hv : v ∈ K) : δ ≤ T v := by
        have hmem : T v ∈ K' := Finset.mem_image.mpr ⟨v, hv, rfl⟩
        change K'.min' hK'_nonempty ≤ T v
        exact Finset.min'_le K' (T v) hmem
      have hsmall :
          ∀ᶠ h : E in nhds 0, ‖h‖ < δ := by
        exact Metric.eventually_nhds_iff.2 ⟨δ, hδ, by
          intro h hh
          simpa [dist_zero_right] using hh⟩
      filter_upwards [hsmall] with h hh
      by_cases hz : h = 0
      · simp [R, hz]
      · let s : ℝ := ‖h‖
        let w : E := s⁻¹ • h
        have hs : 0 < s := by
          exact norm_pos_iff.mpr hz
        have hw : ‖w‖ = 1 := by
          calc
            ‖w‖ = ‖s⁻¹‖ * ‖h‖ := norm_smul _ _
            _ = s⁻¹ * ‖h‖ := by
              rw [Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hs)
        have hwS : w ∈ S := by
          rw [Metric.mem_sphere]
          simpa [dist_zero_right] using hw
        have hwI : ∃ v : I, v ∈ K ∧ (w : E) ∈ U v := by
          have hcover := hK hwS
          rcases Set.mem_iUnion.mp hcover with ⟨v, hcover⟩
          rcases Set.mem_iUnion.mp hcover with ⟨hvK, hwv⟩
          exact ⟨v, hvK, hwv⟩
        obtain ⟨v, hvK, hwv⟩ := hwI
        have hsδ : s < δ := by
          exact hh
        have hst : s ≤ T v := by
          exact hsδ.le.trans (hδ_le v hvK)
        have hmono :
            (u (x + s • w) - u x) / s ≤
              (u (x + T v • w) - u x) / T v := by
          exact convex_line_slope_mono hconv x w hs hst
        have hU := hwv
        change (u (x + T v • w) - u x) / T v -
            ⟪g, w⟫ < ε at hU
        have hmono' :
            u (x + s • w) - u x ≤
              ((u (x + T v • w) - u x) / T v) * s := by
          exact (div_le_iff₀ hs).mp hmono
        have hupper :
            u (x + s • w) - u x - ⟪g, s • w⟫ ≤ ε * s := by
          have hscale : ⟪g, s • w⟫ = s * ⟪g, w⟫ := by
            simp [real_inner_smul_right]
          rw [hscale]
          calc
            u (x + s • w) - u x - s * ⟪g, w⟫ ≤
                ((u (x + T v • w) - u x) / T v) * s -
                  s * ⟪g, w⟫ := by
                    exact sub_le_sub_right hmono' _
            _ = ((u (x + T v • w) - u x) / T v -
                  ⟪g, w⟫) * s := by ring
            _ ≤ ε * s := by
              exact mul_le_mul_of_nonneg_right (by linarith) hs.le
        have heq : s • w = h := by
          dsimp [w, s]
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
        have hnorm : ‖s • w‖ = s := by
          rw [norm_smul, Real.norm_of_nonneg hs.le, hw, mul_one]
        have hupper' :
            R h ≤ ε * ‖h‖ := by
          rw [← heq]
          change u (x + s • w) - u x - ⟪g, s • w⟫ ≤ ε * ‖s • w‖
          rw [hnorm]
          exact hupper
        rw [Real.norm_of_nonneg (hR_nonneg h)]
        exact hupper'
    · have hzero : ∀ v : E, v = 0 := by
        intro v
        by_contra hv
        let w : E := ‖v‖⁻¹ • v
        have hw : ‖w‖ = 1 := by
          calc
            ‖w‖ = ‖‖v‖⁻¹‖ * ‖v‖ := norm_smul _ _
            _ = ‖v‖⁻¹ * ‖v‖ := by
              rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
            _ = 1 := inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hv))
        exact hS ⟨w, by
          rw [Metric.mem_sphere]
          simpa [dist_zero_right] using hw⟩
      exact Filter.Eventually.of_forall (fun h => by
        simp [R, hzero h])
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only [InnerProductSpace.toDual_apply_apply, R] using hlittle

/-- **A convex function with a unique subgradient at every point is differentiable** (weak Letwin
route: "singleton subdifferential ⇒ C¹", differentiability half): on a finite-dimensional
inner product space, if the subgradient inequality `u x + ⟪g, y - x⟫ ≤ u y` (all `y`) is satisfied by
exactly one `g` at every `x`, then `u` is differentiable (with that `g` as gradient; `C¹` then follows
from `contDiff_one_of_convexOn_of_differentiable`). -/
theorem differentiable_of_convexOn_of_unique_subgradient {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hsub : ∀ x, ∃! g : E, ∀ y, u x + ⟪g, y - x⟫ ≤ u y) :
    Differentiable ℝ u := by
  intro x
  obtain ⟨g, hg, huniq⟩ := hsub x
  exact (hasFDerivAt_of_convexOn_of_unique_subgradient hconv x g hg huniq).differentiableAt

end FiniteDimensional

end InnerProduct

end FunctionalInequalities.Analysis

end LT5CUniqueSubgradientDifferentiable

section LT12ASubgradientImageMonotone

open Set
open scoped RealInnerProductSpace
open scoped Topology

/-! Monotonicity of subgradient images (Gutiérrez Lemma 1.4.1). -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma support_of_max
    {u : E → ℝ} {Ω : Set E} (hu : ConvexOn ℝ univ u) (hΩ : IsOpen Ω)
    (x₀ x₁ p : E) (c : ℝ) (hx₁ : x₁ ∈ Ω)
    (hmax :
      IsMaxOn (fun z => c + ⟪p, z - x₀⟫ - u z) (closure Ω) x₁) :
    ∀ y, u x₁ + ⟪p, y - x₁⟫ ≤ u y := by
  let ell : E → ℝ := fun z => c + ⟪p, z - x₀⟫
  let a : ℝ := ell x₁ - u x₁
  let f : E → ℝ := fun z => u z - ell z + a
  have hell :
      ∀ (x y : E) (α β : ℝ), α + β = 1 →
        ell (α • x + β • y) = α • ell x + β • ell y := by
    intro x y α β hab
    dsimp [ell]
    have harg :
        α • x + β • y - x₀ = α • (x - x₀) + β • (y - x₀) := by
      calc
        α • x + β • y - x₀ =
            α • x + β • y - (α + β) • x₀ := by
              rw [hab, one_smul]
        _ = α • (x - x₀) + β • (y - x₀) := by
          rw [add_smul, smul_sub, smul_sub]
          abel
    rw [harg, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    change c + (α * ⟪p, x - x₀⟫ + β * ⟪p, y - x₀⟫) =
      α * (c + ⟪p, x - x₀⟫) + β * (c + ⟪p, y - x₀⟫)
    calc
      c + (α * ⟪p, x - x₀⟫ + β * ⟪p, y - x₀⟫) =
          (α + β) * c +
            (α * ⟪p, x - x₀⟫ + β * ⟪p, y - x₀⟫) := by
              simp [hab]
      _ = α * (c + ⟪p, x - x₀⟫) +
            β * (c + ⟪p, y - x₀⟫) := by ring
  have hfconv : ConvexOn ℝ univ f := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β hα hβ hab
    have h := hu.2 (show x ∈ (univ : Set E) by simp)
      (show y ∈ (univ : Set E) by simp) hα hβ hab
    have h' : u (α • x + β • y) ≤ α * u x + β * u y := by
      simpa only [smul_eq_mul] using h
    calc
      f (α • x + β • y) =
          u (α • x + β • y) - (α * ell x + β * ell y) + a := by
            simp only [f, hell x y α β hab, smul_eq_mul]
      _ ≤ (α * u x + β * u y) - (α * ell x + β * ell y) + a := by
            linarith
      _ = α • f x + β • f y := by
            change
              (α * u x + β * u y) - (α * ell x + β * ell y) + a =
                α * (u x - ell x + a) + β * (u y - ell y + a)
            calc
              (α * u x + β * u y) - (α * ell x + β * ell y) + a =
                  α * (u x - ell x) + β * (u y - ell y) + (α + β) * a := by
                    simp [hab]
                    ring
              _ = α * (u x - ell x + a) + β * (u y - ell y + a) := by
                    ring
  have hnonneg : ∀ z ∈ Ω, 0 ≤ f z := by
    intro z hz
    have hzmax := hmax (subset_closure hz)
    dsimp [f, a, ell] at hzmax ⊢
    linarith
  have hxzero : f x₁ = 0 := by
    dsimp [f, a]
    ring
  intro y
  have hfy : 0 ≤ f y := by
    by_contra hy
    have hy' : f y < 0 := lt_of_not_ge hy
    have hpre :
        (AffineMap.lineMap x₁ y) ⁻¹' Ω ∈ 𝓝 (0 : ℝ) :=
      (AffineMap.lineMap_continuous (p := x₁) (q := y)).continuousAt.preimage_mem_nhds
        (hΩ.mem_nhds (show AffineMap.lineMap x₁ y 0 ∈ Ω by
          rw [AffineMap.lineMap_apply_zero]
          exact hx₁))
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
    let t : ℝ := min (ε / 2) (1 / 2)
    have ht : 0 < t := by
      dsimp [t]
      exact lt_min (by linarith) (by norm_num)
    have htε : t < ε := by
      dsimp [t]
      exact (min_le_left _ _).trans_lt (by linarith)
    have ht1 : t < 1 := by
      dsimp [t]
      exact (min_le_right _ _).trans_lt (by norm_num)
    have htΩ : AffineMap.lineMap x₁ y t ∈ Ω := by
      apply hεsub
      have hdist : dist t 0 < ε := by
        rw [Real.dist_eq]
        simpa [abs_of_pos ht] using htε
      exact hdist
    let z : E := AffineMap.lineMap x₁ y t
    have hzΩ : z ∈ Ω := by
      simpa [z] using htΩ
    have hzseg : z ∈ openSegment ℝ x₁ y := by
      exact lineMap_mem_openSegment ℝ x₁ y ⟨ht, ht1⟩
    have hxz : f x₁ ≤ f z := by
      simpa [hxzero] using hnonneg z hzΩ
    have hzy : f z ≤ f y :=
      hfconv.le_right_of_left_le
        (x := x₁) (y := y) (z := z)
        (show x₁ ∈ (univ : Set E) by simp)
        (show y ∈ (univ : Set E) by simp)
        hzseg hxz
    exact (not_lt_of_ge (hnonneg z hzΩ)) (lt_of_le_of_lt hzy hy')
  have helldiff : ell y - ell x₁ = ⟪p, y - x₁⟫ := by
    dsimp [ell]
    simp only [inner_sub_right]
    ring
  dsimp [f, a] at hfy
  linarith [helldiff]

/-- The **subgradient image** `∂u(S) = {p | ∃ x ∈ S, p is a subgradient of u at x}` (weak Letwin
route, routes/letwin-weak-definitions.md item 2). -/
def subgradientImage {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
    (S : Set E) : Set E :=
  {p | ∃ x ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y}

/-- **Monotonicity of subgradient images under comparison** (Gutiérrez, *The Monge–Ampère
equation*, Lemma 1.4.1; weak Letwin route, comparison principle): if `u ≤ v` on a
bounded open `Ω` and `u = v` on its frontier, then `∂v(Ω) ⊆ ∂u(Ω)`. -/
theorem subgradientImage_subset_of_le
    [FiniteDimensional ℝ E] {u v : E → ℝ} (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hle : ∀ x ∈ Ω, u x ≤ v x)
    (heq : ∀ x ∈ frontier Ω, u x = v x) : subgradientImage v Ω ⊆ subgradientImage u Ω := by
  rintro p ⟨x₀, hx₀, hp⟩
  let w : E → ℝ := fun z => v x₀ + ⟪p, z - x₀⟫ - u z
  have huc : Continuous u := by
    apply continuousOn_univ.mp
    exact hu.continuousOn isOpen_univ
  have hvc : Continuous v := by
    apply continuousOn_univ.mp
    exact hv.continuousOn isOpen_univ
  have hlin : Continuous (fun z : E => ⟪p, z - x₀⟫) := by
    fun_prop
  have hwc : Continuous w := by
    have hwc' : Continuous ((fun _ : E => v x₀) + (fun z : E => ⟪p, z - x₀⟫) - u) :=
      (continuous_const.add hlin).sub huc
    convert hwc' using 1
    ext z
    simp [w]
  have hcompact : IsCompact (closure Ω) := hb.isCompact_closure
  have hnonempty : (closure Ω).Nonempty :=
    ⟨x₀, subset_closure hx₀⟩
  obtain ⟨x₁, hx₁, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty hwc.continuousOn
  by_cases hx₁Ω : x₁ ∈ Ω
  · refine ⟨x₁, hx₁Ω, ?_⟩
    exact support_of_max hu hΩ x₀ x₁ p (v x₀) hx₁Ω (by
      simpa [w] using hmax)
  · have hwx₀ : 0 ≤ w x₀ := by
      simpa [w] using hle x₀ hx₀
    have hax : 0 ≤ w x₁ :=
      hwx₀.trans (hmax (subset_closure hx₀))
    have hfront : x₁ ∈ frontier Ω := by
      rw [← closure_sdiff_interior]
      exact ⟨hx₁, by simpa [hΩ.interior_eq] using hx₁Ω⟩
    have heqx₁ : u x₁ = v x₁ := heq x₁ hfront
    have hupper : w x₁ ≤ 0 := by
      have hp₁ := hp x₁
      rw [← heqx₁] at hp₁
      dsimp [w]
      linarith
    have hax0 : w x₁ = 0 := le_antisymm hupper hax
    have hwx₀zero : w x₀ = 0 := by
      apply le_antisymm
      · simpa [hax0] using hmax (subset_closure hx₀)
      · exact hwx₀
    have hmax₀ : IsMaxOn w (closure Ω) x₀ := by
      intro z hz
      have hzmax := hmax hz
      simpa [hax0, hwx₀zero] using hzmax
    refine ⟨x₀, hx₀, ?_⟩
    exact support_of_max hu hΩ x₀ x₀ p (v x₀) hx₀ (by
      simpa [w] using hmax₀)

end InnerProduct

end FunctionalInequalities.Analysis

end LT12ASubgradientImageMonotone

section LT14ASubgradientAeInjective

open MeasureTheory Set
open scoped RealInnerProductSpace

/-! Almost-everywhere injectivity of the subgradient map. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem legendre_eq_of_subgradient (u : E → ℝ) (x p : E)
    (hsub : ∀ z, u x + ⟪p, z - x⟫ ≤ u z) :
    (⟪x, p⟫ : EReal) - (u x : EReal) =
      legendre (fun z => (u z : EReal)) p := by
  apply le_antisymm
  · change (⟪x, p⟫ : EReal) - (u x : EReal) ≤
      ⨆ z : E, (⟪z, p⟫ : EReal) - (u z : EReal)
    exact le_iSup (fun z : E => (⟪z, p⟫ : EReal) - (u z : EReal)) x
  · change (⨆ z : E, (⟪z, p⟫ : EReal) - (u z : EReal)) ≤
      (⟪x, p⟫ : EReal) - (u x : EReal)
    apply iSup_le
    intro z
    have hz := hsub z
    rw [inner_sub_right] at hz
    rw [← real_inner_comm p z, ← real_inner_comm p x] at hz
    have hz' : ⟪z, p⟫ - u z ≤ ⟪x, p⟫ - u x := by
      linarith
    simpa only [EReal.coe_sub] using
      (EReal.coe_le_coe_iff.mpr hz')

private theorem convex_legendre_finite_domain (φ : E → EReal) (hφ : ProperPotential φ) :
    Convex ℝ {q : E | legendre φ q ≠ ⊤} := by
  intro q₁ hq₁ q₂ hq₂ a b ha hb hab
  have hq₁bot : legendre φ q₁ ≠ ⊥ := legendre_ne_bot φ hφ q₁
  have hq₂bot : legendre φ q₂ ≠ ⊥ := legendre_ne_bot φ hφ q₂
  have hq₁epi :
      (q₁, (legendre φ q₁).toReal) ∈
        {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)} := by
    change legendre φ q₁ ≤ ((legendre φ q₁).toReal : EReal)
    rw [EReal.coe_toReal hq₁ hq₁bot]
  have hq₂epi :
      (q₂, (legendre φ q₂).toReal) ∈
        {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)} := by
    change legendre φ q₂ ≤ ((legendre φ q₂).toReal : EReal)
    rw [EReal.coe_toReal hq₂ hq₂bot]
  have hcomb := (convex_epigraph_legendre φ) hq₁epi hq₂epi ha hb hab
  change legendre φ (a • q₁ + b • q₂) ≤
    ((a * (legendre φ q₁).toReal + b * (legendre φ q₂).toReal : ℝ) : EReal) at hcomb
  intro htop
  rw [htop] at hcomb
  exact (not_le_of_gt (EReal.coe_lt_top _)) hcomb

/-- **Almost every subgradient belongs to a single point** (weak Letwin route, the
Alexandrov identity): for a convex Lipschitz `u` on a finite-dimensional inner product space, the
set of `p` that are subgradients of `u` at two distinct points is Lebesgue-null (such `p` are
non-differentiability points of the conjugate `u*`, or frontier points of its domain). -/
theorem volume_subgradient_two_points_eq_zero [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u) :
    (volume : Measure E) {p : E | ∃ x y : E, x ≠ y ∧ (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧
      (∀ z, u y + ⟪p, z - y⟫ ≤ u z)} = 0 := by
  have _ := hu
  have _ := hconv
  classical
  let φ : E → EReal := fun x => (u x : EReal)
  let Dom : Set E := {q | legendre φ q ≠ ⊤}
  let g : E → ℝ := fun q => (legendre φ q).toReal
  let S : Set E := {p : E | ∃ x y : E, x ≠ y ∧
    (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧
    (∀ z, u y + ⟪p, z - y⟫ ≤ u z)}
  change (volume : Measure E) S = 0
  have hφ : ProperPotential φ := by
    refine ⟨?_, ⟨0, ?_⟩⟩
    · intro x
      exact EReal.coe_ne_bot _
    · exact EReal.coe_ne_top _
  have hDom : Convex ℝ Dom := by
    simpa only [Dom] using convex_legendre_finite_domain φ hφ
  have hconvG : ConvexOn ℝ (interior Dom) g := by
    refine ⟨hDom.interior, ?_⟩
    intro q₁ hq₁ q₂ hq₂ a b ha hb hab
    have hq₁D : q₁ ∈ Dom := interior_subset hq₁
    have hq₂D : q₂ ∈ Dom := interior_subset hq₂
    have hqD : a • q₁ + b • q₂ ∈ Dom :=
      hDom hq₁D hq₂D ha hb hab
    have hq₁bot : legendre φ q₁ ≠ ⊥ := legendre_ne_bot φ hφ q₁
    have hq₂bot : legendre φ q₂ ≠ ⊥ := legendre_ne_bot φ hφ q₂
    have hqbot : legendre φ (a • q₁ + b • q₂) ≠ ⊥ :=
      legendre_ne_bot φ hφ (a • q₁ + b • q₂)
    have hq₁epi :
        (q₁, g q₁) ∈ {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)} := by
      change legendre φ q₁ ≤ ((legendre φ q₁).toReal : EReal)
      rw [EReal.coe_toReal hq₁D hq₁bot]
    have hq₂epi :
        (q₂, g q₂) ∈ {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)} := by
      change legendre φ q₂ ≤ ((legendre φ q₂).toReal : EReal)
      rw [EReal.coe_toReal hq₂D hq₂bot]
    have hE := (convex_epigraph_legendre φ) hq₁epi hq₂epi ha hb hab
    change legendre φ (a • q₁ + b • q₂) ≤
      ((a * g q₁ + b * g q₂ : ℝ) : EReal) at hE
    have hcoe :
        (g (a • q₁ + b • q₂) : EReal) =
          legendre φ (a • q₁ + b • q₂) := by
      dsimp [g]
      exact EReal.coe_toReal hqD hqbot
    have hreal :
        g (a • q₁ + b • q₂) ≤ a * g q₁ + b * g q₂ := by
      apply EReal.coe_le_coe_iff.mp
      rw [hcoe]
      exact hE
    simpa only [smul_eq_mul] using hreal
  have hae :
      ∀ᵐ q : E ∂(volume : Measure E),
        q ∈ interior Dom → DifferentiableAt ℝ g q :=
    FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen
      (volume : Measure E) isOpen_interior hconvG
  let B : Set E := {q | q ∈ interior Dom ∧ ¬ DifferentiableAt ℝ g q}
  have hB : (volume : Measure E) B = 0 := by
    have hnot : ∀ᵐ q : E ∂(volume : Measure E), q ∉ B := by
      filter_upwards [hae] with q hq
      intro hqB
      change q ∈ interior Dom ∧ ¬ DifferentiableAt ℝ g q at hqB
      exact hqB.2 (hq hqB.1)
    have hz := ae_iff.mp hnot
    have hset : {q : E | ¬ q ∉ B} = B := by
      ext q
      simp
    rw [hset] at hz
    exact hz
  have hfrontier : (volume : Measure E) (frontier Dom) = 0 :=
    Convex.addHaar_frontier (volume : Measure E) hDom
  have hsubset : S ⊆ frontier Dom ∪ B := by
    intro p hp
    rcases hp with ⟨x, y, hxy, hx, hy⟩
    have hxEq : (⟪x, p⟫ : EReal) - φ x = legendre φ p := by
      simpa only [φ] using legendre_eq_of_subgradient u x p hx
    have hyEq : (⟪y, p⟫ : EReal) - φ y = legendre φ p := by
      simpa only [φ] using legendre_eq_of_subgradient u y p hy
    have hterm : (⟪x, p⟫ : EReal) - φ x ≠ ⊤ := by
      intro ht
      have ht' : ((⟪x, p⟫ - u x : ℝ) : EReal) = ⊤ := by
        simpa only [φ, EReal.coe_sub] using ht
      exact EReal.coe_ne_top _ ht'
    have hpD : p ∈ Dom := by
      intro htop
      exact hterm (hxEq.trans htop)
    have hpcl : p ∈ closure Dom := subset_closure hpD
    rw [closure_eq_interior_union_frontier] at hpcl
    rcases hpcl with hpI | hpF
    · right
      change p ∈ interior Dom ∧ ¬ DifferentiableAt ℝ g p
      refine ⟨hpI, ?_⟩
      intro hd
      have hd' : DifferentiableAt ℝ
          (fun q => (legendre φ q).toReal) p := by
        simpa only [g] using hd
      have hxg := conjugate_maximizer_eq_gradient φ hφ hpI hd' x hxEq
      have hyg := conjugate_maximizer_eq_gradient φ hφ hpI hd' y hyEq
      exact hxy (hxg.trans hyg.symm)
    · left
      exact hpF
  exact measure_mono_null hsubset (measure_union_null hfrontier hB)

end InnerProduct

end FunctionalInequalities.Analysis

end LT14ASubgradientAeInjective

section LT11BAffineLineSubgradient

open MeasureTheory Set
open scoped RealInnerProductSpace

/-! Subgradients along a segment where the function is affine form a null set (Caffarelli block). -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A function affine along a full line pins every subgradient** (weak Letwin route, Caffarelli's argument): if `u (x₀ + t θ) = u x₀ + t c` for all real `t`, then every subgradient `p` of `u` at
any point satisfies `⟪p, θ⟫ = c`. -/
theorem inner_subgradient_eq_of_affine_on_line {u : E → ℝ} {x₀ θ : E} {c : ℝ}
    (hline : ∀ t : ℝ, u (x₀ + t • θ) = u x₀ + t * c) {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : ⟪p, θ⟫ = c := by
  have hineq (t : ℝ) :
      u x + ⟪p, (x₀ + t • θ) - x⟫ ≤ u x₀ + t * c := by
    calc
      u x + ⟪p, (x₀ + t • θ) - x⟫ ≤ u (x₀ + t • θ) :=
        hp (x₀ + t • θ)
      _ = u x₀ + t * c := hline t
  have hzero : ⟪p, θ⟫ - c = 0 := by
    by_contra hne
    let K : ℝ := u x₀ - u x - ⟪p, x₀ - x⟫
    let t : ℝ := (K + 1) / (⟪p, θ⟫ - c)
    have ht := hineq t
    have harg : (x₀ + t • θ) - x = (x₀ - x) + t • θ := by
      abel
    rw [harg, inner_add_right, inner_smul_right] at ht
    have ht' : t * (⟪p, θ⟫ - c) ≤ K := by
      dsimp [K]
      nlinarith [ht]
    have hprod : t * (⟪p, θ⟫ - c) = K + 1 := by
      dsimp [t]
      exact div_mul_cancel₀ (K + 1) hne
    nlinarith [ht', hprod]
  linarith

/-- The set of subgradients of a function affine along a line in a nonzero direction is
Lebesgue-null (it lies in an affine hyperplane). -/
theorem volume_setOf_subgradient_eq_zero_of_affine_on_line [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {x₀ θ : E} (hθ : θ ≠ 0) {c : ℝ}
    (hline : ∀ t : ℝ, u (x₀ + t • θ) = u x₀ + t * c) :
    (volume : Measure E) {p | ∃ x, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} = 0 := by
  let L : E →ₗ[ℝ] ℝ :=
    { toFun := fun p => ⟪p, θ⟫
      map_add' := by
        intro p q
        exact inner_add_left p q θ
      map_smul' := by
        intro a p
        change ⟪a • p, θ⟫ = a * ⟪p, θ⟫
        exact real_inner_smul_left p θ a }
  let p₀ : E := (c / ⟪θ, θ⟫) • θ
  have hθθ : ⟪θ, θ⟫ ≠ 0 := (inner_self_ne_zero).2 hθ
  have hp₀ : L p₀ = c := by
    dsimp [L, p₀]
    rw [real_inner_smul_left]
    exact div_mul_cancel₀ c hθθ
  let H : AffineSubspace ℝ E := AffineSubspace.mk' p₀ L.ker
  have hq : p₀ + θ ∉ H := by
    intro hmem
    change p₀ + θ ∈ AffineSubspace.mk' p₀ L.ker at hmem
    have hv : (p₀ + θ) -ᵥ p₀ ∈ L.ker :=
      (AffineSubspace.mem_mk').mp hmem
    have hz : L ((p₀ + θ) -ᵥ p₀) = 0 :=
      (LinearMap.mem_ker).mp hv
    have hz' : ⟪θ, θ⟫ = 0 := by
      simpa [L] using hz
    exact hθθ hz'
  have hHtop : H ≠ (⊤ : AffineSubspace ℝ E) := by
    intro htop
    apply hq
    rw [htop]
    exact AffineSubspace.mem_top ℝ E (p₀ + θ)
  apply measure_mono_null ?_ (Measure.addHaar_affineSubspace volume H hHtop)
  intro p hp
  rcases hp with ⟨x, hx⟩
  have hpc : ⟪p, θ⟫ = c :=
    inner_subgradient_eq_of_affine_on_line hline hx
  have hpL : L p = c := by
    simpa [L] using hpc
  change p ∈ AffineSubspace.mk' p₀ L.ker
  apply (AffineSubspace.mem_mk').2
  apply (LinearMap.mem_ker).2
  change L (p - p₀) = 0
  calc
    L (p - p₀) = L p - L p₀ := L.map_sub p p₀
    _ = c - c := by rw [hpL, hp₀]
    _ = 0 := sub_self c

end InnerProduct

end FunctionalInequalities.Analysis

end LT11BAffineLineSubgradient

section LT5DUniqueSubgradientC1

open scoped RealInnerProductSpace

/-! Unique subgradients everywhere give a `C¹` function. -/

namespace FunctionalInequalities.Analysis

/-- **Singleton subdifferential ⇒ `C¹`** (weak Letwin route): a
convex function on a finite-dimensional inner product space with exactly one subgradient at every
point is continuously differentiable. -/
theorem contDiff_one_of_convexOn_of_unique_subgradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hsub : ∀ x, ∃! g : E, ∀ y, u x + ⟪g, y - x⟫ ≤ u y) :
    ContDiff ℝ 1 u := by
  exact contDiff_one_of_convexOn_of_differentiable hconv
    (differentiable_of_convexOn_of_unique_subgradient hconv hsub)

end FunctionalInequalities.Analysis

end LT5DUniqueSubgradientC1

section LT12D5SubgradientExpansionTaylor

open Set Filter
open scoped RealInnerProductSpace Topology

/-! A first-order expansion of the subgradient gives a second-order Taylor expansion of the function. -/

namespace FunctionalInequalities.Analysis

private lemma riemann_sum_affine (N : ℕ) (hN : (N : ℝ) ≠ 0)
    (a b c s : ℝ) :
    (∑ k ∈ Finset.range N,
      (1 / (N : ℝ)) * (a + ((k : ℝ) + s) / N * b + c)) =
      a + (1 / 2 + (s - 1 / 2) / (N : ℝ)) * b + c := by
  have hs : ∀ (n : ℕ) (u v : ℝ),
      (∑ k ∈ Finset.range n, (u + (k : ℝ) * v)) =
        (n : ℝ) * u + ((n : ℝ) * ((n : ℝ) - 1) / 2) * v := by
    intro n u v
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have he :
      (fun k : ℕ => (1 / (N : ℝ)) * (a + ((k : ℝ) + s) / N * b + c)) =
      (fun k : ℕ =>
        (a + s / (N : ℝ) * b + c) / (N : ℝ) +
          (k : ℝ) * (b / (N : ℝ) ^ 2)) := by
    funext k
    ring
  rw [he, hs]
  field_simp [hN]
  ring

private lemma riemann_sum_sandwich (F s : ℕ → ℝ) (N : ℕ)
    (a b c : ℝ) (hN : 0 < (N : ℝ))
    (hstep : ∀ k < N,
      (1 / (N : ℝ)) * s k ≤ F (k + 1) - F k ∧
        F (k + 1) - F k ≤ (1 / (N : ℝ)) * s (k + 1))
    (hs : ∀ k ≤ N, |s k - a - (k : ℝ) / N * b| ≤ c) :
    (∑ k ∈ Finset.range N,
      (1 / (N : ℝ)) * (a + ((k : ℝ) + 0) / N * b + (-c))) ≤ F N - F 0 ∧
    F N - F 0 ≤ ∑ k ∈ Finset.range N,
      (1 / (N : ℝ)) * (a + ((k : ℝ) + 1) / N * b + c) := by
  rw [← Finset.sum_range_sub F N]
  constructor
  · apply Finset.sum_le_sum
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have hb := (abs_le.mp (hs k (Nat.le_of_lt hkN))).1
    have hm := mul_le_mul_of_nonneg_left
      (show a + ((k : ℝ) + 0) / N * b + (-c) ≤ s k by
        simp only [add_zero]
        linarith)
      (le_of_lt (one_div_pos.mpr hN))
    exact hm.trans (hstep k hkN).1
  · apply Finset.sum_le_sum
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have hb := (abs_le.mp (hs (k + 1) hkN)).2
    have hb' : s (k + 1) ≤ a + ((k : ℝ) + 1) / N * b + c := by
      push_cast at hb
      linarith
    exact (hstep k hkN).2.trans
      (mul_le_mul_of_nonneg_left hb' (le_of_lt (one_div_pos.mpr hN)))

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma inner_slope_error
    (p q h : E) (B : E →L[ℝ] E) (t e : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (he : 0 ≤ e)
    (hex : ‖q - p - B (t • h)‖ ≤ e * ‖t • h‖) :
    |⟪q, h⟫ - ⟪p, h⟫ - t * ⟪B h, h⟫| ≤ e * ‖h‖ ^ 2 := by
  have hn : ‖t • h‖ ≤ ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    nlinarith [norm_nonneg h]
  have hb := (abs_real_inner_le_norm (q - p - B (t • h)) h).trans
    (mul_le_mul_of_nonneg_right
      (hex.trans (mul_le_mul_of_nonneg_left hn he)) (norm_nonneg h))
  rw [inner_sub_left, inner_sub_left, map_smul, real_inner_smul_left] at hb
  simpa only [pow_two, mul_assoc] using hb

set_option maxHeartbeats 800000 in
/-- **First-order expansion of the subdifferential gives a second-order Taylor expansion** (weak Letwin
route, Alexandrov's theorem): if every subgradient `q` of the convex `f` at points `y` near `x`
satisfies `‖q − p − B (y − x)‖ ≤ ε ‖y − x‖`, then
`|f y − f x − ⟪p, y − x⟫ − ½ ⟪B (y − x), y − x⟫| ≤ ε' ‖y − x‖²` near `x`. -/
theorem eventually_abs_sub_quadratic_le_of_subgradient_expansion [FiniteDimensional ℝ E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) {x p : E} {B : E →L[ℝ] E}
    (hexp : ∀ ε > 0, ∀ᶠ y in 𝓝 x, ∀ q : E, (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
      ‖q - p - B (y - x)‖ ≤ ε * ‖y - x‖) :
    ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
  classical
  intro ε hε
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨r, hr, hex⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hexp (ε / 2) hε₂)
  obtain ⟨N, hlarge⟩ := exists_nat_gt (‖B‖ / ε + 1)
  have hN : 0 < (N : ℝ) := by
    have : 0 ≤ ‖B‖ / ε := div_nonneg (norm_nonneg B) (le_of_lt hε)
    linarith
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hN
  have hmesh : (1 / (2 * (N : ℝ))) * ‖B‖ ≤ ε / 2 := by
    have hb : ‖B‖ < (N : ℝ) * ε :=
      (div_lt_iff₀ hε).mp (by linarith : ‖B‖ / ε < (N : ℝ))
    have hd : ‖B‖ / (2 * (N : ℝ)) ≤ ε / 2 :=
      (div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ))).2 (by nlinarith)
    convert hd using 1
    ring
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨r, hr, ?_⟩
  intro y hy
  let h : E := y - x
  let z : ℕ → E := fun k => x + ((k : ℝ) / N) • h
  have hh : ‖h‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have ht0 (k : ℕ) : 0 ≤ (k : ℝ) / N :=
    div_nonneg (Nat.cast_nonneg k) (le_of_lt hN)
  have ht1 (k : ℕ) (hk : k ≤ N) : (k : ℝ) / N ≤ 1 :=
    (div_le_one hN).2 (by exact_mod_cast hk)
  have hzsub (k : ℕ) : z k - x = ((k : ℝ) / N) • h := by
    dsimp only [z]
    exact add_sub_cancel_left x _
  have hzball (k : ℕ) (hk : k ≤ N) : z k ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm, hzsub k]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ht0 k)]
    have hle : (k : ℝ) / N * ‖h‖ ≤ ‖h‖ := by
      nlinarith [ht1 k hk, norm_nonneg h]
    exact hle.trans_lt hh
  have hz0 : z 0 = x := by simp [z]
  have hzN : z N = y := by simp [z, h, hN0]
  have hzstep (k : ℕ) : z (k + 1) - z k = (1 / (N : ℝ)) • h := by
    dsimp only [z]
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    push_cast
    ring
  let q : ℕ → E := fun k =>
    Classical.choose (exists_subgradient_slope_le_inner_add hconv (z k) h)
  have hq (k : ℕ) : ∀ w, f (z k) + ⟪q k, w - z k⟫ ≤ f w :=
    (Classical.choose_spec
      (exists_subgradient_slope_le_inner_add hconv (z k) h)).1
  have hslope (k : ℕ) (hk : k ≤ N) :
      |⟪q k, h⟫ - ⟪p, h⟫ - (k : ℝ) / N * ⟪B h, h⟫| ≤
        (ε / 2) * ‖h‖ ^ 2 := by
    have he := hex (z k) (hzball k hk) (q k) (hq k)
    rw [hzsub k] at he
    exact inner_slope_error p (q k) h B ((k : ℝ) / N) (ε / 2)
      (ht0 k) (ht1 k hk) (le_of_lt hε₂) he
  have hstep (k : ℕ) (_hk : k < N) :
      (1 / (N : ℝ)) * ⟪q k, h⟫ ≤ f (z (k + 1)) - f (z k) ∧
      f (z (k + 1)) - f (z k) ≤ (1 / (N : ℝ)) * ⟪q (k + 1), h⟫ := by
    have hl := hq k (z (k + 1))
    rw [hzstep k, real_inner_smul_right] at hl
    have hu := hq (k + 1) (z k)
    rw [← neg_sub (z (k + 1)) (z k), hzstep k,
      inner_neg_right, real_inner_smul_right] at hu
    constructor <;> linarith
  obtain ⟨hl, hu⟩ := riemann_sum_sandwich
    (fun k => f (z k)) (fun k => ⟪q k, h⟫) N
    ⟪p, h⟫ ⟪B h, h⟫ ((ε / 2) * ‖h‖ ^ 2) hN hstep hslope
  rw [riemann_sum_affine N hN0] at hl hu
  have hc0 :
      (1 / 2 : ℝ) + (0 - 1 / 2) / (N : ℝ) =
        1 / 2 - 1 / (2 * (N : ℝ)) := by ring
  have hc1 :
      (1 / 2 : ℝ) + (1 - 1 / 2) / (N : ℝ) =
        1 / 2 + 1 / (2 * (N : ℝ)) := by ring
  rw [hc0, hzN, hz0] at hl
  rw [hc1, hzN, hz0] at hu
  have hB : |⟪B h, h⟫| ≤ ‖B‖ * ‖h‖ ^ 2 := by
    calc
      |⟪B h, h⟫| ≤ ‖B h‖ * ‖h‖ := abs_real_inner_le_norm (B h) h
      _ ≤ (‖B‖ * ‖h‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm h) (norm_nonneg h)
      _ = ‖B‖ * ‖h‖ ^ 2 := by ring
  have hd0 : 0 ≤ 1 / (2 * (N : ℝ)) := by positivity
  have hdisc :
      (1 / (2 * (N : ℝ))) * ⟪B h, h⟫ ≤ (ε / 2) * ‖h‖ ^ 2 := by
    calc
      (1 / (2 * (N : ℝ))) * ⟪B h, h⟫ ≤
          (1 / (2 * (N : ℝ))) * |⟪B h, h⟫| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hd0
      _ ≤ (1 / (2 * (N : ℝ))) * (‖B‖ * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hB hd0
      _ = ((1 / (2 * (N : ℝ))) * ‖B‖) * ‖h‖ ^ 2 := by ring
      _ ≤ (ε / 2) * ‖h‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmesh (sq_nonneg ‖h‖)
  change |f y - f x - ⟪p, h⟫ - (1 / 2) * ⟪B h, h⟫| ≤ ε * ‖h‖ ^ 2
  apply abs_le.mpr
  constructor <;> nlinarith only [hl, hu, hdisc]

end InnerProduct

end FunctionalInequalities.Analysis

end LT12D5SubgradientExpansionTaylor

section StrictConvexGradient

open Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- A differentiable strictly convex function has an injective gradient. This is
an elementary prerequisite for the moment-map inverse in Letwin Lemma 2.2. -/
theorem injective_gradient_of_strictConvexOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} (hu : Differentiable ℝ u) (hstrict : StrictConvexOn ℝ univ u) :
    Function.Injective (gradient u) := by
  intro x y hxy
  by_contra hne
  let l : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hinj : Function.Injective l := AffineMap.lineMap_injective ℝ hne
  have hc : StrictConvexOn ℝ univ (u ∘ l) := by
    refine ⟨convex_univ, ?_⟩
    intro r _ s _ hrs a b ha hb hab
    change u (l (a • r + b • s)) < a • u (l r) + b • u (l s)
    rw [Convex.combo_affine_apply hab]
    exact hstrict.2 (mem_univ _) (mem_univ _) (fun he => hrs (hinj he)) ha hb hab
  have hlineConv : StrictConvexOn ℝ univ (fun t : ℝ => u (x + t • (y - x))) := by
    simpa only [Function.comp_def, l, AffineMap.lineMap_apply_module', add_comm] using hc
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => u (x + s • (y - x)))
      (fderiv ℝ u (x + t • (y - x)) (y - x)) t := by
    have hp : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact (hu (x + t • (y - x))).hasFDerivAt.comp_hasDerivAt t hp
  have hfd : fderiv ℝ u x = fderiv ℝ u y := by
    simpa only [toDual_gradient] using
      congrArg (InnerProductSpace.toDual ℝ E) hxy
  have hlt :=
    (hlineConv.lt_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one (hline 0)).trans
      (hlineConv.slope_lt_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one (hline 1))
  have hlt' : fderiv ℝ u x (y - x) < fderiv ℝ u y (y - x) := by
    simpa only [zero_smul, one_smul, add_zero, add_sub_cancel] using hlt
  rw [hfd] at hlt'
  exact (lt_irrefl _) hlt'

end FunctionalInequalities.Analysis

end StrictConvexGradient

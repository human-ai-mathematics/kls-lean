import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Rademacher
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

module

public import FunctionalInequalities.Analysis.Graph.Implicit
public import FunctionalInequalities.Analysis.Divergence
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The divergence formula on a smooth subgraph

General geometric analysis, independent of the KLS objects: the local Gauss–Green identity for the
region below the graph of a `C¹` function.  Every statement here is proved and uses only the
standard axioms; the module contains no hole.

## Setting

`H` and `V` are finite-dimensional real inner-product spaces with an orthogonal splitting
`IsGraphSplitting ι e` (`Analysis/Graph/Implicit.lean`), so that `V = ι H ⊕ ℝ e`.  For a `C¹`
height function `g : H → ℝ`, a base point `x₀ : V` and the graph parametrization
`Ψ y = x₀ + ι y + g y • e` (`graphChartMap`), the subgraph is

  `S = {x | graphHeight e x₀ x < g (graphCoord ι x₀ x)}`,

the part of `V` strictly below the graph.  The main result
`integral_divergence_subgraph` is, for every compactly supported `C¹` vector field `F`,

  `∫_S div F = ∫_H ⟪F (Ψ y), ι (-∇g y) + e⟫ dy`.

The right-hand side is the **unnormalized** normal flux: the outward unit normal along the graph
is `(ι (-∇g y) + e)/√(1 + ‖∇g y‖²)` and the graph Jacobian is exactly `√(1 + ‖∇g y‖²)`, so the two
cancel and no Jacobian factor survives.  Neither `S` nor its boundary is assumed bounded, `g` is
not assumed Lipschitz or of bounded gradient, and `H` may be zero-dimensional, in which case the
statement is the fundamental theorem of calculus on a half line.

## Route

1. **Measure splitting.**  `splitIsometry` identifies `WithLp 2 (H × ℝ)` with `V`, so
   `splitHomeomorph` is measure preserving (`measurePreserving_splitHomeomorph`).  The shear
   `(y, s) ↦ (y, s + g y)` preserves the product measure by Fubini and translation invariance on
   each fibre (`measurePreserving_shearEquiv`), so the graph chart
   `Ξ (y, s) = x₀ + ι y + (s + g y) • e` is a measure-preserving homeomorphism carrying
   `{s < 0}` onto `S` (`measurePreserving_graphChartHomeomorph`).
2. **Splitting of the divergence.**  `divergence_eq_tangentDiv_add` writes `div F x` as the
   tangential trace `tangentDiv ι (DF x) = tr_H (P ∘ DF x ∘ ι)` plus the normal derivative
   `⟪e, DF x e⟫`; the tangential half uses `LinearMap.trace_comp_comm'`, the normal half the
   rank-one trace identity of `Analysis/Divergence.lean`.  No basis is chosen.
3. **Pointwise identity in the sheared coordinates.**  In the chart `Ξ` the integrand splits as
   the divergence of the tangential slice field `z ↦ P (F (Ξ (z, s)))` plus the `s`-derivative of
   `σ ↦ ⟪e - ι ∇g y, F (Ξ (y, σ))⟫`.  The `∇g` terms produced by the chain rule in the two halves
   cancel exactly; this is where the `-∇g` of the flux comes from.
4. **The two integrals.**  The tangential half integrates to zero on every slice by
   `integral_divergence_eq_zero`; the normal half integrates along each fibre to the value at
   `s = 0` by the fundamental theorem of calculus on `(-∞, 0]`.

`integral_divergence_eq_zero` — the divergence of a compactly supported `C¹` field on `H`
integrates to zero — is proved here by induction on `Module.finrank ℝ H`, splitting off one
direction at a time with `Analysis.isGraphSplitting_orthogonal` and using the same Fubini and
fundamental-theorem-of-calculus steps.  Mathlib's divergence theorem covers boxes in
`Fin (n+1) → ℝ` only.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

universe u v

/-! ### The splitting homeomorphism and its measure invariance -/

section Split

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The linear isometry equivalence `WithLp 2 (H × ℝ) ≃ₗᵢ[ℝ] V` attached to a splitting. -/
def splitIsometry (ι : H →ₗᵢ[ℝ] V) {e : V} (hsp : IsGraphSplitting ι e) :
    WithLp 2 (H × ℝ) ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofSurjective
    { toFun := fun p => ι (WithLp.ofLp p).1 + (WithLp.ofLp p).2 • e
      map_add' := by intro p q; simp [add_smul]; abel
      map_smul' := by intro c p; simp [smul_smul, smul_add]
      norm_map' := by
        intro p
        show ‖ι (WithLp.ofLp p).1 + (WithLp.ofLp p).2 • e‖ = ‖p‖
        have h1 : ‖ι (WithLp.ofLp p).1 + (WithLp.ofLp p).2 • e‖ ^ 2
            = ‖(WithLp.ofLp p).1‖ ^ 2 + ((WithLp.ofLp p).2) ^ 2 := hsp.norm_add_smul_sq _ _
        have h2 : ‖p‖ ^ 2 = ‖(WithLp.ofLp p).1‖ ^ 2 + ‖(WithLp.ofLp p).2‖ ^ 2 :=
          WithLp.prod_norm_sq_eq_of_L2 p
        have h3 : ‖(WithLp.ofLp p).2‖ ^ 2 = ((WithLp.ofLp p).2) ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
        nlinarith [norm_nonneg (ι (WithLp.ofLp p).1 + (WithLp.ofLp p).2 • e), norm_nonneg p] }
    (by
      intro x
      exact ⟨WithLp.toLp 2 (graphProj ι x, (⟪e, x⟫ : ℝ)), hsp.eq_ι_add_smul x⟩)

theorem splitIsometry_apply (ι : H →ₗᵢ[ℝ] V) {e : V} (hsp : IsGraphSplitting ι e)
    (p : WithLp 2 (H × ℝ)) :
    splitIsometry ι hsp p = ι (WithLp.ofLp p).1 + (WithLp.ofLp p).2 • e := rfl

variable {ι : H →ₗᵢ[ℝ] V} {e : V}

/-- The splitting chart `(y, t) ↦ x₀ + ι y + t • e` as a homeomorphism of `H × ℝ` onto `V`; its
inverse is the pair of the tangential coordinate and the normal height. -/
def splitHomeomorph (hsp : IsGraphSplitting ι e) (x₀ : V) : (H × ℝ) ≃ₜ V where
  toFun p := x₀ + ι p.1 + p.2 • e
  invFun x := (graphCoord ι x₀ x, graphHeight e x₀ x)
  left_inv := by
    rintro ⟨y, t⟩
    have h1 : x₀ + ι y + t • e - x₀ = ι y + t • e := by abel
    have h2 : graphCoord ι x₀ (x₀ + ι y + t • e) = y := by
      rw [graphCoord, h1, hsp.proj_add_smul]
    have h3 : graphHeight e x₀ (x₀ + ι y + t • e) = t := by
      rw [graphHeight, h1, hsp.inner_add_smul]
    simp only [h2, h3]
  right_inv := fun x => (eq_graphChartMap_coord hsp x₀ x).symm
  continuous_toFun := by
    refine (continuous_const.add (ι.continuous.comp continuous_fst)).add ?_
    exact continuous_snd.smul continuous_const
  continuous_invFun := by
    have h1 : Continuous fun x : V => graphCoord ι x₀ x :=
      (graphProj ι).continuous.comp (continuous_id.sub continuous_const)
    have h2 : Continuous fun x : V => graphHeight e x₀ x :=
      (innerSL ℝ e).continuous.comp (continuous_id.sub continuous_const)
    exact h1.prodMk h2

@[simp] theorem splitHomeomorph_apply (hsp : IsGraphSplitting ι e) (x₀ : V) (p : H × ℝ) :
    splitHomeomorph hsp x₀ p = x₀ + ι p.1 + p.2 • e := rfl

/-- The shear `(y, s) ↦ (y, s + g y)` of `H × ℝ`, a homeomorphism for continuous `g`. -/
def shearEquiv {g : H → ℝ} (hg : Continuous g) : (H × ℝ) ≃ₜ (H × ℝ) where
  toFun p := (p.1, p.2 + g p.1)
  invFun p := (p.1, p.2 - g p.1)
  left_inv := by rintro ⟨y, s⟩; simp
  right_inv := by rintro ⟨y, t⟩; simp
  continuous_toFun :=
    continuous_fst.prodMk (continuous_snd.add (hg.comp continuous_fst))
  continuous_invFun :=
    continuous_fst.prodMk (continuous_snd.sub (hg.comp continuous_fst))

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
@[simp] theorem shearEquiv_apply {g : H → ℝ} (hg : Continuous g) (p : H × ℝ) :
    shearEquiv hg p = (p.1, p.2 + g p.1) := rfl

/-- The graph chart `(y, s) ↦ x₀ + ι y + (s + g y) • e`: the splitting chart sheared by the graph
of `g`.  It is a homeomorphism of `H × ℝ` onto `V` carrying the open half space `{s < 0}` onto the
open region strictly below the graph of `g`. -/
def graphChartHomeomorph (hsp : IsGraphSplitting ι e) (x₀ : V) {g : H → ℝ} (hg : Continuous g) :
    (H × ℝ) ≃ₜ V :=
  (shearEquiv hg).trans (splitHomeomorph hsp x₀)

@[simp] theorem graphChartHomeomorph_apply (hsp : IsGraphSplitting ι e) (x₀ : V) {g : H → ℝ}
    (hg : Continuous g) (p : H × ℝ) :
    graphChartHomeomorph hsp x₀ hg p = x₀ + ι p.1 + (p.2 + g p.1) • e := rfl

theorem graphCoord_graphChartHomeomorph (hsp : IsGraphSplitting ι e) (x₀ : V) {g : H → ℝ}
    (hg : Continuous g) (p : H × ℝ) :
    graphCoord ι x₀ (graphChartHomeomorph hsp x₀ hg p) = p.1 := by
  have h1 : x₀ + ι p.1 + (p.2 + g p.1) • e - x₀ = ι p.1 + (p.2 + g p.1) • e := by abel
  rw [graphChartHomeomorph_apply, graphCoord, h1, hsp.proj_add_smul]

theorem graphHeight_graphChartHomeomorph (hsp : IsGraphSplitting ι e) (x₀ : V) {g : H → ℝ}
    (hg : Continuous g) (p : H × ℝ) :
    graphHeight e x₀ (graphChartHomeomorph hsp x₀ hg p) = p.2 + g p.1 := by
  have h1 : x₀ + ι p.1 + (p.2 + g p.1) • e - x₀ = ι p.1 + (p.2 + g p.1) • e := by abel
  rw [graphChartHomeomorph_apply, graphHeight, h1, hsp.inner_add_smul]

/-- At height zero the graph chart is the graph parametrization. -/
theorem graphChartHomeomorph_zero (hsp : IsGraphSplitting ι e) (x₀ : V) {g : H → ℝ}
    (hg : Continuous g) (y : H) :
    graphChartHomeomorph hsp x₀ hg (y, 0) = graphChartMap ι e x₀ g y := by
  rw [graphChartHomeomorph_apply, graphChartMap_apply, zero_add]

variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]

/-- The plain splitting chart preserves Lebesgue measure: it is a translate of a linear isometry
from the `L²` product `WithLp 2 (H × ℝ)`. -/
theorem measurePreserving_splitHomeomorph (hsp : IsGraphSplitting ι e) (x₀ : V) :
    MeasurePreserving (splitHomeomorph hsp x₀)
      (volume : Measure (H × ℝ)) (volume : Measure V) := by
  have h1 : MeasurePreserving (WithLp.toLp 2 : H × ℝ → WithLp 2 (H × ℝ))
      (volume : Measure (H × ℝ)) (volume : Measure (WithLp 2 (H × ℝ))) :=
    WithLp.volume_preserving_toLp H ℝ
  have h2 : MeasurePreserving (splitIsometry ι hsp)
      (volume : Measure (WithLp 2 (H × ℝ))) (volume : Measure V) :=
    (splitIsometry ι hsp).measurePreserving
  have h3 := (measurePreserving_add_left (volume : Measure V) x₀).comp (h2.comp h1)
  have heq : (fun x => x₀ + x) ∘ ⇑(splitIsometry ι hsp) ∘ (WithLp.toLp 2 : H × ℝ → _)
      = ⇑(splitHomeomorph hsp x₀) := by
    funext p
    simp [Function.comp_def, splitIsometry_apply, add_assoc]
  rwa [heq] at h3

/-- The shear `(y, s) ↦ (y, s + g y)` preserves the product measure of `H × ℝ`: Fubini reduces it
to translation invariance of Lebesgue measure on each fibre.  No boundedness or regularity of `g`
beyond measurability is used. -/
theorem measurePreserving_shearEquiv {g : H → ℝ} (hg : Continuous g) :
    MeasurePreserving (shearEquiv hg)
      (volume : Measure (H × ℝ)) (volume : Measure (H × ℝ)) := by
  have hmeas : Measurable (shearEquiv hg) :=
    measurable_fst.prodMk (measurable_snd.add (hg.measurable.comp measurable_fst))
  refine ⟨hmeas, ?_⟩
  refine Measure.ext fun E hE => ?_
  rw [Measure.map_apply hmeas hE, Measure.volume_eq_prod,
    Measure.prod_apply (hmeas hE), Measure.prod_apply hE]
  refine lintegral_congr fun y => ?_
  have hset : (Prod.mk y ⁻¹' (⇑(shearEquiv hg) ⁻¹' E))
      = (fun s : ℝ => s + g y) ⁻¹' (Prod.mk y ⁻¹' E) := rfl
  rw [hset]
  exact measure_preimage_add_right _ _ _

/-- The graph chart preserves Lebesgue measure: the shear has unit Jacobian and the splitting
chart is an isometry. -/
theorem measurePreserving_graphChartHomeomorph (hsp : IsGraphSplitting ι e) (x₀ : V)
    {g : H → ℝ} (hg : Continuous g) :
    MeasurePreserving (graphChartHomeomorph hsp x₀ hg)
      (volume : Measure (H × ℝ)) (volume : Measure V) :=
  (measurePreserving_splitHomeomorph hsp x₀).comp (measurePreserving_shearEquiv hg)

/-- Change of variables along the graph chart, for an arbitrary integrand. -/
theorem integral_comp_graphChartHomeomorph (hsp : IsGraphSplitting ι e) (x₀ : V) {g : H → ℝ}
    (hg : Continuous g) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : V → E) :
    ∫ p : H × ℝ, f (graphChartHomeomorph hsp x₀ hg p) ∂(volume : Measure (H × ℝ))
      = ∫ x, f x ∂(volume : Measure V) :=
  (measurePreserving_graphChartHomeomorph hsp x₀ hg).integral_comp
    (graphChartHomeomorph hsp x₀ hg).measurableEmbedding f

end Split

/-! ### Compact support along an affine chart -/

section Support

variable {V : Type v} [NormedAddCommGroup V]

/-- If the parameter norm is controlled by the norm of its image, a compactly supported function
stays compactly supported after composition. -/
theorem hasCompactSupport_comp_of_norm_le {α : Type*} [Zero α] [TopologicalSpace α]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {f : V → α} (hf : HasCompactSupport f) {γ : W → V} (C : ℝ)
    (hle : ∀ w, ‖w‖ ≤ C + ‖γ w‖) : HasCompactSupport (fun w => f (γ w)) := by
  obtain ⟨M, hM⟩ := (hf.isCompact.isBounded).subset_closedBall (0 : V)
  have hsub : Function.support (fun w => f (γ w)) ⊆ Metric.closedBall (0 : W) (C + M) := by
    intro w hw
    have hγw : γ w ∈ tsupport f := subset_tsupport _ hw
    have h1 : ‖γ w‖ ≤ M := by
      have := hM hγw
      simpa [Metric.mem_closedBall] using this
    have := hle w
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : W) (C + M)) isClosed_closure ?_
  exact closure_minimal hsub Metric.isClosed_closedBall

end Support

/-! ### The tangential trace -/

section Trace

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The tangential trace of a continuous linear map `H →L[ℝ] V`: the trace over `H` of the
tangential part of the map. -/
def graphTrace (ι : H →ₗᵢ[ℝ] V) : (H →L[ℝ] V) →ₗ[ℝ] ℝ where
  toFun L := LinearMap.trace ℝ H ((graphProj ι).toLinearMap ∘ₗ L.toLinearMap)
  map_add' L L' := by
    have h : ((L + L' : H →L[ℝ] V)).toLinearMap = L.toLinearMap + L'.toLinearMap := rfl
    rw [h, LinearMap.comp_add, map_add]
  map_smul' c L := by
    have h : ((c • L : H →L[ℝ] V)).toLinearMap = c • L.toLinearMap := rfl
    rw [h, LinearMap.comp_smul, map_smul]
    rfl

theorem graphTrace_apply (ι : H →ₗᵢ[ℝ] V) (L : H →L[ℝ] V) :
    graphTrace ι L = LinearMap.trace ℝ H ((graphProj ι).toLinearMap ∘ₗ L.toLinearMap) := rfl

/-- The tangential divergence functional: the tangential trace of the restriction of a map of `V`
to the tangent factor. -/
def tangentDiv (ι : H →ₗᵢ[ℝ] V) : (V →L[ℝ] V) →ₗ[ℝ] ℝ where
  toFun M := graphTrace ι (M.comp ι.toContinuousLinearMap)
  map_add' M M' := by
    rw [ContinuousLinearMap.add_comp, map_add]
  map_smul' c M := by
    rw [ContinuousLinearMap.smul_comp, map_smul]
    rfl

theorem tangentDiv_apply (ι : H →ₗᵢ[ℝ] V) (M : V →L[ℝ] V) :
    tangentDiv ι M = graphTrace ι (M.comp ι.toContinuousLinearMap) := rfl

theorem continuous_tangentDiv (ι : H →ₗᵢ[ℝ] V) : Continuous (tangentDiv ι) :=
  (tangentDiv ι).continuous_of_finiteDimensional

theorem tangentDiv_zero (ι : H →ₗᵢ[ℝ] V) : tangentDiv ι 0 = 0 := map_zero _

/-- The tangential trace of a rank-one map. -/
theorem graphTrace_smulRight (ι : H →ₗᵢ[ℝ] V) (a : H) (v : V) :
    graphTrace ι ((innerSL ℝ a).smulRight v) = (⟪a, graphProj ι v⟫ : ℝ) := by
  rw [graphTrace_apply]
  have h : (graphProj ι).toLinearMap ∘ₗ ((innerSL ℝ a).smulRight v).toLinearMap
      = LinearMap.smulRight (innerSL ℝ a).toLinearMap (graphProj ι v) := by
    ext w; simp
  rw [h, trace_smulRight]
  rfl

/-- The tangential trace along a graph derivative picks up the slope term. -/
theorem graphTrace_comp_graphLinear (ι : H →ₗᵢ[ℝ] V) (e : V) (M : V →L[ℝ] V) (a : H) :
    graphTrace ι (M.comp (graphLinear ι e a))
      = tangentDiv ι M + (⟪a, graphProj ι (M e)⟫ : ℝ) := by
  have hsplit : M.comp (graphLinear ι e a)
      = M.comp ι.toContinuousLinearMap + (innerSL ℝ a).smulRight (M e) := by
    ext v; simp [graphLinear_apply]
  rw [hsplit, map_add, graphTrace_smulRight, tangentDiv_apply]

variable {ι : H →ₗᵢ[ℝ] V} {e : V}

/-- **Splitting of the divergence.**  In the orthogonal splitting `V = ι H ⊕ ℝ e` the divergence
of a vector field is its tangential divergence plus the normal derivative of its normal
component. -/
theorem divergence_eq_tangentDiv_add (hsp : IsGraphSplitting ι e) (F : V → V) (x : V) :
    divergence F x = tangentDiv ι (fderiv ℝ F x) + (⟪e, fderiv ℝ F x e⟫ : ℝ) := by
  set L : V →ₗ[ℝ] V := (fderiv ℝ F x).toLinearMap with hL
  have hsplit : (LinearMap.id : V →ₗ[ℝ] V)
      = ι.toLinearMap ∘ₗ (graphProj ι).toLinearMap
        + LinearMap.smulRight (innerSL ℝ e).toLinearMap e := by
    ext w
    simpa [graphRetract_apply] using (hsp.split w).symm
  have hLsplit : L = L ∘ₗ (ι.toLinearMap ∘ₗ (graphProj ι).toLinearMap)
      + L ∘ₗ (LinearMap.smulRight (innerSL ℝ e).toLinearMap e) := by
    rw [← LinearMap.comp_add, ← hsplit, LinearMap.comp_id]
  have hnormal : L ∘ₗ (LinearMap.smulRight (innerSL ℝ e).toLinearMap e)
      = LinearMap.smulRight (innerSL ℝ e).toLinearMap (L e) := by
    ext w; simp
  have htang : L ∘ₗ (ι.toLinearMap ∘ₗ (graphProj ι).toLinearMap)
      = (L ∘ₗ ι.toLinearMap) ∘ₗ (graphProj ι).toLinearMap := by
    rw [LinearMap.comp_assoc]
  rw [divergence, ← hL, hLsplit, map_add, hnormal, htang,
    LinearMap.trace_comp_comm' (graphProj ι).toLinearMap (L ∘ₗ ι.toLinearMap),
    trace_smulRight]
  rfl

/-- The divergence of the tangential part of a vector field pulled back along a differentiable
map. -/
theorem divergence_graphProj_comp (ι : H →ₗᵢ[ℝ] V) {F : V → V} {γ : H → V} {y : H}
    (hF : DifferentiableAt ℝ F (γ y)) (hγ : DifferentiableAt ℝ γ y) :
    divergence (fun z => graphProj ι (F (γ z))) y
      = graphTrace ι ((fderiv ℝ F (γ y)).comp (fderiv ℝ γ y)) := by
  have hd : HasFDerivAt (fun z => graphProj ι (F (γ z)))
      ((graphProj ι).comp ((fderiv ℝ F (γ y)).comp (fderiv ℝ γ y))) y :=
    ((graphProj ι).hasFDerivAt.comp y (hF.hasFDerivAt.comp y hγ.hasFDerivAt))
  rw [divergence, hd.fderiv, graphTrace_apply]
  rfl

end Trace

/-! ### The divergence of a compactly supported field integrates to zero -/

section Zero

/-- The integral over the line of the derivative of a compactly supported `C¹` function
vanishes. -/
theorem integral_deriv_eq_zero {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h) :
    ∫ t, deriv h t ∂(volume : Measure ℝ) = 0 := by
  obtain ⟨M, hM⟩ := (hhc.isCompact.isBounded).subset_closedBall (0 : ℝ)
  have hnotmem : ∀ t : ℝ, M < t → t ∉ tsupport h := by
    intro t ht hmem
    have := hM hmem
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at this
    linarith [this.2]
  have hout : ∀ t : ℝ, M < t → deriv h t = 0 := by
    intro t ht
    have heq : h =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_compl_iff.mpr (isClosed_tsupport h)).mem_nhds (hnotmem t ht)]
        with s hs
      exact image_eq_zero_of_notMem_tsupport hs
    rw [heq.deriv_eq]
    simp
  have hint : Integrable (deriv h) (volume : Measure ℝ) :=
    (hh.continuous_deriv le_rfl).integrable_of_hasCompactSupport hhc.deriv
  have hsplit := integral_add_compl (measurableSet_Iic (a := M + 1)) hint
  have h1 : ∫ t in Iic (M + 1), deriv h t = h (M + 1) :=
    HasCompactSupport.integral_Iic_deriv_eq hh hhc (M + 1)
  have h2 : ∫ t in (Iic (M + 1))ᶜ, deriv h t = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    rw [Set.mem_compl_iff, Set.mem_Iic, not_le] at ht
    exact hout t (by linarith)
  have h3 : h (M + 1) = 0 :=
    image_eq_zero_of_notMem_tsupport (hnotmem (M + 1) (by linarith))
  rw [← hsplit, h1, h2, h3, add_zero]

/-- Induction step carrier: the statement of `integral_divergence_eq_zero`, quantified over the
space so that the orthogonal complement of a line can be fed back into it. -/
private theorem integral_divergence_aux (n : ℕ) :
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
      [MeasurableSpace H] [BorelSpace H], Module.finrank ℝ H = n →
      ∀ W : H → H, ContDiff ℝ 1 W → HasCompactSupport W →
        ∫ y, divergence W y ∂(volume : Measure H) = 0 := by
  induction n with
  | zero =>
    intro H _ _ _ _ _ hrank W _ _
    have hss : Subsingleton H := Module.finrank_zero_iff.mp hrank
    have hzero : ∀ y : H, divergence W y = 0 := by
      intro y
      have h0 : fderiv ℝ W y = 0 := Subsingleton.elim _ _
      rw [divergence, h0]
      simp
    simp [hzero]
  | succ n ih =>
    intro H _ _ _ _ _ hrank W hW hWc
    -- a unit vector of `H`, and the orthogonal splitting it defines
    have hpos : 0 < Module.finrank ℝ H := by omega
    have hnt : Nontrivial H := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨u₀, hu₀⟩ := exists_ne (0 : H)
    set u : H := ‖u₀‖⁻¹ • u₀ with hudef
    have hu : ‖u‖ = 1 := by
      rw [hudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu₀)]
    have hune : u ≠ 0 := by
      intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
    have hsp : IsGraphSplitting ((ℝ ∙ u)ᗮ : Submodule ℝ H).subtypeₗᵢ u :=
      isGraphSplitting_orthogonal hu
    have hrankK : Module.finrank ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ H) = n := by
      have h := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ u : Submodule ℝ H))
      rw [finrank_span_singleton hune] at h
      omega
    set ι : ((ℝ ∙ u)ᗮ : Submodule ℝ H) →ₗᵢ[ℝ] H := ((ℝ ∙ u)ᗮ : Submodule ℝ H).subtypeₗᵢ with hι
    set Φ : (((ℝ ∙ u)ᗮ : Submodule ℝ H) × ℝ) ≃ₜ H := splitHomeomorph hsp 0 with hΦ
    have hΦapply : ∀ p, Φ p = ι p.1 + p.2 • u := by
      intro p; rw [hΦ]; show (0 : H) + ι p.1 + p.2 • u = _; rw [zero_add]
    -- the two components of the divergence
    have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
    have hfd : Continuous (fderiv ℝ W) := hW.continuous_fderiv one_ne_zero
    have hfdc : HasCompactSupport (fderiv ℝ W) := hWc.fderiv ℝ
    set A : H → ℝ := fun x => tangentDiv ι (fderiv ℝ W x) with hA
    set B : H → ℝ := fun x => (⟪u, fderiv ℝ W x u⟫ : ℝ) with hB
    have hdecomp : ∀ x, divergence W x = A x + B x := divergence_eq_tangentDiv_add hsp W
    have hAcont : Continuous A := (continuous_tangentDiv ι).comp hfd
    have hBcont : Continuous B := by
      have h1 : Continuous fun x : H => fderiv ℝ W x u :=
        (ContinuousLinearMap.apply ℝ H u).continuous.comp hfd
      exact (innerSL ℝ u).continuous.comp h1
    have hAcs : HasCompactSupport A := by
      have := hfdc.comp_left (g := fun L : H →L[ℝ] H => tangentDiv ι L) (map_zero _)
      simpa [hA, Function.comp_def] using this
    have hBcs : HasCompactSupport B := by
      have := hfdc.comp_left (g := fun L : H →L[ℝ] H => (⟪u, L u⟫ : ℝ)) (by simp)
      simpa [hB, Function.comp_def] using this
    have hAint : Integrable (fun p => A (Φ p)) (volume : Measure _) :=
      (hAcont.comp Φ.continuous).integrable_of_hasCompactSupport (hAcs.comp_homeomorph Φ)
    have hBint : Integrable (fun p => B (Φ p)) (volume : Measure _) :=
      (hBcont.comp Φ.continuous).integrable_of_hasCompactSupport (hBcs.comp_homeomorph Φ)
    -- the tangential term integrates to zero on each slice, by the induction hypothesis
    have hAslice : ∀ t : ℝ, ∫ z, A (Φ (z, t)) ∂(volume : Measure _) = 0 := by
      intro t
      have hpath : (fun z' : ((ℝ ∙ u)ᗮ : Submodule ℝ H) => Φ (z', t))
          = fun z' => t • u + ι z' := by
        funext z'; rw [hΦapply]; abel
      have hγ : ∀ z : ((ℝ ∙ u)ᗮ : Submodule ℝ H),
          HasFDerivAt (fun z' : ((ℝ ∙ u)ᗮ : Submodule ℝ H) => Φ (z', t))
            ι.toContinuousLinearMap z := by
        intro z
        rw [hpath]
        exact (ι.toContinuousLinearMap.hasFDerivAt).const_add _
      have hγc : ContDiff ℝ 1 (fun z' : ((ℝ ∙ u)ᗮ : Submodule ℝ H) => Φ (z', t)) := by
        rw [hpath]
        exact contDiff_const.add ι.toContinuousLinearMap.contDiff
      have hγnorm : ∀ z' : ((ℝ ∙ u)ᗮ : Submodule ℝ H), ‖z'‖ ≤ ‖t • u‖ + ‖Φ (z', t)‖ := by
        intro z'
        have h1 : (ι z' : H) = Φ (z', t) - t • u := by rw [hΦapply]; abel
        have h2 : ‖z'‖ = ‖ι z'‖ := (ι.norm_map z').symm
        rw [h2, h1]
        have := norm_sub_le (Φ (z', t)) (t • u)
        linarith
      have hslice : ∀ z, A (Φ (z, t))
          = divergence (fun z' => graphProj ι (W (Φ (z', t)))) z := by
        intro z
        rw [divergence_graphProj_comp ι (hWd _) (hγ z).differentiableAt, (hγ z).fderiv]
        rfl
      simp_rw [hslice]
      refine ih ((ℝ ∙ u)ᗮ : Submodule ℝ H) hrankK _ ((graphProj ι).contDiff.comp (hW.comp hγc)) ?_
      exact hasCompactSupport_comp_of_norm_le
        (hWc.comp_left (g := fun w : H => graphProj ι w) (map_zero _)) _ hγnorm
    -- the normal term integrates to zero along each fibre, by the fundamental theorem of calculus
    have hBslice : ∀ z : ((ℝ ∙ u)ᗮ : Submodule ℝ H),
        ∫ t, B (Φ (z, t)) ∂(volume : Measure ℝ) = 0 := by
      intro z
      have hpath : (fun t' : ℝ => Φ (z, t')) = fun t' => (ι z : H) + t' • u := by
        funext t'; rw [hΦapply]
      have hpathd : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => Φ (z, t')) u t := by
        intro t
        rw [hpath]
        simpa using ((hasDerivAt_id t).smul_const u).const_add ((ι z : H))
      have hpathc : ContDiff ℝ 1 (fun t' : ℝ => Φ (z, t')) := by
        rw [hpath]
        exact contDiff_const.add (contDiff_id.smul contDiff_const)
      have hderiv : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => (⟪u, W (Φ (z, t'))⟫ : ℝ))
          (B (Φ (z, t))) t := by
        intro t
        have h1 : HasDerivAt (fun t' : ℝ => W (Φ (z, t'))) (fderiv ℝ W (Φ (z, t)) u) t :=
          (hWd _).hasFDerivAt.comp_hasDerivAt t (hpathd t)
        exact (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt t h1
      have hcd : ContDiff ℝ 1 (fun t' : ℝ => (⟪u, W (Φ (z, t'))⟫ : ℝ)) :=
        (innerSL ℝ u).contDiff.comp (hW.comp hpathc)
      have hcs : HasCompactSupport (fun t' : ℝ => (⟪u, W (Φ (z, t'))⟫ : ℝ)) := by
        refine hasCompactSupport_comp_of_norm_le
          (hWc.comp_left (g := fun w : H => (⟪u, w⟫ : ℝ)) (by simp)) ‖(ι z : H)‖ ?_
        intro t'
        have h1 : t' • u = Φ (z, t') - (ι z : H) := by rw [hΦapply]; abel
        have h2 : ‖t'‖ = ‖t' • u‖ := by rw [norm_smul, hu, mul_one]
        rw [h2, h1]
        have := norm_sub_le (Φ (z, t')) ((ι z : H))
        linarith
      have := integral_deriv_eq_zero hcd hcs
      rw [← this]
      exact integral_congr_ae (Eventually.of_forall fun t => ((hderiv t).deriv).symm)
    -- assembling the two vanishing contributions
    have hstep : ∫ y, divergence W y ∂(volume : Measure H)
        = ∫ p, (A (Φ p) + B (Φ p)) ∂(volume : Measure _) := by
      rw [((measurePreserving_splitHomeomorph hsp (0 : H)).integral_comp
        (splitHomeomorph hsp (0 : H)).measurableEmbedding (fun x => A x + B x))]
      exact integral_congr_ae (Eventually.of_forall hdecomp)
    rw [hstep, integral_add hAint hBint]
    have hAint' : Integrable (Function.uncurry fun z t => A (Φ (z, t)))
        ((volume : Measure ((ℝ ∙ u)ᗮ : Submodule ℝ H)).prod (volume : Measure ℝ)) := by
      rw [← Measure.volume_eq_prod]; exact hAint
    have hBint' : Integrable (Function.uncurry fun z t => B (Φ (z, t)))
        ((volume : Measure ((ℝ ∙ u)ᗮ : Submodule ℝ H)).prod (volume : Measure ℝ)) := by
      rw [← Measure.volume_eq_prod]; exact hBint
    have hA0 : ∫ p, A (Φ p) ∂(volume : Measure _) = 0 := by
      have hfub : ∫ p, A (Φ p) ∂(volume : Measure _)
          = ∫ z, ∫ t, A (Φ (z, t)) ∂(volume : Measure ℝ)
              ∂(volume : Measure ((ℝ ∙ u)ᗮ : Submodule ℝ H)) := by
        rw [Measure.volume_eq_prod]
        exact (integral_integral hAint').symm
      rw [hfub, integral_integral_swap hAint']
      simp [hAslice]
    have hB0 : ∫ p, B (Φ p) ∂(volume : Measure _) = 0 := by
      have hfub : ∫ p, B (Φ p) ∂(volume : Measure _)
          = ∫ z, ∫ t, B (Φ (z, t)) ∂(volume : Measure ℝ)
              ∂(volume : Measure ((ℝ ∙ u)ᗮ : Submodule ℝ H)) := by
        rw [Measure.volume_eq_prod]
        exact (integral_integral hBint').symm
      rw [hfub]
      simp [hBslice]
    rw [hA0, hB0, add_zero]

/-- **The divergence of a compactly supported `C¹` vector field integrates to zero.**  There is no
boundary term: the ambient space has no boundary.  The proof is an induction on the dimension,
splitting off one direction at a time with `isGraphSplitting_orthogonal` and integrating the
normal derivative by the fundamental theorem of calculus. -/
theorem integral_divergence_eq_zero {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] {W : H → H} (hW : ContDiff ℝ 1 W)
    (hWc : HasCompactSupport W) :
    ∫ y, divergence W y ∂(volume : Measure H) = 0 :=
  integral_divergence_aux (Module.finrank ℝ H) H rfl W hW hWc

end Zero

/-! ### Auxiliary estimates for the tangential projection -/

section Projection

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The tangential projection is the adjoint of the embedding. -/
theorem inner_graphProj_right (ι : H →ₗᵢ[ℝ] V) (a : H) (w : V) :
    (⟪a, graphProj ι w⟫ : ℝ) = ⟪ι a, w⟫ :=
  ContinuousLinearMap.adjoint_inner_right _ _ _

/-- The tangential projection is a contraction. -/
theorem norm_graphProj_le (ι : H →ₗᵢ[ℝ] V) (w : V) : ‖graphProj ι w‖ ≤ ‖w‖ := by
  have h1 : (⟪graphProj ι w, graphProj ι w⟫ : ℝ) = ⟪ι (graphProj ι w), w⟫ :=
    inner_graphProj_right ι _ w
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 : (⟪ι (graphProj ι w), w⟫ : ℝ) ≤ ‖ι (graphProj ι w)‖ * ‖w‖ :=
    real_inner_le_norm _ _
  rw [ι.norm_map] at h2
  nlinarith [norm_nonneg (graphProj ι w), norm_nonneg w]

end Projection

/-! ### The divergence formula on a subgraph -/

section Subgraph

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {ι : H →ₗᵢ[ℝ] V} {e : V}

/-- **Divergence formula on a smooth subgraph.** -/
theorem integral_divergence_subgraph (hsp : IsGraphSplitting ι e) (x₀ : V) {g : H → ℝ}
    (hg : ContDiff ℝ 1 g) {F : V → V} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ∫ x in {x : V | graphHeight e x₀ x < g (graphCoord ι x₀ x)}, divergence F x =
      ∫ y : H, (⟪F (graphChartMap ι e x₀ g y), ι (-(gradient g y)) + e⟫ : ℝ) := by
  classical
  have hgc : Continuous g := hg.continuous
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hfdcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have hgradcont : Continuous (gradient g) := BakryEmery.continuous_gradient hg
  have hcoordcont : Continuous fun x : V => graphCoord ι x₀ x :=
    (graphProj ι).continuous.comp (continuous_id.sub continuous_const)
  set Ξ : (H × ℝ) ≃ₜ V := graphChartHomeomorph hsp x₀ hgc with hΞ
  have hΞapply : ∀ p : H × ℝ, Ξ p = x₀ + ι p.1 + (p.2 + g p.1) • e := fun p => rfl
  have hΞcoord : ∀ p : H × ℝ, graphCoord ι x₀ (Ξ p) = p.1 :=
    graphCoord_graphChartHomeomorph hsp x₀ hgc
  have hΞheight : ∀ p : H × ℝ, graphHeight e x₀ (Ξ p) = p.2 + g p.1 :=
    graphHeight_graphChartHomeomorph hsp x₀ hgc
  have hΞzero : ∀ y : H, Ξ (y, 0) = graphChartMap ι e x₀ g y :=
    graphChartHomeomorph_zero hsp x₀
      hgc
  -- the two pieces of the integrand, as functions on `V`


  -- Split the ambient divergence into tangential and normal contributions.
  set Aamb : V → ℝ := fun x =>
    tangentDiv ι (fderiv ℝ F x) +
      (⟪gradient g (graphCoord ι x₀ x), graphProj ι (fderiv ℝ F x e)⟫ : ℝ) with
    hAamb
  set Qamb : V → ℝ := fun x => (⟪e - ι (gradient g (graphCoord ι x₀ x)), F x⟫ : ℝ) with hQamb
  set Bamb : V → ℝ := fun x =>
    (⟪e - ι (gradient g (graphCoord ι x₀ x)), fderiv ℝ F x e⟫ : ℝ) with hBamb
  have hAcont : Continuous Aamb := by
    refine Continuous.add ((continuous_tangentDiv ι).comp hfdcont) ?_
    refine Continuous.inner (hgradcont.comp hcoordcont) ?_
    exact
      (graphProj ι).continuous.comp ((ContinuousLinearMap.apply ℝ V e).continuous.comp hfdcont)
  have hQcont : Continuous Qamb :=
    Continuous.inner (continuous_const.sub (ι.continuous.comp (hgradcont.comp hcoordcont)))
      hF.continuous
  have hAcs : HasCompactSupport Aamb := by
    refine HasCompactSupport.intro hFc.isCompact fun x hx => ?_
    show
      tangentDiv ι (fderiv ℝ F x) +
          (⟪gradient g (graphCoord ι x₀ x), graphProj ι (fderiv ℝ F x e)⟫ : ℝ) =
        0
    simp [fderiv_of_notMem_tsupport ℝ hx]
  have hQcs : HasCompactSupport Qamb := by
    refine HasCompactSupport.intro hFc.isCompact fun x hx => ?_
    show (⟪e - ι (gradient g (graphCoord ι x₀ x)), F x⟫ : ℝ) = 0
    rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_right]
  have hBcont : Continuous Bamb :=
    Continuous.inner (continuous_const.sub (ι.continuous.comp (hgradcont.comp hcoordcont)))
      ((ContinuousLinearMap.apply ℝ V e).continuous.comp hfdcont)
  have hBcs : HasCompactSupport Bamb := by
    refine HasCompactSupport.intro hFc.isCompact fun x hx => ?_
    show (⟪e - ι (gradient g (graphCoord ι x₀ x)), fderiv ℝ F x e⟫ : ℝ) = 0
    rw [fderiv_of_notMem_tsupport ℝ hx]
    simp
  -- the pointwise splitting of the divergence

  have hsplit : ∀ x : V, divergence F x = Aamb x + Bamb x := by
    intro x
    rw [divergence_eq_tangentDiv_add hsp F x]
    show
      _ =
        (tangentDiv ι (fderiv ℝ F x) +
            (⟪gradient g (graphCoord ι x₀ x), graphProj ι (fderiv ℝ F x e)⟫ : ℝ)) +
          (⟪e - ι (gradient g (graphCoord ι x₀ x)), fderiv ℝ F x e⟫ : ℝ)
    rw [inner_sub_left,
      inner_graphProj_right ι (gradient g (graphCoord ι x₀ x)) (fderiv ℝ F x e)]
    ring
  -- the tangential piece is the divergence of a compactly supported field on `H`

  have hAslice :
    ∀ (s : ℝ) (y : H), Aamb (Ξ (y, s)) = divergence (fun z => graphProj ι (F (Ξ (z, s)))) y := by
    intro s y
    have hpath : (fun z : H => Ξ (z, s)) = fun z => x₀ + graphMap ι e (fun z => s + g z) z := by
      funext z; rw [hΞapply, graphMap, add_assoc]
    have hgrad : gradient (fun z : H => s + g z) y = gradient g y := by
      have hf : fderiv ℝ (fun z : H => s + g z) y = fderiv ℝ g y :=
        ((hgd y).hasFDerivAt.const_add s).fderiv
      rw [gradient, gradient, hf]
    have hd : HasFDerivAt (fun z : H => Ξ (z, s)) (graphLinear ι e (gradient g y)) y := by
      rw [hpath, ← hgrad]
      exact
        (hasFDerivAt_graphMap ι e
              (((contDiff_const.add hg).differentiable one_ne_zero) y)).const_add
          x₀
    rw [divergence_graphProj_comp ι (hFd _) hd.differentiableAt, hd.fderiv,
      graphTrace_comp_graphLinear, hAamb]
    simp only [hΞcoord (y, s)]
  -- the slice fields are `C¹` with compact support

  have hslicecd : ∀ s : ℝ, ContDiff ℝ 1 (fun z : H => graphProj ι (F (Ξ (z, s)))) := by
    intro s
    have hpath : ContDiff ℝ 1 (fun z : H => Ξ (z, s)) := by
      have h : (fun z : H => Ξ (z, s)) = fun z => x₀ + (ι z + (s + g z) • e) := by
        funext z;
        rw [hΞapply, add_assoc]
      rw [h]
      exact
        contDiff_const.add
          (ι.toContinuousLinearMap.contDiff.add ((contDiff_const.add hg).smul contDiff_const))
    exact (graphProj ι).contDiff.comp (hF.comp hpath)
  have hslicecs : ∀ s : ℝ, HasCompactSupport (fun z : H => graphProj ι (F (Ξ (z, s)))) := by
    intro s
    refine
      hasCompactSupport_comp_of_norm_le
        (hFc.comp_left (g := fun w : V => graphProj ι w) (map_zero _)) ‖x₀‖ ?_
    intro z
    have h1 : ‖z‖ = ‖graphCoord ι x₀ (Ξ (z, s))‖ := by rw [hΞcoord (z, s)]
    have h2 : ‖graphCoord ι x₀ (Ξ (z, s))‖ ≤ ‖Ξ (z, s) - x₀‖ := norm_graphProj_le ι _
    have h3 : ‖Ξ (z, s) - x₀‖ ≤ ‖Ξ (z, s)‖ + ‖x₀‖ := norm_sub_le _ _
    rw [h1];
    linarith
  -- the fibre derivative of the normal piece


  -- Compute the normal derivative along the chart fibers.
  have hqpath : ∀ y : H, (fun σ : ℝ => Ξ (y, σ)) = fun σ => (x₀ + ι y + g y • e) + σ • e := by
    intro y
    funext σ
    rw [hΞapply]
    show x₀ + ι y + (σ + g y) • e = x₀ + ι y + g y • e + σ • e
    rw [add_smul, add_assoc]
    abel
  have hqderiv :
    ∀ (y : H) (s : ℝ), HasDerivAt (fun σ : ℝ => Qamb (Ξ (y, σ))) (Bamb (Ξ (y, s))) s := by
    intro y s
    have hpathd : HasDerivAt (fun σ' : ℝ => Ξ (y, σ')) e s := by
      rw [hqpath y]
      simpa using ((hasDerivAt_id s).smul_const e).const_add (x₀ + ι y + g y • e)
    have h1 : HasDerivAt (fun σ : ℝ => F (Ξ (y, σ))) (fderiv ℝ F (Ξ (y, s)) e) s :=
      (hFd _).hasFDerivAt.comp_hasDerivAt s hpathd
    have h2 := (innerSL ℝ (e - ι (gradient g y))).hasFDerivAt.comp_hasDerivAt s h1
    have h3 :
      (fun σ : ℝ => Qamb (Ξ (y, σ))) = fun σ : ℝ =>
        (⟪e - ι (gradient g y), F (Ξ (y, σ))⟫ : ℝ) := by
      funext σ
      show (⟪e - ι (gradient g (graphCoord ι x₀ (Ξ (y, σ)))), F (Ξ (y, σ))⟫ : ℝ) = _
      rw [hΞcoord (y, σ)]
    have h4 : Bamb (Ξ (y, s)) = (⟪e - ι (gradient g y), fderiv ℝ F (Ξ (y, s)) e⟫ : ℝ) := by
      show (⟪e - ι (gradient g (graphCoord ι x₀ (Ξ (y, s)))), fderiv ℝ F (Ξ (y, s)) e⟫ : ℝ) = _
      rw [hΞcoord (y, s)]
    rw [h3, h4]
    exact h2
  have hqcd : ∀ y : H, ContDiff ℝ 1 (fun σ : ℝ => Qamb (Ξ (y, σ))) := by
    intro y
    have hpath : ContDiff ℝ 1 (fun σ : ℝ => Ξ (y, σ)) := by
      rw [hqpath y]
      exact contDiff_const.add (contDiff_id.smul contDiff_const)
    have h3 :
      (fun σ : ℝ => Qamb (Ξ (y, σ))) = fun σ : ℝ =>
        (⟪e - ι (gradient g y), F (Ξ (y, σ))⟫ : ℝ) := by
      funext σ
      show (⟪e - ι (gradient g (graphCoord ι x₀ (Ξ (y, σ)))), F (Ξ (y, σ))⟫ : ℝ) = _
      rw [hΞcoord (y, σ)]
    rw [h3]
    exact (innerSL ℝ (e - ι (gradient g y))).contDiff.comp (hF.comp hpath)
  have hfibrenorm : ∀ (y : H) (σ : ℝ), ‖σ‖ ≤ ‖x₀ + ι y + g y • e‖ + ‖Ξ (y, σ)‖ := by
    intro y σ
    have h1 : ‖σ‖ = ‖σ • e‖ := by rw [norm_smul, hsp.norm_e, mul_one]
    have h2 : σ • e = Ξ (y, σ) - (x₀ + ι y + g y • e) := by rw [congrFun (hqpath y) σ]; abel
    rw [h1, h2]
    have := norm_sub_le (Ξ (y, σ)) (x₀ + ι y + g y • e)
    linarith
  have hqcs : ∀ y : H, HasCompactSupport (fun σ : ℝ => Qamb (Ξ (y, σ))) := fun y =>
    hasCompactSupport_comp_of_norm_le (hQcs.comp_homeomorph (Homeomorph.refl V))
      ‖x₀ + ι y + g y • e‖ (hfibrenorm y)
  have hBcsfibre : ∀ y : H, HasCompactSupport (fun σ : ℝ => Bamb (Ξ (y, σ))) := fun y =>
    hasCompactSupport_comp_of_norm_le (hBcs.comp_homeomorph (Homeomorph.refl V))
      ‖x₀ + ι y + g y • e‖
      (hfibrenorm y)
  -- the fundamental theorem of calculus along each fibre

  have hFTC : ∀ y : H, ∫ s in Iic (0 : ℝ), Bamb (Ξ (y, s)) = Qamb (Ξ (y, 0)) := by
    intro y
    rw [← HasCompactSupport.integral_Iic_deriv_eq (hqcd y) (hqcs y) 0]
    exact
      setIntegral_congr_fun measurableSet_Iic fun s _ =>
        ((hqderiv y s).deriv).symm
  -- integrability of the two pieces along the chart


  -- Check integrability before changing variables and applying Fubini.
  have hAΞint : Integrable (fun p : H × ℝ => Aamb (Ξ p)) (volume : Measure (H × ℝ)) :=
    (hAcont.comp Ξ.continuous).integrable_of_hasCompactSupport (hAcs.comp_homeomorph Ξ)
  have hBΞint : Integrable (fun p : H × ℝ => Bamb (Ξ p)) (volume : Measure (H × ℝ)) :=
    (hBcont.comp Ξ.continuous).integrable_of_hasCompactSupport (hBcs.comp_homeomorph Ξ)
  have hmeaseq :
    (volume : Measure (H × ℝ)).restrict (Set.univ ×ˢ Iio (0 : ℝ)) =
      (volume : Measure H).prod ((volume : Measure ℝ).restrict (Iio 0)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hAprod :
    Integrable (Function.uncurry fun y s => Aamb (Ξ (y, s)))
      ((volume : Measure H).prod ((volume : Measure ℝ).restrict (Iio 0))) := by
    rw [← hmeaseq]; exact hAΞint.restrict
  have hBprod :
    Integrable (Function.uncurry fun y s => Bamb (Ξ (y, s)))
      ((volume : Measure H).prod ((volume : Measure ℝ).restrict (Iio 0))) := by
    rw [← hmeaseq];
    exact
      hBΞint.restrict
  -- the divergence itself

  have hDcont : Continuous (divergence F) := by
    have h : (divergence F) = fun x => Aamb x + Bamb x := funext hsplit
    rw [h]; exact hAcont.add hBcont
  have hDcs : HasCompactSupport (divergence F) := by
    have h : (divergence F) = fun x => Aamb x + Bamb x := funext hsplit
    rw [h]; exact hAcs.add hBcs
  have hDΞint : Integrable (fun p : H × ℝ => divergence F (Ξ p)) (volume : Measure (H × ℝ)) :=
    (hDcont.comp Ξ.continuous).integrable_of_hasCompactSupport (hDcs.comp_homeomorph Ξ)
  have hDprod :
    Integrable (Function.uncurry fun y s => divergence F (Ξ (y, s)))
      ((volume : Measure H).prod ((volume : Measure ℝ).restrict (Iio 0))) := by
    rw [← hmeaseq];
    exact
      hDΞint.restrict
  -- step 1: change of variables and Fubini

  have hSopen : IsOpen {x : V | graphHeight e x₀ x < g (graphCoord ι x₀ x)} := by
    have h1 : Continuous fun x : V => graphHeight e x₀ x :=
      (innerSL ℝ e).continuous.comp (continuous_id.sub continuous_const)
    exact isOpen_lt h1 (hgc.comp hcoordcont)
  have hΞS :
    ∀ p : H × ℝ,
      Ξ p ∈ {x : V | graphHeight e x₀ x < g (graphCoord ι x₀ x)} ↔
        p ∈ Set.univ ×ˢ Iio (0 : ℝ) := by
    intro p
    simp only [Set.mem_ofPred_eq, hΞcoord p, hΞheight p, Set.mem_prod, Set.mem_univ,
      Set.mem_Iio, true_and]
    constructor <;> intro h <;> linarith
  have hstep1 :
    ∫ x in {x : V | graphHeight e x₀ x < g (graphCoord ι x₀ x)}, divergence F x =
      ∫ y,
        ∫ s in Iio (0 : ℝ),
          divergence F (Ξ (y, s)) ∂(volume : Measure ℝ) ∂(volume : Measure H) := by
    rw [← integral_indicator hSopen.measurableSet, ←
      integral_comp_graphChartHomeomorph hsp x₀ hgc
        (Set.indicator {x : V | graphHeight e x₀ x < g (graphCoord ι x₀ x)} (divergence F))]
    have hind :
      ∀ p : H × ℝ,
        Set.indicator {x : V | graphHeight e x₀ x < g (graphCoord ι x₀ x)} (divergence F)
            (Ξ p) =
          (Set.univ ×ˢ Iio (0 : ℝ)).indicator (fun p : H × ℝ => divergence F (Ξ p)) p := by
      intro p
      by_cases hp : p ∈ Set.univ ×ˢ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ((hΞS p).mpr hp), Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem (fun h => hp ((hΞS p).mp h)), Set.indicator_of_notMem hp]
    rw [integral_congr_ae (Eventually.of_forall hind),
      integral_indicator (MeasurableSet.univ.prod measurableSet_Iio), hmeaseq]
    exact
      (integral_integral hDprod).symm
  -- step 2: split the integrand fibre by fibre

  have hfibrecont : ∀ y : H, Continuous fun σ : ℝ => Ξ (y, σ) := fun y =>
    Ξ.continuous.comp (continuous_const.prodMk continuous_id)
  have hAinner : ∀ y : H, IntegrableOn (fun s : ℝ => Aamb (Ξ (y, s))) (Iio 0) volume := by
    intro y
    exact
      ((hAcont.comp (hfibrecont y)).integrable_of_hasCompactSupport
          (hasCompactSupport_comp_of_norm_le (hAcs.comp_homeomorph (Homeomorph.refl V))
            ‖x₀ + ι y + g y • e‖ (hfibrenorm y))).integrableOn
  have hBinner : ∀ y : H, IntegrableOn (fun s : ℝ => Bamb (Ξ (y, s))) (Iio 0) volume := by
    intro y
    exact
      ((hBcont.comp (hfibrecont y)).integrable_of_hasCompactSupport (hBcsfibre y)).integrableOn
  have hinner :
    ∀ y : H,
      ∫ s in Iio (0 : ℝ), divergence F (Ξ (y, s)) =
        (∫ s in Iio (0 : ℝ), Aamb (Ξ (y, s))) + ∫ s in Iio (0 : ℝ), Bamb (Ξ (y, s)) := by
    intro y
    rw [← integral_add (hAinner y) (hBinner y)]
    exact setIntegral_congr_fun measurableSet_Iio fun s _ => hsplit (Ξ (y, s))
  have hAouter :
    Integrable (fun y : H => ∫ s in Iio (0 : ℝ), Aamb (Ξ (y, s))) (volume : Measure H) :=
    hAprod.integral_prod_left
  have hBouter :
    Integrable (fun y : H => ∫ s in Iio (0 : ℝ), Bamb (Ξ (y, s))) (volume : Measure H) :=
    hBprod.integral_prod_left

  -- Evaluate the tangential integral and the normal boundary term separately.
  have hstep2 :
    ∫ y,
        ∫ s in Iio (0 : ℝ),
          divergence F (Ξ (y, s)) ∂(volume : Measure ℝ) ∂(volume : Measure H) =
      (∫ y, ∫ s in Iio (0 : ℝ), Aamb (Ξ (y, s)) ∂(volume : Measure ℝ) ∂(volume : Measure H)) +
        ∫ y, ∫ s in Iio (0 : ℝ), Bamb (Ξ (y, s)) ∂(volume : Measure ℝ) ∂(volume : Measure H) := by
    rw [integral_congr_ae (Eventually.of_forall hinner), integral_add hAouter hBouter]
  -- step 3: the tangential contribution vanishes

  have hstep3 :
    ∫ y, ∫ s in Iio (0 : ℝ), Aamb (Ξ (y, s)) ∂(volume : Measure ℝ) ∂(volume : Measure H) = 0 := by
    rw [integral_integral_swap hAprod]
    have hzero : ∀ s : ℝ, ∫ y, Aamb (Ξ (y, s)) ∂(volume : Measure H) = 0 := by
      intro s
      rw [show
          (fun y : H => Aamb (Ξ (y, s))) = fun y : H =>
            divergence (fun z : H => graphProj ι (F (Ξ (z, s)))) y
          from funext (hAslice s)]
      exact integral_divergence_eq_zero (hslicecd s) (hslicecs s)
    simp [hzero]
  -- step 4: the normal contribution is the boundary flux

  have hstep4 :
    ∫ y, ∫ s in Iio (0 : ℝ), Bamb (Ξ (y, s)) ∂(volume : Measure ℝ) ∂(volume : Measure H) =
      ∫ y, Qamb (Ξ (y, 0)) ∂(volume : Measure H) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ∫ s in Iio (0 : ℝ), Bamb (Ξ (y, s)) = Qamb (Ξ (y, 0))
    rw [setIntegral_congr_set (Iio_ae_eq_Iic (a := (0 : ℝ)))]
    exact hFTC y
  rw [hstep1, hstep2, hstep3, hstep4, zero_add]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show (⟪e - ι (gradient g (graphCoord ι x₀ (Ξ (y, 0)))), F (Ξ (y, 0))⟫ : ℝ) = _
  rw [hΞcoord (y, 0), hΞzero y, real_inner_comm]
  congr 1
  rw [map_neg]
  abel

end Subgraph

end FunctionalInequalities.Analysis

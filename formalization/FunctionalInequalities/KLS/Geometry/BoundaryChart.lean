import FunctionalInequalities.KLS.Geometry.SmoothDomain
import FunctionalInequalities.Analysis.Graph.Implicit

/-!
# The outward normal and the local boundary chart of a smooth domain

Application layer of `Analysis/Graph/Implicit.lean` to `KLS.SmoothDomain`.  Every statement in this
module is proved and uses only the standard axioms; the module contains **no** `sorry`.

## Why this module exists, and what it imports

`outwardNormal` and its four basic properties were introduced in
`KLS/WIP/AnalyticPrerequisites.lean` together with the still-open Gauss–Green obligations.  The
local boundary chart proved here is an *input* to Gauss–Green, so it has to sit below that module;
the definition and its proved lemmas therefore moved down here verbatim (same namespace, same
names, same statements — no compatibility alias, no duplicated proof, no forwarding declaration),
with the global consequences now importing this module through `LocalGaussGreen`.

`KLS/Geometry/SmoothDomain.lean` supplies the smooth-domain foundations with no WIP imports.

## Contents

* `SmoothDomain.outwardNormal` and `outwardNormal_eq`, `norm_outwardNormal`,
  `continuousOn_outwardNormal`, `measurable_outwardNormal` (moved, unchanged).
* `SmoothDomain.tangentSpace x₀ = (ℝ ∙ outwardNormal x₀)ᗮ` and its isometric embedding
  `tangentEmbedding`, with `isGraphSplitting_tangent` identifying `V = tangent ⊕ ℝ ν`.
* `SmoothDomain.BoundaryChart U x₀`: a local `C^∞` graph chart of the boundary at a frontier
  point.  Its three substantive fields are set *equalities*, not inclusions: the frontier meets the
  cylinder exactly in the graph, the domain meets the cylinder exactly below the graph, and the
  outward normal along the graph is `(ι (-∇g) + ν) / √(1 + ‖∇g‖²)`.
* `SmoothDomain.exists_boundaryChart`: every frontier point has such a chart.
* `BoundaryChart.surfaceMeasure_image` and
  `BoundaryChart.surfaceMeasure_frontier_inter_cylinder`: the normalized surface measure of a
  boundary piece is `∫ √(1 + ‖∇g‖²)` over the corresponding parameter set.

## Dimension zero

A subsingleton space has no frontier points at all (every set is clopen), so every statement below
that assumes `x₀ ∈ frontier U.carrier` is vacuous there.  Nothing in this module assumes
`Nontrivial V`; where nondegeneracy is needed it is *derived* from the frontier point, through
`‖outwardNormal x₀‖ = 1`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FunctionalInequalities

universe u

namespace KLS.SmoothDomain

section Normal

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

open Classical in
/-- The outward unit normal of a smooth domain: at a frontier point, the normalized gradient of a
local defining function (chosen by `exists_defining`); zero away from the frontier.  Any defining
function gives the same vector (`outwardNormal_eq`), and the vector has norm one on the frontier
(`norm_outwardNormal`). -/
def outwardNormal (U : SmoothDomain V) (x : V) : V :=
  if h : x ∈ frontier U.carrier then
    ‖gradient (U.exists_defining x h).choose_spec.choose x‖⁻¹ •
      gradient (U.exists_defining x h).choose_spec.choose x
  else 0

/-- If a real function vanishes at `0` and has a negative derivative there, it is negative just
to the right of `0`. -/
private theorem eventually_lt_zero_of_hasDerivAt {g : ℝ → ℝ} {c : ℝ} (hg : HasDerivAt g c 0)
    (hg0 : g 0 = 0) (hc : c < 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < 0 := by
  have hslope : Tendsto (slope g 0) (𝓝[≠] (0 : ℝ)) (𝓝 c) := hasDerivAt_iff_tendsto_slope.mp hg
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope g 0 t < 0 :=
    (hslope.eventually_lt_const hc).filter_mono (nhdsWithin_mono 0 fun _ ht => ne_of_gt ht)
  filter_upwards [h2, self_mem_nhdsWithin] with t ht htpos
  have htne : t ≠ 0 := ne_of_gt htpos
  have hgt : g t = slope g 0 t * t := by
    rw [slope_def_field, hg0]
    field_simp
    ring
  rw [hgt]
  exact mul_neg_of_neg_of_pos ht htpos

/-- If a real function vanishes at `0` and has a positive derivative there, it is positive just
to the right of `0`. -/
private theorem eventually_zero_lt_of_hasDerivAt {g : ℝ → ℝ} {c : ℝ} (hg : HasDerivAt g c 0)
    (hg0 : g 0 = 0) (hc : 0 < c) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g t := by
  have := eventually_lt_zero_of_hasDerivAt hg.neg (by simp [hg0]) (by simpa using hc)
  filter_upwards [this] with t ht
  simpa using ht

omit [CompleteSpace V] in
/-- The derivative of a `C¹` function along the ray `t ↦ x + t v`. -/
private theorem hasDerivAt_line {ψ : V → ℝ} {x : V} (hψ : DifferentiableAt ℝ ψ x) (v : V) :
    HasDerivAt (fun t : ℝ => ψ (x + t • v)) (fderiv ℝ ψ x v) 0 := by
  have hpath : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x
  exact hψ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)

omit [CompleteSpace V] in
/-- Two nonzero real linear functionals one of whose negative half-spaces is contained in the
other's nonpositive half-space are positive multiples of each other. -/
private theorem eq_smul_of_forall_lt_imp_le {A B : V →L[ℝ] ℝ} (hB : B ≠ 0)
    (hA : ∃ v, A v = 1) (h : ∀ v, A v < 0 → B v ≤ 0) :
    ∃ lam : ℝ, 0 < lam ∧ B = lam • A := by
  obtain ⟨v₀, hv₀⟩ := hA
  set lam := B v₀ with hlam
  have hlam0 : 0 ≤ lam := by
    have hneg : A (-v₀) < 0 := by rw [map_neg, hv₀]; norm_num
    have := h _ hneg
    rw [map_neg] at this
    linarith
  have hker : ∀ u, A u = 0 → B u = 0 := by
    intro u hu
    have hstep : ∀ ε : ℝ, 0 < ε → |B u| ≤ ε * lam := by
      intro ε hε
      have hA1 : A (u - ε • v₀) < 0 := by
        rw [map_sub, map_smul, smul_eq_mul, hu, hv₀]; simpa using hε
      have hA2 : A (-u - ε • v₀) < 0 := by
        rw [map_sub, map_neg, map_smul, smul_eq_mul, hu, hv₀]; simpa using hε
      have h1 := h _ hA1
      have h2 := h _ hA2
      rw [map_sub, map_smul, smul_eq_mul, ← hlam] at h1
      rw [map_sub, map_neg, map_smul, smul_eq_mul, ← hlam] at h2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    by_contra hne
    have h0 : 0 < |B u| := abs_pos.mpr hne
    have := hstep (|B u| / (lam + 1)) (by positivity)
    have hpos : (0 : ℝ) < lam + 1 := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos] at this
    nlinarith
  have hBeq : ∀ w, B w = A w * lam := by
    intro w
    have h0 : A (w - A w • v₀) = 0 := by rw [map_sub, map_smul, smul_eq_mul, hv₀]; ring
    have h1 := hker _ h0
    rw [map_sub, map_smul, smul_eq_mul, ← hlam] at h1
    linarith
  have hlamne : lam ≠ 0 := by
    intro h0
    exact hB (ContinuousLinearMap.ext fun w => by rw [hBeq w, h0, mul_zero]; rfl)
  exact ⟨lam, lt_of_le_of_ne hlam0 (Ne.symm hlamne),
    ContinuousLinearMap.ext fun w => by
      rw [hBeq w, smul_apply, smul_eq_mul, mul_comm]⟩

/-- The outward normal does not depend on the local defining function: for every defining pair
`(W, φ)` at a frontier point `x`, it is `∇φ x / ‖∇φ x‖`. -/
theorem outwardNormal_eq (U : SmoothDomain V) {x : V} (hx : x ∈ frontier U.carrier)
    {W : Set V} {φ : V → ℝ} (hW : IsOpen W) (hxW : x ∈ W) (hφ : ContDiff ℝ ∞ φ)
    (hφ' : ∀ y ∈ W, fderiv ℝ φ y ≠ 0) (hU : U.carrier ∩ W = {y ∈ W | φ y < 0}) :
    U.outwardNormal x = ‖gradient φ x‖⁻¹ • gradient φ x := by
  classical
  have key : ∀ (W₂ : Set V) (φ₂ : V → ℝ), IsOpen W₂ → x ∈ W₂ → ContDiff ℝ ∞ φ₂ →
      (∀ y ∈ W₂, fderiv ℝ φ₂ y ≠ 0) → U.carrier ∩ W₂ = {y ∈ W₂ | φ₂ y < 0} →
      ‖gradient φ₂ x‖⁻¹ • gradient φ₂ x = ‖gradient φ x‖⁻¹ • gradient φ x := by
    intro W₂ φ₂ hW₂ hxW₂ hφ₂ hφ₂' hU₂
    have hzero : φ x = 0 := by
      have hmem : x ∈ {y ∈ W | φ y = 0} := by
        rw [← U.frontier_inter_eq hW hφ hφ' hU]; exact ⟨hx, hxW⟩
      exact hmem.2
    have hzero₂ : φ₂ x = 0 := by
      have hmem : x ∈ {y ∈ W₂ | φ₂ y = 0} := by
        rw [← U.frontier_inter_eq hW₂ hφ₂ hφ₂' hU₂]; exact ⟨hx, hxW₂⟩
      exact hmem.2
    have hdiff : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
    have hdiff₂ : DifferentiableAt ℝ φ₂ x := hφ₂.differentiable (by simp) x
    have hcontline : ∀ v : V, Continuous fun t : ℝ => x + t • v := fun v =>
      continuous_const.add (continuous_id.smul continuous_const)
    have hmemev : ∀ (Z : Set V), IsOpen Z → x ∈ Z → ∀ v : V,
        ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∈ Z := by
      intro Z hZ hxZ v
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      have hca := (hcontline v).continuousAt (x := (0 : ℝ))
      rw [ContinuousAt, show x + (0 : ℝ) • v = x by simp] at hca
      exact hca (hZ.mem_nhds hxZ)
    have himp : ∀ v : V, fderiv ℝ φ x v < 0 → fderiv ℝ φ₂ x v ≤ 0 := by
      intro v hv
      by_contra hcon
      have hpos : 0 < fderiv ℝ φ₂ x v := lt_of_not_ge hcon
      have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ (x + t • v) < 0 :=
        eventually_lt_zero_of_hasDerivAt (hasDerivAt_line hdiff v) (by simpa using hzero) hv
      have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < φ₂ (x + t • v) :=
        eventually_zero_lt_of_hasDerivAt (hasDerivAt_line hdiff₂ v) (by simpa using hzero₂) hpos
      obtain ⟨t, ⟨ht1, ht2⟩, ht3, ht4⟩ :=
        ((e1.and e2).and ((hmemev W hW hxW v).and (hmemev W₂ hW₂ hxW₂ v))).exists
      have hmemU : x + t • v ∈ U.carrier := by
        have : x + t • v ∈ U.carrier ∩ W := by rw [hU]; exact ⟨ht3, ht1⟩
        exact this.1
      have : x + t • v ∈ U.carrier ∩ W₂ := ⟨hmemU, ht4⟩
      rw [hU₂] at this
      exact absurd this.2 (not_lt.mpr ht2.le)
    have hAone : ∃ v : V, fderiv ℝ φ x v = 1 := by
      obtain ⟨w, hw⟩ : ∃ w : V, fderiv ℝ φ x w ≠ 0 := by
        by_contra hcon
        refine hφ' x hxW (ContinuousLinearMap.ext fun w => ?_)
        simpa using not_exists.mp hcon w
      exact ⟨(fderiv ℝ φ x w)⁻¹ • w, by
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]⟩
    obtain ⟨lam, hlam, hBA⟩ := eq_smul_of_forall_lt_imp_le (hφ₂' x hxW₂) hAone himp
    have hgrad : gradient φ₂ x = lam • gradient φ x := by
      refine (InnerProductSpace.toDual ℝ V).injective ?_
      rw [map_smul, toDual_gradient (𝕜 := ℝ), toDual_gradient (𝕜 := ℝ), hBA]
    rw [hgrad, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, smul_smul]
    congr 1
    field_simp
  rw [outwardNormal, dif_pos hx]
  obtain ⟨h1, h2, h3, h4, h5⟩ := (U.exists_defining x hx).choose_spec.choose_spec
  exact key _ _ h1 h2 h3 h4 h5

/-- The outward normal is a unit vector on the frontier. -/
theorem norm_outwardNormal (U : SmoothDomain V) {x : V} (hx : x ∈ frontier U.carrier) :
    ‖U.outwardNormal x‖ = 1 := by
  classical
  obtain ⟨-, hxW, -, hφ', -⟩ := (U.exists_defining x hx).choose_spec.choose_spec
  have hne : gradient (U.exists_defining x hx).choose_spec.choose x ≠ 0 := fun h =>
    hφ' x hxW (by rw [← toDual_gradient (𝕜 := ℝ), h, map_zero])
  rw [outwardNormal, dif_pos hx, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

/-- The outward unit normal is continuous on the frontier. Its zero extension need not be
continuous on the ambient space. -/
theorem continuousOn_outwardNormal (U : SmoothDomain V) :
    ContinuousOn U.outwardNormal (frontier U.carrier) := by
  intro x hx
  obtain ⟨W, φ, hW, hxW, hφ, hφ', hU⟩ := U.exists_defining x hx
  set h : V → V := fun y => ‖gradient φ y‖⁻¹ • gradient φ y
  have hgradcont : Continuous fun y : V => gradient φ y := by
    have hfd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
    exact (InnerProductSpace.toDual ℝ V).symm.continuous.comp hfd
  have hgradne : gradient φ x ≠ 0 := fun hzero =>
    hφ' x hxW (by rw [← toDual_gradient (𝕜 := ℝ), hzero, map_zero])
  have hcont : ContinuousAt h x :=
    ContinuousAt.smul ((hgradcont.continuousAt.norm).inv₀ (norm_ne_zero_iff.mpr hgradne))
      hgradcont.continuousAt
  have heq : ∀ y ∈ frontier U.carrier ∩ W, U.outwardNormal y = h y := by
    rintro y ⟨hy1, hy2⟩
    exact U.outwardNormal_eq hy1 hW hy2 hφ hφ' hU
  refine ContinuousWithinAt.congr_of_eventuallyEq hcont.continuousWithinAt ?_ (heq x ⟨hx, hxW⟩)
  filter_upwards [Filter.inter_mem self_mem_nhdsWithin
    (nhdsWithin_le_nhds (hW.mem_nhds hxW))] with y hy
  exact heq y ⟨hy.1, hy.2⟩

end Normal

section NormalMeasurability

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V]

open Classical in
/-- The outward unit normal, extended by zero off the closed frontier, is Borel measurable. -/
theorem measurable_outwardNormal (U : SmoothDomain V) :
    Measurable U.outwardNormal := by
  have hpw : U.outwardNormal
      = (frontier U.carrier).piecewise U.outwardNormal (fun _ => (0 : V)) := by
    funext x
    by_cases hx : x ∈ frontier U.carrier
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx, outwardNormal, dif_neg hx]
  rw [hpw]
  exact U.continuousOn_outwardNormal.measurable_piecewise continuousOn_const
    isClosed_frontier.measurableSet

end NormalMeasurability

/-! ### The tangent hyperplane at a frontier point -/

section Tangent

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The tangent hyperplane of a smooth domain at a frontier point: the orthogonal complement of
the outward unit normal.  Away from the frontier `outwardNormal` is zero and this is the whole
space, which no statement below uses. -/
def tangentSpace (U : SmoothDomain V) (x₀ : V) : Submodule ℝ V := (ℝ ∙ U.outwardNormal x₀)ᗮ

/-- The natural isometric embedding of the tangent hyperplane into the ambient space. -/
def tangentEmbedding (U : SmoothDomain V) (x₀ : V) : (U.tangentSpace x₀) →ₗᵢ[ℝ] V :=
  (U.tangentSpace x₀).subtypeₗᵢ

@[simp] theorem tangentEmbedding_apply (U : SmoothDomain V) (x₀ : V) (y : U.tangentSpace x₀) :
    U.tangentEmbedding x₀ y = (y : V) := rfl

/-- The tangential coordinate of a point relative to the base point: the inverse of the graph
parametrization of a boundary chart. -/
def tangentCoord [FiniteDimensional ℝ V] (U : SmoothDomain V) (x₀ : V) (x : V) :
    U.tangentSpace x₀ :=
  Analysis.graphCoord (U.tangentEmbedding x₀) x₀ x

theorem inner_outwardNormal_tangent (U : SmoothDomain V) (x₀ : V) (y : U.tangentSpace x₀) :
    (⟪U.outwardNormal x₀, (y : V)⟫ : ℝ) = 0 := by
  have h := (Submodule.mem_orthogonal _ _).mp y.2 (U.outwardNormal x₀)
    (Submodule.mem_span_singleton_self _)
  exact h

/-- At a frontier point the outward normal and the tangent hyperplane split the ambient space
orthogonally, which is the hypothesis of the graph geometry of `Analysis/Graph/Implicit.lean`.
This is `Analysis.isGraphSplitting_orthogonal` for the unit vector `outwardNormal x₀`. -/
theorem isGraphSplitting_tangent [FiniteDimensional ℝ V] (U : SmoothDomain V) {x₀ : V}
    (hx₀ : x₀ ∈ frontier U.carrier) :
    Analysis.IsGraphSplitting (U.tangentEmbedding x₀) (U.outwardNormal x₀) :=
  Analysis.isGraphSplitting_orthogonal (U.norm_outwardNormal hx₀)

theorem finrank_tangentSpace [FiniteDimensional ℝ V] (U : SmoothDomain V) {x₀ : V}
    (hx₀ : x₀ ∈ frontier U.carrier) :
    Module.finrank ℝ (U.tangentSpace x₀) = Module.finrank ℝ V - 1 := by
  have hne : U.outwardNormal x₀ ≠ 0 := by
    intro hzero
    have := U.norm_outwardNormal hx₀
    rw [hzero, norm_zero] at this
    exact zero_ne_one this
  have h := Submodule.finrank_add_finrank_orthogonal
    (K := (ℝ ∙ U.outwardNormal x₀ : Submodule ℝ V))
  rw [finrank_span_singleton hne] at h
  rw [tangentSpace]
  omega

end Tangent

/-! ### The local boundary chart -/

section Chart

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- A **local `C^∞` graph chart of the boundary** of a smooth domain at a frontier point `x₀`.

Write `ν = U.outwardNormal x₀`, `ι` for the isometric embedding of the tangent hyperplane
`(ℝ ∙ ν)ᗮ`, `Ψ y = x₀ + ι y + g y • ν` for the graph parametrization
(`Analysis.graphChartMap`) and `Cyl` for the open cylinder
`{x | graphProj ι (x - x₀) ∈ param ∧ |⟪ν, x - x₀⟫| < depth}` (`Analysis.graphCylinder`).

The three substantive fields are **equalities of sets**, not inclusions:

* `frontier_inter_cylinder`: `∂U ∩ Cyl = Ψ '' param`, so the boundary piece *is* the graph;
* `carrier_inter_cylinder`: `U ∩ Cyl` is exactly the part of the cylinder strictly below the
  graph, which is the side convention;
* `outwardNormal_graph`: along the graph the outward unit normal is
  `(ι (-∇g y) + ν) / √(1 + ‖∇g y‖²)`, with the sign fixed, not only up to `±`.

The height function is globally `C^∞`, so the area formula
`Analysis.hausdorffNormalized_image_graphChartMap` applies to it without any further extension
step; `param` is the parameter set of this single chart, never the whole boundary. -/
structure BoundaryChart (U : SmoothDomain V) (x₀ : V) where
  /-- The height function of the boundary graph, globally `C^∞`. -/
  height : U.tangentSpace x₀ → ℝ
  /-- The open tangential parameter neighbourhood of the origin. -/
  param : Set (U.tangentSpace x₀)
  /-- The half-height of the chart cylinder. -/
  depth : ℝ
  /-- The height function is `C^∞` on the whole tangent hyperplane. -/
  contDiff_height : ContDiff ℝ ∞ height
  /-- The parameter neighbourhood is open. -/
  isOpen_param : IsOpen param
  /-- The chart is centred at `x₀`. -/
  zero_mem_param : (0 : U.tangentSpace x₀) ∈ param
  /-- The graph passes through `x₀`. -/
  height_zero : height 0 = 0
  /-- The cylinder is nondegenerate. -/
  depth_pos : 0 < depth
  /-- The graph stays strictly inside the cylinder. -/
  abs_height_lt : ∀ y ∈ param, |height y| < depth
  /-- The frontier meets the cylinder exactly in the graph. -/
  frontier_inter_cylinder :
    frontier U.carrier
        ∩ Analysis.graphCylinder (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ param depth
      = Analysis.graphChartMap (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ height '' param
  /-- The domain meets the cylinder exactly below the graph. -/
  carrier_inter_cylinder :
    U.carrier
        ∩ Analysis.graphCylinder (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ param depth
      = {x ∈ Analysis.graphCylinder (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ param depth |
          Analysis.graphHeight (U.outwardNormal x₀) x₀ x
            < height (Analysis.graphCoord (U.tangentEmbedding x₀) x₀ x)}
  /-- The outward unit normal along the graph, in graph coordinates. -/
  outwardNormal_graph : ∀ y ∈ param,
    U.outwardNormal
        (Analysis.graphChartMap (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ height y)
      = (Analysis.graphJacobian (gradient height y))⁻¹ •
          (U.tangentEmbedding x₀ (-(gradient height y)) + U.outwardNormal x₀)

namespace BoundaryChart

variable {U : SmoothDomain V} {x₀ : V} (C : BoundaryChart U x₀)

/-- The cylinder of the chart. -/
def cylinder : Set V :=
  Analysis.graphCylinder (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ C.param C.depth

/-- The graph parametrization of the chart. -/
def map : U.tangentSpace x₀ → V :=
  Analysis.graphChartMap (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ C.height

theorem map_apply (y : U.tangentSpace x₀) :
    C.map y = x₀ + (y : V) + C.height y • U.outwardNormal x₀ :=
  Analysis.graphChartMap_apply _ _ _ _ y

theorem isOpen_cylinder : IsOpen C.cylinder :=
  Analysis.isOpen_graphCylinder _ _ _ C.isOpen_param _

theorem tangentCoord_map (hx₀ : x₀ ∈ frontier U.carrier) (y : U.tangentSpace x₀) :
    U.tangentCoord x₀ (C.map y) = y := by
  show Analysis.graphCoord (U.tangentEmbedding x₀) x₀
    (Analysis.graphChartMap (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ C.height y) = y
  exact Analysis.graphCoord_graphChartMap (U.isGraphSplitting_tangent hx₀) x₀ C.height y

theorem injective_map (hx₀ : x₀ ∈ frontier U.carrier) : Function.Injective C.map :=
  Analysis.graphChartMap_injective (U.isGraphSplitting_tangent hx₀) x₀ C.height

/-- The centre of the chart lies in its own cylinder: the tangential coordinate of `x₀` is `0`,
which is in `param`, and its height is `0`, which is below `depth`. -/
theorem self_mem_cylinder : x₀ ∈ C.cylinder := by
  refine ⟨?_, ?_⟩
  · show Analysis.graphCoord (U.tangentEmbedding x₀) x₀ x₀ ∈ C.param
    simpa [Analysis.graphCoord] using C.zero_mem_param
  · show |Analysis.graphHeight (U.outwardNormal x₀) x₀ x₀| < C.depth
    simpa [Analysis.graphHeight] using C.depth_pos

/-- A parameter piece maps onto the corresponding boundary piece. -/
theorem image_subset_frontier {s : Set (U.tangentSpace x₀)} (hs : s ⊆ C.param) :
    C.map '' s ⊆ frontier U.carrier ∩ C.cylinder := by
  rw [BoundaryChart.cylinder, C.frontier_inter_cylinder]
  exact Set.image_mono hs

end BoundaryChart

/-- **Every frontier point of a smooth domain has a local `C^∞` graph chart.**

The chart is produced from one local defining function `φ` by `Analysis.exists_graphRepr`: the
outward normal at `x₀` is the normalized gradient of `φ` there (`outwardNormal_eq`), so
`gradient φ x₀ = ‖gradient φ x₀‖ • ν` with a positive factor, and the cylinder is chosen inside the
defining neighbourhood `W`, where `frontier U ∩ W = {φ = 0} ∩ W` and `U ∩ W = {φ < 0} ∩ W`.  The
chart statements are therefore about `U` itself, not about `φ`, and do not depend on which defining
function was chosen.

No global hypothesis is added: `U` need not be bounded, its frontier may have infinite total
surface measure, and nothing is assumed about `dim V` — a subsingleton space simply has no frontier
point to feed this theorem. -/
theorem exists_boundaryChart (U : SmoothDomain V) {x₀ : V} (hx₀ : x₀ ∈ frontier U.carrier) :
    Nonempty (U.BoundaryChart x₀) := by
  obtain ⟨W, φ, hWopen, hx₀W, hφ, hφ', hUW⟩ := U.exists_defining x₀ hx₀
  have hsp := U.isGraphSplitting_tangent hx₀
  have hfr := U.frontier_inter_eq hWopen hφ hφ' hUW
  have hφ0 : φ x₀ = 0 := by
    have hmem : x₀ ∈ {y ∈ W | φ y = 0} := by rw [← hfr]; exact ⟨hx₀, hx₀W⟩
    exact hmem.2
  have hgradne : gradient φ x₀ ≠ 0 := fun h =>
    hφ' x₀ hx₀W (by rw [← toDual_gradient (𝕜 := ℝ), h, map_zero])
  have hc : 0 < ‖gradient φ x₀‖ := norm_pos_iff.mpr hgradne
  have hgrad : gradient φ x₀ = ‖gradient φ x₀‖ • U.outwardNormal x₀ := by
    rw [U.outwardNormal_eq hx₀ hWopen hx₀W hφ hφ' hUW, smul_smul, mul_inv_cancel₀ hc.ne',
      one_smul]
  obtain ⟨G, hGsub⟩ := Analysis.exists_graphRepr (U.tangentEmbedding x₀) hsp hφ hφ0 hc hgrad
    (hWopen.mem_nhds hx₀W)
  have hfrcyl : ∀ x ∈ G.cylinder, (x ∈ frontier U.carrier ↔ φ x = 0) := by
    intro x hx
    have hxW : x ∈ W := hGsub hx
    constructor
    · intro hxfr
      have : x ∈ {y ∈ W | φ y = 0} := by rw [← hfr]; exact ⟨hxfr, hxW⟩
      exact this.2
    · intro hx0
      have : x ∈ frontier U.carrier ∩ W := by rw [hfr]; exact ⟨hxW, hx0⟩
      exact this.1
  have hUcyl : ∀ x ∈ G.cylinder, (x ∈ U.carrier ↔ φ x < 0) := by
    intro x hx
    have hxW : x ∈ W := hGsub hx
    constructor
    · intro hxU
      have : x ∈ U.carrier ∩ W := ⟨hxU, hxW⟩
      rw [hUW] at this
      exact this.2
    · intro hx0
      have : x ∈ U.carrier ∩ W := by rw [hUW]; exact ⟨hxW, hx0⟩
      exact this.1
  have hfront : frontier U.carrier ∩ G.cylinder = G.map '' G.param := by
    rw [← G.zeroSet_inter_cylinder hsp]
    ext x
    exact ⟨fun hx => ⟨(hfrcyl x hx.2).mp hx.1, hx.2⟩, fun hx => ⟨(hfrcyl x hx.2).mpr hx.1, hx.2⟩⟩
  have hcarrier : U.carrier ∩ G.cylinder
      = {x ∈ G.cylinder | Analysis.graphHeight (U.outwardNormal x₀) x₀ x
          < G.height (Analysis.graphCoord (U.tangentEmbedding x₀) x₀ x)} := by
    rw [← G.sublevel_inter_cylinder]
    ext x
    exact ⟨fun hx => ⟨(hUcyl x hx.2).mp hx.1, hx.2⟩, fun hx => ⟨(hUcyl x hx.2).mpr hx.1, hx.2⟩⟩
  refine ⟨{ height := G.height
            param := G.param
            depth := G.depth
            contDiff_height := G.contDiff_height
            isOpen_param := G.isOpen_param
            zero_mem_param := G.zero_mem_param
            height_zero := G.height_zero
            depth_pos := G.depth_pos
            abs_height_lt := G.abs_height_lt
            frontier_inter_cylinder := hfront
            carrier_inter_cylinder := hcarrier
            outwardNormal_graph := ?_ }⟩
  intro y hy
  have hmemfr : G.map y ∈ frontier U.carrier := by
    have : G.map y ∈ frontier U.carrier ∩ G.cylinder := by
      rw [hfront]; exact ⟨y, hy, rfl⟩
    exact this.1
  have hmemW : G.map y ∈ W := hGsub (G.map_mem_cylinder hsp hy)
  rw [show Analysis.graphChartMap (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ G.height y
      = G.map y from rfl,
    U.outwardNormal_eq hmemfr hWopen hmemW hφ hφ' hUW]
  exact G.normalized_gradient_map hsp (hφ.differentiable (by simp)) hy

end Chart

/-! ### The surface measure of a boundary piece -/

section Area

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- **The normalized surface measure of a boundary piece, in chart coordinates.**  For a
measurable parameter set `s` the `(n-1)`-dimensional surface measure of the graph piece `Ψ '' s`
is `∫_s √(1 + ‖∇g‖²)` against Lebesgue measure of the tangent hyperplane, `n = finrank ℝ V`.

This is `Analysis.hausdorffNormalized_image_graphChartMap` together with
`finrank (tangentSpace) = n - 1`; the height function of a `BoundaryChart` is globally `C^∞`, so
no extension step is needed here. -/
theorem BoundaryChart.surfaceMeasure_image {U : SmoothDomain V} {x₀ : V}
    (hx₀ : x₀ ∈ frontier U.carrier) (C : U.BoundaryChart x₀)
    {s : Set (U.tangentSpace x₀)} (hs : MeasurableSet s) :
    surfaceMeasure V (C.map '' s)
      = ∫⁻ y in s, ENNReal.ofReal (Analysis.graphJacobian (gradient C.height y))
          ∂(volume : Measure (U.tangentSpace x₀)) := by
  rw [surfaceMeasure, ← U.finrank_tangentSpace hx₀]
  exact Analysis.hausdorffNormalized_image_graphChartMap _ (U.norm_outwardNormal hx₀)
    (fun v => (U.isGraphSplitting_tangent hx₀).perp v) x₀
    (C.contDiff_height.of_le (by simp)) hs

/-- **The surface measure of the whole boundary piece of one chart.**  The frontier piece cut out
by the chart cylinder — which is exactly the graph over the chart's parameter set, not the whole
boundary — has surface measure `∫_{param} √(1 + ‖∇g‖²)`. -/
theorem BoundaryChart.surfaceMeasure_frontier_inter_cylinder {U : SmoothDomain V} {x₀ : V}
    (hx₀ : x₀ ∈ frontier U.carrier) (C : U.BoundaryChart x₀) :
    surfaceMeasure V (frontier U.carrier ∩ C.cylinder)
      = ∫⁻ y in C.param, ENNReal.ofReal (Analysis.graphJacobian (gradient C.height y))
          ∂(volume : Measure (U.tangentSpace x₀)) := by
  rw [BoundaryChart.cylinder, C.frontier_inter_cylinder,
    show Analysis.graphChartMap (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ C.height
      = C.map from rfl]
  exact BoundaryChart.surfaceMeasure_image hx₀ C C.isOpen_param.measurableSet

end Area

end KLS.SmoothDomain

end FunctionalInequalities

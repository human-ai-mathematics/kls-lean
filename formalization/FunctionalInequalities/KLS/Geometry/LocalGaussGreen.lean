import FunctionalInequalities.KLS.Geometry.BoundaryChart
import FunctionalInequalities.Analysis.SubgraphDivergence
import FunctionalInequalities.Analysis.GraphIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Gauss–Green for a vector field supported in one boundary chart

Application layer: the subgraph divergence formula of `Analysis/SubgraphDivergence.lean` and the
weighted boundary change of variables of `Analysis/GraphIntegral.lean`, connected to the local
`C^∞` boundary chart of `KLS/Geometry/BoundaryChart.lean`.  Every statement here is proved and
uses only the standard axioms; the module contains **no** `sorry`.

## What is proved, and what is not

`BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`: for a smooth domain `U`, a
frontier point `x₀`, a boundary chart `C` at `x₀` and a compactly supported `C¹` vector field `F`
**whose support lies in the chart cylinder**, `tsupport F ⊆ C.cylinder`,

  `∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n-1}`.

This is the *local* identity.  It is **not** the Gauss–Green theorem for an arbitrary compactly
supported field: that needs in addition a finite smooth partition of unity subordinate to a cover
of the support, which this module does not provide.  The gluing is done one level up, in
`KLS/Geometry/GaussGreen.lean`, where this identity supplies the boundary blocks of the cover and
the interior and exterior blocks are handled separately; the global theorem there is proved and
no longer a `sorry`.

## The two localizations

`tsupport F ⊆ C.cylinder` is the exact hypothesis that makes both sides local: outside the
cylinder `F` vanishes on a neighbourhood, hence so does its derivative, so *both* `F` and
`div F` vanish there (`BoundaryChart.eq_zero_of_notMem_cylinder`).  Consequently

* `integral_divergence_carrier`: the indicator of `U.carrier` and the indicator of the *global*
  subgraph `{x | graphHeight ν x₀ x < height (graphCoord ι x₀ x)}` of the chart's height function
  agree against `div F`.  The two sets are **not** equal — outside the cylinder the globally
  extended graph has nothing to do with `∂U` — they agree only inside the cylinder, which is where
  `div F` lives.  The subgraph formula then evaluates the integral.
* `integral_inner_outwardNormal_frontier`: the flux integrand vanishes off `C.map '' C.param`, so
  the boundary integral is the integral over that single graph piece; the weighted change of
  variables turns it into a parameter integral with the factor `√(1 + ‖∇g‖²)`, which cancels
  exactly against the denominator of `outwardNormal_graph`.  The integrand is then extended from
  `C.param` back to the whole tangent hyperplane because `y ∉ C.param` forces `C.map y` out of the
  cylinder (`BoundaryChart.map_notMem_cylinder`).

Boundary-side integrability is never assumed: the change of variables of
`Analysis/GraphIntegral.lean` needs only measurability, and the restriction steps are equalities of
indicator functions, so nothing here supposes that `∂U` has finite total surface measure.  The
domain is not assumed bounded and `V` is not assumed nontrivial.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FunctionalInequalities

universe u

namespace KLS.SmoothDomain

section Local

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

namespace BoundaryChart

variable {U : SmoothDomain V} {x₀ : V}

omit [MeasurableSpace V] [BorelSpace V] in
/-- Outside the chart cylinder a field supported in the cylinder, and its divergence, vanish. -/
theorem eq_zero_of_notMem_cylinder (C : U.BoundaryChart x₀) {F : V → V}
    (hsupp : tsupport F ⊆ C.cylinder) {x : V} (hx : x ∉ C.cylinder) :
    F x = 0 ∧ Analysis.divergence F x = 0 := by
  have hx' : x ∉ tsupport F := fun h => hx (hsupp h)
  refine ⟨image_eq_zero_of_notMem_tsupport hx', ?_⟩
  rw [Analysis.divergence, Analysis.fderiv_eq_zero_of_notMem_tsupport hx']
  simp

omit [MeasurableSpace V] [BorelSpace V] in
/-- A parameter outside the chart's parameter set maps out of the cylinder. -/
theorem map_notMem_cylinder (hx₀ : x₀ ∈ frontier U.carrier) (C : U.BoundaryChart x₀)
    {y : U.tangentSpace x₀} (hy : y ∉ C.param) : C.map y ∉ C.cylinder := by
  intro hmem
  exact hy (by rw [← C.tangentCoord_map hx₀ y]; exact hmem.1)

/-- **Localization of the volume integral.**  For a field supported in the chart cylinder the
integral of the divergence over the domain is the integral over the *global* subgraph of the
chart's height function, and the subgraph divergence formula evaluates it. -/
theorem integral_divergence_carrier (hx₀ : x₀ ∈ frontier U.carrier) (C : U.BoundaryChart x₀)
    {F : V → V} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (hsupp : tsupport F ⊆ C.cylinder) :
    ∫ x in U.carrier, Analysis.divergence F x
      = ∫ y : U.tangentSpace x₀, (⟪F (C.map y),
          U.tangentEmbedding x₀ (-(gradient C.height y)) + U.outwardNormal x₀⟫ : ℝ) := by
  have hsp := U.isGraphSplitting_tangent hx₀
  have hheight : ContDiff ℝ 1 C.height := C.contDiff_height.of_le (by simp)
  set ι := U.tangentEmbedding x₀ with hι
  set ν := U.outwardNormal x₀ with hν
  set S : Set V :=
    {x : V | Analysis.graphHeight ν x₀ x < C.height (Analysis.graphCoord ι x₀ x)} with hS
  have hSopen : IsOpen S := by
    have h1 : Continuous fun x : V => Analysis.graphHeight ν x₀ x :=
      (innerSL ℝ ν).continuous.comp (continuous_id.sub continuous_const)
    have h2 : Continuous fun x : V => Analysis.graphCoord ι x₀ x :=
      (Analysis.graphProj ι).continuous.comp (continuous_id.sub continuous_const)
    exact isOpen_lt h1 (hheight.continuous.comp h2)
  have hind : ∀ x : V, U.carrier.indicator (Analysis.divergence F) x
      = S.indicator (Analysis.divergence F) x := by
    intro x
    by_cases hx : x ∈ C.cylinder
    · have hcyl : U.carrier ∩ C.cylinder = {x ∈ C.cylinder | x ∈ S} := C.carrier_inter_cylinder
      have hiff : x ∈ U.carrier ↔ x ∈ S := by
        constructor
        · intro hxU
          have hmem : x ∈ U.carrier ∩ C.cylinder := ⟨hxU, hx⟩
          rw [hcyl] at hmem
          exact hmem.2
        · intro hxS
          have hmem : x ∈ {x ∈ C.cylinder | x ∈ S} := ⟨hx, hxS⟩
          rw [← hcyl] at hmem
          exact hmem.1
      by_cases h : x ∈ U.carrier
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem fun hs => h (hiff.mpr hs)]
    · have hzero := (C.eq_zero_of_notMem_cylinder hsupp hx).2
      simp [Set.indicator_apply, hzero]
  calc ∫ x in U.carrier, Analysis.divergence F x
      = ∫ x, U.carrier.indicator (Analysis.divergence F) x ∂(volume : Measure V) :=
        (integral_indicator U.isOpen.measurableSet).symm
    _ = ∫ x, S.indicator (Analysis.divergence F) x ∂(volume : Measure V) :=
        integral_congr_ae (Eventually.of_forall hind)
    _ = ∫ x in S, Analysis.divergence F x := integral_indicator hSopen.measurableSet
    _ = _ := Analysis.integral_divergence_subgraph hsp x₀ hheight hF hFc

/-- **Localization of the boundary integral.**  For a field supported in the chart cylinder the
flux through the frontier is the flux through the single graph piece the chart covers, and the
weighted change of variables of `Analysis/GraphIntegral.lean` together with the chart's normal
formula cancels the graph Jacobian exactly. -/
theorem integral_inner_outwardNormal_frontier (hx₀ : x₀ ∈ frontier U.carrier)
    (C : U.BoundaryChart x₀) {F : V → V} (hF : ContDiff ℝ 1 F)
    (hsupp : tsupport F ⊆ C.cylinder) :
    ∫ x in frontier U.carrier, (⟪F x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V)
      = ∫ y : U.tangentSpace x₀, (⟪F (C.map y),
          U.tangentEmbedding x₀ (-(gradient C.height y)) + U.outwardNormal x₀⟫ : ℝ) := by
  have hsp := U.isGraphSplitting_tangent hx₀
  have hheight : ContDiff ℝ 1 C.height := C.contDiff_height.of_le (by simp)
  have hmapeq : C.map
      = Analysis.graphChartMap (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀ C.height := rfl
  have hmeas : Measurable fun x : V => (⟪F x, U.outwardNormal x⟫ : ℝ) :=
    Measurable.inner (𝕜 := ℝ) hF.continuous.measurable U.measurable_outwardNormal
  -- the boundary integral only sees the graph piece of the chart
  have hind : ∀ x : V, (frontier U.carrier).indicator
        (fun x : V => (⟪F x, U.outwardNormal x⟫ : ℝ)) x
      = (C.map '' C.param).indicator (fun x : V => (⟪F x, U.outwardNormal x⟫ : ℝ)) x := by
    intro x
    by_cases hximg : x ∈ C.map '' C.param
    · rw [Set.indicator_of_mem hximg,
        Set.indicator_of_mem (C.image_subset_frontier (subset_refl C.param) hximg).1]
    · rw [Set.indicator_of_notMem hximg]
      by_cases hxfr : x ∈ frontier U.carrier
      · have hxcyl : x ∉ C.cylinder := by
          intro hc
          refine hximg ?_
          have hmem : x ∈ frontier U.carrier ∩ C.cylinder := ⟨hxfr, hc⟩
          rw [BoundaryChart.cylinder, C.frontier_inter_cylinder] at hmem
          exact hmem
        rw [Set.indicator_of_mem hxfr]
        show (⟪F x, U.outwardNormal x⟫ : ℝ) = 0
        rw [(C.eq_zero_of_notMem_cylinder hsupp hxcyl).1, inner_zero_left]
      · rw [Set.indicator_of_notMem hxfr]
  have hfrmeas : MeasurableSet (frontier U.carrier) := isClosed_frontier.measurableSet
  have himgmeas : MeasurableSet (C.map '' C.param) := by
    rw [hmapeq]
    exact Analysis.measurableSet_image_graphChartMap (U.tangentEmbedding x₀) hsp.perp x₀
      hheight.continuous C.isOpen_param.measurableSet
  have hstep1 : ∫ x in frontier U.carrier, (⟪F x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V)
      = ∫ x in C.map '' C.param, (⟪F x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V) := by
    rw [← integral_indicator hfrmeas, ← integral_indicator himgmeas]
    exact integral_congr_ae (Eventually.of_forall hind)
  -- the weighted change of variables, with the Jacobian cancelled by the normal formula
  have hstep2 : ∫ x in C.map '' C.param, (⟪F x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V)
      = ∫ y in C.param, (⟪F (C.map y),
          U.tangentEmbedding x₀ (-(gradient C.height y)) + U.outwardNormal x₀⟫ : ℝ)
          ∂(volume : Measure (U.tangentSpace x₀)) := by
    rw [surfaceMeasure, ← U.finrank_tangentSpace hx₀, hmapeq,
      Analysis.setIntegral_image_graphChartMap (U.tangentEmbedding x₀)
        (U.norm_outwardNormal hx₀) hsp.perp x₀ hheight C.isOpen_param.measurableSet
        hmeas.aestronglyMeasurable]
    refine setIntegral_congr_fun C.isOpen_param.measurableSet fun y hy => ?_
    have hJ : Analysis.graphJacobian (gradient C.height y) ≠ 0 :=
      (Analysis.graphJacobian_pos _).ne'
    show Analysis.graphJacobian (gradient C.height y)
        • (⟪F (Analysis.graphChartMap (U.tangentEmbedding x₀) (U.outwardNormal x₀) x₀
              C.height y),
            U.outwardNormal (Analysis.graphChartMap (U.tangentEmbedding x₀)
              (U.outwardNormal x₀) x₀ C.height y)⟫ : ℝ)
      = (⟪F (C.map y),
          U.tangentEmbedding x₀ (-(gradient C.height y)) + U.outwardNormal x₀⟫ : ℝ)
    rw [C.outwardNormal_graph y hy, real_inner_smul_right, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hJ, one_mul, ← hmapeq]
  -- the integrand vanishes outside the parameter set
  have hstep3 : ∫ y in C.param, (⟪F (C.map y),
          U.tangentEmbedding x₀ (-(gradient C.height y)) + U.outwardNormal x₀⟫ : ℝ)
        ∂(volume : Measure (U.tangentSpace x₀))
      = ∫ y : U.tangentSpace x₀, (⟪F (C.map y),
          U.tangentEmbedding x₀ (-(gradient C.height y)) + U.outwardNormal x₀⟫ : ℝ) := by
    rw [← integral_indicator C.isOpen_param.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ C.param
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      show (0 : ℝ) = (⟪F (C.map y),
        U.tangentEmbedding x₀ (-(gradient C.height y)) + U.outwardNormal x₀⟫ : ℝ)
      rw [(C.eq_zero_of_notMem_cylinder hsupp (C.map_notMem_cylinder hx₀ hy)).1,
        inner_zero_left]
  rw [hstep1, hstep2, hstep3]

/-- **Gauss–Green for a vector field supported in one boundary chart.**  This is the *local*
identity: the hypothesis `tsupport F ⊆ C.cylinder` confines the field, and therefore its
derivative, to the single chart.  It is not the global theorem for an arbitrary compactly
supported field, which additionally needs a finite smooth partition of unity; that gluing is
`KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` in
`KLS/Geometry/GaussGreen.lean`. -/
theorem integral_divergence_eq_integral_inner_outwardNormal (hx₀ : x₀ ∈ frontier U.carrier)
    (C : U.BoundaryChart x₀) {F : V → V} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (hsupp : tsupport F ⊆ C.cylinder) :
    ∫ x in U.carrier, Analysis.divergence F x
      = ∫ x in frontier U.carrier, (⟪F x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V) := by
  rw [C.integral_divergence_carrier hx₀ hF hFc hsupp,
    C.integral_inner_outwardNormal_frontier hx₀ hF hsupp]

end BoundaryChart

end Local

end KLS.SmoothDomain

end FunctionalInequalities

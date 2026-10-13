import FunctionalInequalities.Analysis.Convex.Subgradient
import Mathlib

/-!
# Alexandrov identity in push-forward form

If `(∇u)_# ν = μ` with `ν, μ ≪ volume` for a convex Lipschitz `u`, the subgradient image of a set has `μ`-measure
equal to the `ν`-measure of the set (route node N5 of the weak moment-map route to Letwin arXiv:2607.24164v1), and the
farthest-point exposure lemma for the Caffarelli block. Proof bodies: GPT (Letwin sub-controller tasks L-T14b, L-T11c1);
statements by the Letwin sub-controller; placement: Claude.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace FunctionalInequalities.Analysis

private lemma alexandrov_gradient_support {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : E → ℝ} (hc : ConvexOn ℝ univ u)
    {x : E} (hx : DifferentiableAt ℝ u x) (y : E) :
    u x + ⟪gradient u x, y - x⟫ ≤ u y := by
  have hd :
      HasFDerivAt u ((InnerProductSpace.toDual ℝ E) (gradient u x))
        ((AffineMap.lineMap (k := ℝ) x y) (0 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero] using hx.hasGradientAt.hasFDerivAt
  have hl :
      HasDerivAt (u ∘ ⇑(AffineMap.lineMap (k := ℝ) x y))
        ⟪gradient u x, y - x⟫ (0 : ℝ) := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      hd.comp_hasDerivAt 0
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have hcl :
      ConvexOn ℝ univ (u ∘ ⇑(AffineMap.lineMap (k := ℝ) x y)) := by
    simpa only [preimage_univ] using
      ConvexOn.comp_affineMap (AffineMap.lineMap (k := ℝ) x y) hc
  have hle : ⟪gradient u x, y - x⟫ ≤ u y - u x := by
    simpa only [slope_def_field, Function.comp_apply,
      AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, sub_zero, div_one] using
      hcl.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1)
        (zero_lt_one : (0 : ℝ) < 1) hl
  linarith

private lemma alexandrov_isClosed_subgradientImage {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} (hu : Continuous u)
    {S : Set E} (hS : IsCompact S) :
    IsClosed (subgradientImage u S) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let C : Set (S × E) :=
    ⋂ y : E, {q | u q.1.1 + ⟪q.2, y - q.1.1⟫ ≤ u y}
  have hC : IsClosed C := by
    refine isClosed_iInter fun y => ?_
    exact isClosed_le
      ((hu.comp (continuous_subtype_val.comp continuous_fst)).add
        (continuous_snd.inner
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst))))
      continuous_const
  have himage : Prod.snd '' C = subgradientImage u S := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hq, rfl⟩
      refine ⟨x.1, x.2, ?_⟩
      exact mem_iInter.mp hq
    · rintro ⟨x, hx, hp⟩
      refine ⟨(⟨x, hx⟩, p), ?_, rfl⟩
      exact mem_iInter.mpr hp
  rw [← himage]
  exact isClosedMap_snd_of_compactSpace C hC

/-- **Alexandrov identity in push-forward form** (weak Letwin route, step N5): for a convex Lipschitz
`u` with `ν ≪ volume`, `ν.map (gradient u) = μ ≪ volume`, integrals of nonnegative functions over the subgradient
image `∂u(S)` of a compact `S` against `μ` equal integrals over `S` of the composition with `∇u`
against `ν`. -/
theorem lintegral_subgradientImage_eq_of_map_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    {ν μ : Measure E} (hν : ν ≪ (volume : Measure E)) (hmap : ν.map (gradient u) = μ)
    (hac : μ ≪ (volume : Measure E))
    {S : Set E} (hS : IsCompact S) (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p in subgradientImage u S, g p ∂μ = ∫⁻ x in S, g (gradient u x) ∂ν := by
  classical
  have hgrad : Measurable (gradient u) := by
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have hT : MeasurableSet (subgradientImage u S) :=
    (alexandrov_isClosed_subgradientImage hu.continuous hS).measurableSet
  let D : Set E :=
    {p | ∃ x y : E, x ≠ y ∧
      (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧
      (∀ z, u y + ⟪p, z - y⟫ ≤ u z)}
  have hD : μ D = 0 :=
    hac (volume_subgradient_two_points_eq_zero hu hconv)
  have hpre : ν (gradient u ⁻¹' D) = 0 := by
    apply le_antisymm
    · calc
        ν (gradient u ⁻¹' D) ≤ (ν.map (gradient u)) D :=
          Measure.le_map_apply hgrad.aemeasurable D
        _ = μ D := congrArg (fun m : Measure E => m D) hmap
        _ = 0 := hD
    · exact bot_le
  have havoid : ∀ᵐ x ∂ν, gradient u x ∉ D := by
    apply ae_iff.mpr
    apply measure_mono_null (t := gradient u ⁻¹' D) _ hpre
    intro x hx
    exact Classical.not_not.mp hx
  have hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ u x := by
    exact ae_iff.mpr
      (hν (ae_iff.mp (hu.ae_differentiableAt (μ := (volume : Measure E)))))
  have hsets : (gradient u ⁻¹' subgradientImage u S) =ᵐ[ν] S := by
    filter_upwards [hdiff, havoid] with x hx hxD
    change (gradient u x ∈ subgradientImage u S) = (x ∈ S)
    apply propext
    constructor
    · rintro ⟨y, hyS, hy⟩
      by_contra hxS
      have hxy : x ≠ y := by
        intro h
        exact hxS (h.symm ▸ hyS)
      exact hxD ⟨x, y, hxy, alexandrov_gradient_support hconv hx, hy⟩
    · intro hxS
      exact ⟨x, hxS, alexandrov_gradient_support hconv hx⟩
  calc
    ∫⁻ p in subgradientImage u S, g p ∂μ =
        ∫⁻ p in subgradientImage u S, g p ∂(ν.map (gradient u)) := by
          rw [hmap]
    _ = ∫⁻ x in gradient u ⁻¹' subgradientImage u S, g (gradient u x) ∂ν :=
      setLIntegral_map hT hg hgrad
    _ = ∫⁻ x in S, g (gradient u x) ∂ν :=
      setLIntegral_congr hsets

end FunctionalInequalities.Analysis

section LT11C1FarthestPointExposed

open Set
open scoped RealInnerProductSpace

/-! Farthest points are exposed (task L-T11c1). -/

namespace FunctionalInequalities.Analysis

/-- **A farthest point of a compact set is exposed** (weak Letwin route, Caffarelli block T11c/T11e):
for a nonempty compact `C` in an inner product space and any `y`, there is `x_e ∈ C` with
`⟪x − x_e, x_e − y⟫ < 0` for every other `x ∈ C`; moreover `‖x_e − y‖ ≥ ‖x − y‖` for all `x ∈ C`. -/
theorem exists_farthest_point_exposed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} (hC : IsCompact C) (hne : C.Nonempty) (y : E) :
    ∃ xe ∈ C, (∀ x ∈ C, ‖x - y‖ ≤ ‖xe - y‖) ∧ ∀ x ∈ C, x ≠ xe → ⟪x - xe, xe - y⟫ < 0 := by
  have hcont : Continuous (fun x : E => ‖x - y‖) :=
    (continuous_id.sub (continuous_const : Continuous (fun _ : E => y))).norm
  obtain ⟨xe, hxe, hmax⟩ := hC.exists_isMaxOn hne hcont.continuousOn
  have hle : ∀ x ∈ C, ‖x - y‖ ≤ ‖xe - y‖ := by
    intro x hx
    have hm : C ⊆ {z : E | ‖z - y‖ ≤ ‖xe - y‖} :=
      Filter.mem_principal.mp
        (Filter.eventually_iff.mp
          (show ∀ᶠ z in Filter.principal C, ‖z - y‖ ≤ ‖xe - y‖ from hmax))
    exact hm hx
  refine ⟨xe, hxe, hle, ?_⟩
  intro x hx hne
  have hsq : ‖x - y‖ ^ 2 ≤ ‖xe - y‖ ^ 2 :=
    sq_le_sq'
      (le_trans
        (neg_nonpos.mpr (norm_nonneg (xe - y)))
        (norm_nonneg (x - y)))
      (hle x hx)
  have hidentity :
      ‖x - y‖ ^ 2 =
        ‖x - xe‖ ^ 2 + 2 * ⟪x - xe, xe - y⟫ + ‖xe - y‖ ^ 2 := by
    calc
      ‖x - y‖ ^ 2 = ‖(x - xe) + (xe - y)‖ ^ 2 := by
        rw [sub_add_sub_cancel]
      _ = ‖x - xe‖ ^ 2 + 2 * ⟪x - xe, xe - y⟫ + ‖xe - y‖ ^ 2 :=
        norm_add_sq_real (x - xe) (xe - y)
  have hinner : 2 * ⟪x - xe, xe - y⟫ ≤ -‖x - xe‖ ^ 2 := by
    nlinarith [hsq, hidentity]
  have hnormpos : 0 < ‖x - xe‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hspos : 0 < ‖x - xe‖ ^ 2 := sq_pos_of_pos hnormpos
  nlinarith [hinner, hspos]

end FunctionalInequalities.Analysis

end LT11C1FarthestPointExposed

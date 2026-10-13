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

section LT14CLocalAlexandrovBounds

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

/-! Local two-sided Alexandrov bounds (task L-T14c). -/

namespace FunctionalInequalities.Analysis

private lemma isCompact_subgradientImage_local {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) {S : Set E}
    (hS : IsCompact S) :
    IsCompact (subgradientImage u S) := by
  let T : Set (E × E) :=
    (S ×ˢ Metric.closedBall (0 : E) (L : ℝ)) ∩
      ⋂ y : E, {z : E × E | u z.1 + ⟪z.2, y - z.1⟫ ≤ u y}
  have hclosed : IsClosed
      (⋂ y : E, {z : E × E | u z.1 + ⟪z.2, y - z.1⟫ ≤ u y}) := by
    apply isClosed_iInter
    intro y
    have hcont :
        Continuous (fun z : E × E => u z.1 + ⟪z.2, y - z.1⟫) :=
      (hu.continuous.comp continuous_fst).add
        (continuous_snd.inner (continuous_const.sub continuous_fst))
    exact isClosed_Iic.preimage hcont
  have hcompact : IsCompact T := by
    dsimp [T]
    exact (hS.prod (isCompact_closedBall (0 : E) (L : ℝ))).inter_right hclosed
  have hTimage : IsCompact (Prod.snd '' T) :=
    hcompact.image continuous_snd
  have hEq : Prod.snd '' T = subgradientImage u S := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hz, rfl⟩
      rcases hz with ⟨hzprod, hzall⟩
      refine ⟨x, hzprod.1, ?_⟩
      intro y
      exact Set.mem_iInter.mp hzall y
    · rintro ⟨x, hxS, hp⟩
      have hpbound : ‖p‖ ≤ (L : ℝ) := by
        have hnorm := hu.norm_sub_le (x + p) x
        have habs : |u (x + p) - u x| ≤ (L : ℝ) * ‖p‖ := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnorm
        have hup : u (x + p) - u x ≤ (L : ℝ) * ‖p‖ :=
          (le_abs_self _).trans habs
        have hsub : u x + ⟪p, p⟫ ≤ u (x + p) := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp (x + p)
        have hinner : ⟪p, p⟫ = ‖p‖ ^ 2 :=
          real_inner_self_eq_norm_sq p
        rw [hinner] at hsub
        nlinarith [norm_nonneg p, (show (0 : ℝ) ≤ (L : ℝ) by positivity)]
      have hpball : p ∈ Metric.closedBall (0 : E) (L : ℝ) := by
        change dist p 0 ≤ (L : ℝ)
        simpa [dist_eq_norm] using hpbound
      refine ⟨(x, p), ?_, rfl⟩
      refine ⟨⟨hxS, hpball⟩, ?_⟩
      apply Set.mem_iInter.mpr
      intro y
      exact hp y
  rw [← hEq]
  exact hTimage

/-- **Local two-sided Alexandrov bounds** (weak Letwin route, step N5, input of the Caffarelli
argument N6): if `u` is convex and Lipschitz, `ν = e^{-u} dx` (normalized), `ν.map ∇u = μ` has a
density `ρ` bounded above and below on a closed convex `K` containing `∇u` a.e., then on every compact
`Q` the volume of the subgradient image is comparable to the volume of the set:
`a · vol S ≤ vol (∂u(S)) ≤ b · vol S` for all compact `S ⊆ Q`, with `0 < a`. -/
theorem exists_local_subgradientImage_volume_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {μ : Measure E} (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) = μ)
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) (hμ : μ = (volume : Measure E).withDensity ρ)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K)
    {c C : ℝ} (hc : 0 < c) (hρK : ∀ p ∈ K, ENNReal.ofReal c ≤ ρ p ∧ ρ p ≤ ENNReal.ofReal C)
    {Q : Set E} (hQ : IsCompact Q) :
    ∃ a b : ℝ, 0 < a ∧ ∀ S : Set E, IsCompact S → S ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) S ≤ (volume : Measure E) (subgradientImage u S) ∧
      (volume : Measure E) (subgradientImage u S) ≤ ENNReal.ofReal b * (volume : Measure E) S := by
  have _hρ : Measurable ρ := hρ
  let ν : Measure E := (volume : Measure E).tilted (-u)
  have hν : ν ≪ (volume : Measure E) := by
    dsimp [ν, Measure.tilted]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have hμac : μ ≪ (volume : Measure E) := by
    rw [hμ]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have hν_eq :
      ν = (volume : Measure E).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-u x))) := by
    dsimp [ν, Measure.tilted]
    rw [hnorm]
    simp
  by_cases hQne : Q.Nonempty
  · obtain ⟨xm, hxmQ, hxm⟩ :=
      hQ.exists_isMaxOn hQne hu.continuous.continuousOn
    obtain ⟨xn, hxnQ, hxn⟩ :=
      hQ.exists_isMinOn hQne hu.continuous.continuousOn
    let m : ℝ := u xm
    let n : ℝ := u xn
    let C' : ℝ := max C 1
    let a : ℝ := Real.exp (-m) / C'
    let b : ℝ := Real.exp (-n) / c
    have hC'pos : 0 < C' := by
      dsimp [C']
      exact lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    refine ⟨a, b, ha, ?_⟩
    intro S hS hSQ
    have hSmeas : MeasurableSet S := hS.measurableSet
    have hIcompact : IsCompact (subgradientImage u S) :=
      isCompact_subgradientImage_local hu hS
    have hImeas : MeasurableSet (subgradientImage u S) :=
      hIcompact.measurableSet
    have hνS :
        ν S = ∫⁻ x in S, ENNReal.ofReal (Real.exp (-u x)) := by
      rw [hν_eq]
      exact MeasureTheory.withDensity_apply _ hSmeas
    have hident :
        ∫⁻ p in subgradientImage u S, (1 : ℝ≥0∞) ∂μ =
          ∫⁻ x in S, (1 : ℝ≥0∞) ∂ν :=
      lintegral_subgradientImage_eq_of_map_gradient hu hconv hν
        (by simpa [ν] using hmap) hμac hS 1 measurable_const
    have hμS : μ (subgradientImage u S) = ν S := by
      simpa [MeasureTheory.lintegral_one,
        MeasureTheory.Measure.restrict_apply_univ] using hident
    have hsubK : subgradientImage u S ⊆ K := by
      intro p hp
      rcases hp with ⟨x, hxS, hp⟩
      exact subgradient_mem_of_ae_gradient_mem hu hconv hK hKc hae hp
    have hlowerν :
        ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S ≤ ν S := by
      rw [hνS]
      calc
        ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S =
            ∫⁻ x in S, ENNReal.ofReal (Real.exp (-m)) :=
          (MeasureTheory.setLIntegral_const S _).symm
        _ ≤ ∫⁻ x in S, ENNReal.ofReal (Real.exp (-u x)) := by
          apply MeasureTheory.setLIntegral_mono' hSmeas
          intro x hx
          have hxu : u x ≤ m := hxm (hSQ hx)
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hxu))
    have hupperν :
        ν S ≤ ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) S := by
      rw [hνS]
      calc
        ∫⁻ x in S, ENNReal.ofReal (Real.exp (-u x))
            ≤ ∫⁻ x in S, ENNReal.ofReal (Real.exp (-n)) := by
              apply MeasureTheory.setLIntegral_mono' hSmeas
              intro x hx
              have hxu : n ≤ u x := hxn (hSQ hx)
              exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hxu))
        _ = ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) S :=
          MeasureTheory.setLIntegral_const S _
    have hμlower :
        ENNReal.ofReal c * (volume : Measure E) (subgradientImage u S) ≤
          μ (subgradientImage u S) := by
      rw [hμ, MeasureTheory.withDensity_apply ρ hImeas]
      calc
        ENNReal.ofReal c * (volume : Measure E) (subgradientImage u S) =
            ∫⁻ p in subgradientImage u S, ENNReal.ofReal c :=
          (MeasureTheory.setLIntegral_const _ _).symm
        _ ≤ ∫⁻ p in subgradientImage u S, ρ p := by
          apply MeasureTheory.setLIntegral_mono' hImeas
          intro p hp
          exact (hρK p (hsubK hp)).1
    have hμupper :
        μ (subgradientImage u S) ≤
          ENNReal.ofReal C' * (volume : Measure E) (subgradientImage u S) := by
      rw [hμ, MeasureTheory.withDensity_apply ρ hImeas]
      calc
        ∫⁻ p in subgradientImage u S, ρ p ≤
            ∫⁻ p in subgradientImage u S, ENNReal.ofReal C' := by
          apply MeasureTheory.setLIntegral_mono' hImeas
          intro p hp
          exact le_trans (hρK p (hsubK hp)).2
            (ENNReal.ofReal_mono (le_max_left C 1))
        _ = ENNReal.ofReal C' * (volume : Measure E) (subgradientImage u S) :=
          MeasureTheory.setLIntegral_const _ _
    constructor
    · have hmul :
          ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S ≤
            ENNReal.ofReal C' * (volume : Measure E) (subgradientImage u S) := by
        calc
          ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S
              ≤ ν S := hlowerν
          _ = μ (subgradientImage u S) := hμS.symm
          _ ≤ _ := hμupper
      have hC0 : ENNReal.ofReal C' ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr hC'pos)
      have hCne : ENNReal.ofReal C' ≠ ∞ := ENNReal.ofReal_ne_top
      have hdiv :
          (ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S) /
              ENNReal.ofReal C' ≤
            (volume : Measure E) (subgradientImage u S) := by
        apply (ENNReal.div_le_iff hC0 hCne).mpr
        simpa [mul_comm] using hmul
      have hdiv' :
          ENNReal.ofReal (Real.exp (-m) / C') * (volume : Measure E) S ≤
            (volume : Measure E) (subgradientImage u S) := by
        simpa [ENNReal.ofReal_div_of_pos hC'pos, ENNReal.div_eq_inv_mul,
          mul_assoc, mul_left_comm, mul_comm] using hdiv
      simpa [a] using hdiv'
    · have hmul :
          ENNReal.ofReal c * (volume : Measure E) (subgradientImage u S) ≤
            ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) S := by
        calc
          ENNReal.ofReal c * (volume : Measure E) (subgradientImage u S)
              ≤ μ (subgradientImage u S) := hμlower
          _ = ν S := hμS
          _ ≤ _ := hupperν
      have hc0 : ENNReal.ofReal c ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr hc)
      have hcne : ENNReal.ofReal c ≠ ∞ := ENNReal.ofReal_ne_top
      have hdiv :
          (volume : Measure E) (subgradientImage u S) ≤
            (ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) S) /
              ENNReal.ofReal c := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcne)).mpr
        simpa [mul_comm] using hmul
      have hdiv' :
          (volume : Measure E) (subgradientImage u S) ≤
            ENNReal.ofReal (Real.exp (-n) / c) * (volume : Measure E) S := by
        simpa [ENNReal.ofReal_div_of_pos hc, ENNReal.div_eq_inv_mul,
          mul_assoc, mul_left_comm, mul_comm] using hdiv
      simpa [b] using hdiv'
  · have hQempty : Q = ∅ := Set.not_nonempty_iff_eq_empty.mp hQne
    refine ⟨1, 1, by norm_num, ?_⟩
    intro S hS hSQ
    have hSsub : S ⊆ (∅ : Set E) := by
      intro x hx
      rw [hQempty] at hSQ
      exact hSQ hx
    have hSempty : S = ∅ :=
      Set.Subset.antisymm hSsub (Set.empty_subset S)
    rw [hSempty]
    simp [subgradientImage]

end FunctionalInequalities.Analysis

end LT14CLocalAlexandrovBounds

section LT11C2AlexandrovSliding

open Set Metric
open scoped RealInnerProductSpace

/-! Sliding supporting hyperplanes (Caffarelli block; task L-T11c2). -/

namespace FunctionalInequalities.Analysis

/-- **Sliding lemma for the Alexandrov maximum principle** (weak Letwin route, Caffarelli block T11c):
if `u` is convex, `u ≥ 0` on the frontier of a bounded open `Ω`, `u x₀ < 0` at some `x₀ ∈ Ω`, and the
affine function `x ↦ u x₀ + ⟪p, x − x₀⟫` is `≤ 0` on `closure Ω`, then `p` is a subgradient of `u` at
some point of `Ω`. In particular, `closedBall 0 (-u x₀ / diam Ω) ⊆ ∂u(Ω)`, and the cone over the ball
with apex in the direction of a nearest boundary point is contained in `∂u(Ω)`. -/
theorem mem_subgradientImage_of_affine_le_of_nonneg_frontier {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hfr : ∀ x ∈ frontier Ω, 0 ≤ u x) {x₀ : E} (hx₀ : x₀ ∈ Ω) (hneg : u x₀ < 0)
    {p : E} (hp : ∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) : p ∈ subgradientImage u Ω := by
  have _hneg : u x₀ < 0 := hneg
  let ell : E → ℝ := fun x => u x₀ + ⟪p, x - x₀⟫
  let w : E → ℝ := fun x => u x - ell x
  have hu : Continuous u := by
    exact continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
  have hconst : Continuous (fun _ : E => x₀) := continuous_const
  have hinner : Continuous (fun x : E => ⟪p, x - x₀⟫) := by
    exact
      (continuous_const : Continuous (fun _ : E => p)).inner
        (continuous_id.sub hconst)
  have hell_cont : Continuous ell := by
    change Continuous (fun x : E => u x₀ + ⟪p, x - x₀⟫)
    have h :=
      (continuous_const : Continuous (fun _ : E => u x₀)).add hinner
    exact h.congr (fun x => rfl)
  have hw : Continuous w := by
    change Continuous (fun x : E => u x - ell x)
    exact (hu.sub hell_cont).congr (fun x => rfl)
  have hcomp : IsCompact (closure Ω) := hb.isCompact_closure
  have hne : (closure Ω).Nonempty := ⟨x₀, subset_closure hx₀⟩
  obtain ⟨x₁, hx₁, hmin₁⟩ :=
    hcomp.exists_isMinOn hne hw.continuousOn
  have hw₀ : w x₀ = 0 := by
    simp [w, ell]
  have hle₁ : w x₁ ≤ 0 := by
    calc
      w x₁ ≤ w x₀ := hmin₁ (subset_closure hx₀)
      _ = 0 := hw₀
  have hfront : ∀ x ∈ frontier Ω, 0 ≤ w x := by
    intro x hx
    change 0 ≤ u x - ell x
    exact
      sub_nonneg.mpr
        (le_trans
          (by simpa [ell] using hp x (frontier_subset_closure hx))
          (hfr x hx))
  have hex : ∃ x₂ ∈ Ω, IsMinOn w (closure Ω) x₂ := by
    by_cases h₁fr : x₁ ∈ frontier Ω
    · have hw₁ : w x₁ = 0 := le_antisymm hle₁ (hfront x₁ h₁fr)
      have hmin₀ : IsMinOn w (closure Ω) x₀ := by
        intro z hz
        calc
          w x₀ = w x₁ := hw₀.trans hw₁.symm
          _ ≤ w z := hmin₁ hz
      exact ⟨x₀, hx₀, hmin₀⟩
    · have hx₁union : x₁ ∈ Ω ∪ frontier Ω := by
        rw [← closure_eq_self_union_frontier]
        exact hx₁
      exact ⟨x₁, hx₁union.resolve_right h₁fr, hmin₁⟩
  obtain ⟨x₂, hx₂, hmin₂⟩ := hex
  refine ⟨x₂, hx₂, ?_⟩
  intro y
  have htouch (z : E) :
      ell z + w x₂ = u x₂ + ⟪p, z - x₂⟫ := by
    have hi :
        ⟪p, z - x₀⟫ - ⟪p, x₂ - x₀⟫ = ⟪p, z - x₂⟫ := by
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      ring
    dsimp [w, ell]
    calc
      (u x₀ + ⟪p, z - x₀⟫) +
          (u x₂ - (u x₀ + ⟪p, x₂ - x₀⟫)) =
          u x₂ + (⟪p, z - x₀⟫ - ⟪p, x₂ - x₀⟫) := by ring
      _ = u x₂ + ⟪p, z - x₂⟫ := by rw [hi]
  have hwle : w x₂ ≤ w y := by
    by_contra hnot
    have hlt : w y < w x₂ := lt_of_not_ge hnot
    have hy : y ≠ x₂ := by
      intro hxy
      subst y
      exact (lt_irrefl _ hlt)
    have hdn : 0 < ‖y - x₂‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    obtain ⟨ε, hε, hball⟩ :=
      Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₂)
    set t : ℝ := min (1 / 2) (ε / (2 * ‖y - x₂‖)) with ht
    have htpos : 0 < t := by
      rw [ht]
      exact lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hdn))
    have htle : t ≤ 1 / 2 := by
      rw [ht]
      exact min_le_left _ _
    have htleone : t ≤ 1 := by
      linarith
    have htdiv : t ≤ ε / (2 * ‖y - x₂‖) := by
      rw [ht]
      exact min_le_right _ _
    have hcone : t * ‖y - x₂‖ < ε := by
      have hmul :=
        mul_le_mul_of_nonneg_right htdiv (le_of_lt hdn)
      calc
        t * ‖y - x₂‖ ≤ (ε / (2 * ‖y - x₂‖)) * ‖y - x₂‖ := hmul
        _ = ε / 2 := by field_simp [ne_of_gt hdn]
        _ < ε := by linarith
    let z : E := (1 - t) • x₂ + t • y
    have hzsub : z - x₂ = t • (y - x₂) := by
      dsimp [z]
      module
    have hzball : z ∈ ball x₂ ε := by
      rw [mem_ball, dist_eq_norm]
      rw [hzsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      exact hcone
    have hzΩ : z ∈ Ω := hball hzball
    have hzcl : z ∈ closure Ω := subset_closure hzΩ
    have hconv' :
        ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
          u (a • x₂ + b • y) ≤ a • u x₂ + b • u y :=
      hconv.2 (mem_univ x₂) (mem_univ y)
    have huv' :
        u ((1 - t) • x₂ + t • y) ≤
          (1 - t) • u x₂ + t • u y :=
      hconv' (a := 1 - t) (b := t)
        (sub_nonneg.mpr htleone) (le_of_lt htpos) (by ring)
    have huv : u z ≤ (1 - t) * u x₂ + t * u y := by
      dsimp [z]
      simpa only [smul_eq_mul] using huv'
    have hzlin :
        z - x₀ = (1 - t) • (x₂ - x₀) + t • (y - x₀) := by
      dsimp [z]
      module
    have hell :
        ell z = (1 - t) * ell x₂ + t * ell y := by
      dsimp [ell]
      rw [hzlin, inner_add_right, inner_smul_right, inner_smul_right]
      ring
    have hwz : w z ≤ (1 - t) * w x₂ + t * w y := by
      calc
        w z = u z - ell z := rfl
        _ ≤ ((1 - t) * u x₂ + t * u y) - ell z :=
          sub_le_sub_right huv _
        _ = (1 - t) * w x₂ + t * w y := by
          rw [hell]
          dsimp [w]
          ring
    have hminz : w x₂ ≤ w z := hmin₂ hzcl
    have hmul : t * w x₂ ≤ t * w y := by
      nlinarith [hminz, hwz]
    have hltmul : t * w y < t * w x₂ :=
      (mul_lt_mul_of_pos_left hlt htpos)
    exact (not_lt_of_ge hmul) hltmul
  calc
    u x₂ + ⟪p, y - x₂⟫ = ell y + w x₂ := (htouch y).symm
    _ ≤ ell y + w y := by linarith
    _ = u y := by
      dsimp [w]
      ring

end FunctionalInequalities.Analysis

end LT11C2AlexandrovSliding

section LT11C3NearestBoundaryHalfspace

open Set Metric
open scoped RealInnerProductSpace

/-! Nearest boundary points and supporting half-spaces (task L-T11c3). -/

namespace FunctionalInequalities.Analysis

/-- **Supporting half-space at a nearest boundary point of an open convex set** (weak Letwin route,
Caffarelli block T11c, the `dist(x₀, ∂Ω)` factor of the Alexandrov estimate): for a bounded open convex
`Ω` and `x₀ ∈ Ω`, with `d := infDist x₀ (frontier Ω)`, there is a unit vector `e` such that
`⟪x − x₀, e⟫ ≤ d` for every `x ∈ Ω`. -/
theorem exists_unit_inner_le_infDist_frontier {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω)
    (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ e : E, ‖e‖ = 1 ∧ ∀ x ∈ Ω, ⟪x - x₀, e⟫ ≤ infDist x₀ (frontier Ω) := by
  classical
  obtain ⟨r, hr⟩ := hb.subset_closedBall x₀
  have hcompact_ball : IsCompact (closedBall x₀ r) := isCompact_closedBall x₀ r
  have hcompact_frontier : IsCompact (frontier Ω) :=
    hcompact_ball.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (closure_minimal hr isClosed_closedBall))
  have hfrontier_nonempty : (frontier Ω).Nonempty := by
    by_contra hne
    have hfrontier_empty : frontier Ω = ∅ := by
      ext y
      constructor
      · intro hy
        exact (hne ⟨y, hy⟩).elim
      · intro hy
        simp at hy
    rw [frontier_eq_empty_iff] at hfrontier_empty
    rcases hfrontier_empty with hΩempty | hΩuniv
    · rw [hΩempty] at hx₀
      exact hx₀
    · obtain ⟨s, hs⟩ := hb.subset_closedBall x₀
      have hs_nonneg : 0 ≤ s := by
        have hsx : dist x₀ x₀ ≤ s := hs hx₀
        simpa only [dist_self] using hsx
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
        simp [ne_of_gt hvpos]
      let y : E := x₀ + (s + 1) • (‖v‖⁻¹ • v)
      have hyΩ : y ∈ Ω := by
        rw [hΩuniv]
        exact mem_univ y
      have hyball : y ∈ closedBall x₀ s := hs hyΩ
      have hnorm : ‖y - x₀‖ = s + 1 := by
        have hs1 : 0 ≤ s + 1 := by linarith
        calc
          ‖y - x₀‖ = ‖(s + 1) • (‖v‖⁻¹ • v)‖ := by
            dsimp [y]
            rw [add_sub_cancel_left]
          _ = ‖s + 1‖ * ‖‖v‖⁻¹ • v‖ := norm_smul _ _
          _ = (s + 1) * 1 := by
            rw [Real.norm_eq_abs, abs_of_nonneg hs1, hunit]
          _ = s + 1 := by ring
      have hydist : dist y x₀ ≤ s := by
        exact hyball
      rw [dist_eq_norm, hnorm] at hydist
      linarith
  obtain ⟨xb, hxb, hxb_dist⟩ :=
    hcompact_frontier.exists_infDist_eq_dist hfrontier_nonempty x₀
  have hxbΩ : xb ∉ Ω := by
    intro h
    apply hxb.2
    rw [hΩ.interior_eq]
    exact h
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hc hΩ hxbΩ
  let e₀ : E := (InnerProductSpace.toDual ℝ E).symm f
  have hdual (z : E) : inner ℝ e₀ z = f z := by
    dsimp [e₀]
    exact InnerProductSpace.toDual_symm_apply
  have hrepr (z : E) : f z = inner ℝ z e₀ := by
    calc
      f z = inner ℝ e₀ z := (hdual z).symm
      _ = inner ℝ z e₀ := real_inner_comm _ _
  have he₀_ne : e₀ ≠ 0 := by
    intro he₀_zero
    have hzero (z : E) : f z = 0 := by
      rw [hrepr, he₀_zero]
      simp
    have hlt := hf x₀ hx₀
    rw [hzero x₀, hzero xb] at hlt
    exact (lt_irrefl 0) hlt
  let e : E := ‖e₀‖⁻¹ • e₀
  have he_norm : ‖e‖ = 1 := by
    have hnorm_pos : 0 < ‖e₀‖ := norm_pos_iff.mpr he₀_ne
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos)]
    simp [ne_of_gt hnorm_pos]
  refine ⟨e, he_norm, ?_⟩
  intro x hx
  have hfx : f x ≤ f xb := (hf x hx).le
  have hgap : f xb - f x₀ ≤ ‖xb - x₀‖ * ‖e₀‖ := by
    calc
      f xb - f x₀ = f (xb - x₀) := (map_sub f xb x₀).symm
      _ = inner ℝ (xb - x₀) e₀ := hrepr (xb - x₀)
      _ ≤ |inner ℝ (xb - x₀) e₀| := le_abs_self _
      _ ≤ ‖xb - x₀‖ * ‖e₀‖ := abs_real_inner_le_norm _ _
  have hrepr_norm (z : E) : inner ℝ z e = f z / ‖e₀‖ := by
    change inner ℝ z (‖e₀‖⁻¹ • e₀) = f z / ‖e₀‖
    rw [real_inner_smul_right, hrepr]
    ring
  have hnorm_pos : 0 < ‖e₀‖ := norm_pos_iff.mpr he₀_ne
  calc
    ⟪x - x₀, e⟫ = (f x - f x₀) / ‖e₀‖ := by
      rw [hrepr_norm, map_sub]
    _ ≤ (f xb - f x₀) / ‖e₀‖ :=
      div_le_div_of_nonneg_right (sub_le_sub_right hfx _) (norm_nonneg _)
    _ ≤ (‖xb - x₀‖ * ‖e₀‖) / ‖e₀‖ :=
      div_le_div_of_nonneg_right hgap (norm_nonneg _)
    _ = ‖xb - x₀‖ := by
      field_simp [ne_of_gt hnorm_pos]
    _ = dist x₀ xb := by
      rw [dist_eq_norm]
      exact norm_sub_rev _ _
    _ = infDist x₀ (frontier Ω) := hxb_dist.symm

end FunctionalInequalities.Analysis

end LT11C3NearestBoundaryHalfspace

section LT11C4ConeVolume

open MeasureTheory Set Metric
open scoped ENNReal

/-! Volumes of cones over convex sets (task L-T11c4). -/

namespace FunctionalInequalities.Analysis

/-- **Volume of the cone over a ball** (weak Letwin route, Caffarelli block T11c, Alexandrov maximum
principle): there is `c > 0`, depending only on `E`, such that the convex hull of the closed ball of
radius `r` and a point `q` with `‖q‖ ≥ r` has volume at least `c · r^(n−1) · ‖q‖`, `n = dim E`. -/
theorem exists_pos_volume_convexHull_closedBall_union_singleton_ge {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → ∀ q : E, r ≤ ‖q‖ →
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
        (volume : Measure E) (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := by
  classical
  by_cases hE : Nontrivial E
  · let v : ℝ := (volume (ball (0 : E) 1)).toReal
    let c : ℝ := v / (2 : ℝ) ^ (Module.finrank ℝ E + 2)
    have hn0 : Module.finrank ℝ E ≠ 0 := by
      intro hn
      have hs : Subsingleton E := Module.finrank_zero_iff.mp hn
      exact (not_nontrivial_iff_subsingleton.mpr hs) hE
    have hn : 1 ≤ Module.finrank ℝ E :=
      Nat.one_le_iff_ne_zero.mpr hn0
    have hv_top : volume (ball (0 : E) 1) ≠ ∞ :=
      ne_of_lt measure_ball_lt_top
    have hv_pos : 0 < v := by
      dsimp [v]
      exact ENNReal.toReal_pos
        (ne_of_gt (Metric.measure_ball_pos volume (0 : E) zero_lt_one)) hv_top
    have hc : 0 < c := by
      dsimp [c]
      positivity
    refine ⟨c, hc, ?_⟩
    intro r hr q hq
    have hqpos : 0 < ‖q‖ := lt_of_lt_of_le hr hq
    let e : E := ‖q‖⁻¹ • q
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hqpos]
      exact inv_mul_cancel₀ hqpos.ne'
    have hqe : q = ‖q‖ • e := by
      calc
        q = (1 : ℝ) • q := (one_smul ℝ q).symm
        _ = (‖q‖ * ‖q‖⁻¹) • q := by
          rw [mul_inv_cancel₀ hqpos.ne', one_smul]
        _ = ‖q‖ • (‖q‖⁻¹ • q) := by rw [smul_smul]
        _ = ‖q‖ • e := by rfl
    let N : ℕ := ⌊‖q‖ / (4 * r)⌋₊
    let C : ℕ → E := fun k => ((k : ℝ) * (2 * r)) • e
    have hN : (N : ℝ) ≤ ‖q‖ / (4 * r) := by
      dsimp [N]
      exact Nat.floor_le (by positivity)
    have hball :
        ∀ k ∈ Finset.range (N + 1),
          closedBall (C k) (r / 2) ⊆
            convexHull ℝ (closedBall (0 : E) r ∪ {q}) := by
      intro k hk x hx
      have hkN : k ≤ N :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hkr : (k : ℝ) * (2 * r) ≤ ‖q‖ / 2 := by
        have hk' : (k : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast hkN
        have h₁ : (k : ℝ) * (2 * r) ≤ (N : ℝ) * (2 * r) :=
          mul_le_mul_of_nonneg_right hk' (by positivity)
        have h₂ : (N : ℝ) * (2 * r) ≤ ‖q‖ / 2 := by
          calc
            (N : ℝ) * (2 * r) ≤ (‖q‖ / (4 * r)) * (2 * r) :=
              mul_le_mul_of_nonneg_right hN (by positivity)
            _ = ‖q‖ / 2 := by
              field_simp
              ring
        exact h₁.trans h₂
      have hx' : ‖x - C k‖ ≤ r / 2 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      let s : ℝ := ((k : ℝ) * (2 * r)) / ‖q‖
      let b : E := (1 - s)⁻¹ • (x - C k)
      have hs0 : 0 ≤ s := by
        dsimp [s]
        positivity
      have hs_half : s ≤ 1 / 2 := by
        dsimp [s]
        apply (div_le_iff₀ hqpos).2
        nlinarith [hkr]
      have hs1 : s ≤ 1 := by
        linarith
      have hden : 0 < 1 - s := by
        linarith
      have hi : (1 - s)⁻¹ ≤ 2 := by
        have hmul :
            (1 / 2 : ℝ) * (1 - s)⁻¹ ≤ (1 - s) * (1 - s)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (by linarith [hs_half]) (inv_nonneg.mpr hden.le)
        rw [mul_inv_cancel₀ hden.ne'] at hmul
        nlinarith
      have hb : b ∈ closedBall (0 : E) r := by
        rw [Metric.mem_closedBall, dist_zero_right]
        dsimp [b]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hden.le)]
        calc
          (1 - s)⁻¹ * ‖x - C k‖ ≤ 2 * ‖x - C k‖ :=
            mul_le_mul_of_nonneg_right hi (norm_nonneg _)
          _ ≤ 2 * (r / 2) := by
            exact mul_le_mul_of_nonneg_left hx' (by norm_num)
          _ = r := by ring
      have hsQ : s * ‖q‖ = (k : ℝ) * (2 * r) := by
        dsimp [s]
        field_simp
      have hs_q : s • q = (s * ‖q‖) • e := by
        calc
          s • q = s • (‖q‖ • e) := congrArg (fun z : E => s • z) hqe
          _ = (s * ‖q‖) • e := by rw [smul_smul]
      have hrep : (1 - s) • b + s • q = x := by
        calc
          (1 - s) • b + s • q =
              (1 - s) • b + (s * ‖q‖) • e := by rw [hs_q]
          _ = (x - C k) + (s * ‖q‖) • e := by
            dsimp [b]
            rw [smul_smul, mul_inv_cancel₀ hden.ne', one_smul]
          _ = (x - C k) + ((k : ℝ) * (2 * r)) • e := by rw [hsQ]
          _ = x := by
            dsimp [C]
            abel
      have hxseg : x ∈ segment ℝ b q := by
        rw [segment_eq_image]
        refine ⟨s, ⟨hs0, hs1⟩, ?_⟩
        simpa using hrep
      exact
        segment_subset_convexHull
          (Set.mem_union_left {q} hb)
          (Set.mem_union_right (closedBall (0 : E) r) (by simp))
          hxseg
    have hdisj :
        (Finset.range (N + 1) : Set ℕ).PairwiseDisjoint
          (fun k => closedBall (C k) (r / 2)) := by
      rw [Set.pairwiseDisjoint_iff]
      intro i hi j hj hne
      rcases hne with ⟨x, hxi, hxj⟩
      by_contra hneq
      rcases lt_or_gt_of_ne hneq with hlt | hgt
      · have hij : i + 1 ≤ j := Nat.succ_le_iff.mp hlt
        have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by
          exact_mod_cast hij
        have hscalar :
            (i : ℝ) * (2 * r) - (j : ℝ) * (2 * r) ≤ 0 := by
          nlinarith [hij', hr.le]
        have hdist : 2 * r ≤ dist (C i) (C j) := by
          rw [dist_eq_norm]
          dsimp [C]
          rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs,
            abs_of_nonpos hscalar]
          nlinarith [hij', hr]
        have hxi' : dist (C i) x ≤ r / 2 := by
          rw [dist_comm]
          exact Metric.mem_closedBall.mp hxi
        have hxj' : dist x (C j) ≤ r / 2 :=
          Metric.mem_closedBall.mp hxj
        have hlt' : dist (C i) (C j) ≤ r := by
          calc
            dist (C i) (C j) ≤ dist (C i) x + dist x (C j) :=
              dist_triangle _ _ _
            _ ≤ r := by linarith
        linarith
      · have hji : j + 1 ≤ i := Nat.succ_le_iff.mp hgt
        have hji' : (j : ℝ) + 1 ≤ (i : ℝ) := by
          exact_mod_cast hji
        have hscalar :
            (j : ℝ) * (2 * r) - (i : ℝ) * (2 * r) ≤ 0 := by
          nlinarith [hji', hr.le]
        have hdist : 2 * r ≤ dist (C j) (C i) := by
          rw [dist_eq_norm]
          dsimp [C]
          rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs,
            abs_of_nonpos hscalar]
          nlinarith [hji', hr]
        have hxj' : dist (C j) x ≤ r / 2 := by
          rw [dist_comm]
          exact Metric.mem_closedBall.mp hxj
        have hxi' : dist x (C i) ≤ r / 2 :=
          Metric.mem_closedBall.mp hxi
        have hlt' : dist (C j) (C i) ≤ r := by
          calc
            dist (C j) (C i) ≤ dist (C j) x + dist x (C i) :=
              dist_triangle _ _ _
            _ ≤ r := by linarith
        linarith
    have hmeas :
        ∀ k ∈ Finset.range (N + 1),
          MeasurableSet (closedBall (C k) (r / 2)) := by
      intro k hk
      exact isClosed_closedBall.measurableSet
    have hunion :
        volume (⋃ k ∈ Finset.range (N + 1), closedBall (C k) (r / 2)) =
          ∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2)) :=
      measure_biUnion_finset hdisj hmeas
    have hsum :
        (∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2))) =
          ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) := by
      calc
        (∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2))) =
            ∑ k ∈ Finset.range (N + 1),
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Measure.addHaar_closedBall volume (C k) (by positivity)]
        _ = ((N + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsubset :
        (⋃ k ∈ Finset.range (N + 1), closedBall (C k) (r / 2)) ⊆
          convexHull ℝ (closedBall (0 : E) r ∪ {q}) := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hk, hx⟩
      exact hball k hk hx
    have hmeasure :
        ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) ≤
          volume (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := by
      calc
        ((N + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) =
            ∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2)) := hsum.symm
        _ = volume (⋃ k ∈ Finset.range (N + 1), closedBall (C k) (r / 2)) :=
          hunion.symm
        _ ≤ volume (convexHull ℝ (closedBall (0 : E) r ∪ {q})) :=
          measure_mono hsubset
    have hcount : ‖q‖ / (4 * r) < (N + 1 : ℝ) := by
      dsimp [N]
      exact Nat.lt_floor_add_one _
    have hreal :
        c * r ^ (Module.finrank ℝ E - 1) * ‖q‖ ≤
          (N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v := by
      have hQ : ‖q‖ ≤ 4 * r * (N + 1 : ℝ) := by
        have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * r)).mp hcount
        exact le_of_lt (by linarith)
      have hcoef :
          0 ≤ c * r ^ (Module.finrank ℝ E - 1) :=
        mul_nonneg hc.le (pow_nonneg hr.le _)
      have hp :
          r ^ (Module.finrank ℝ E - 1) * r =
            r ^ Module.finrank ℝ E := by
        rw [← pow_succ]
        congr 1
        exact Nat.sub_add_cancel hn
      calc
        c * r ^ (Module.finrank ℝ E - 1) * ‖q‖ =
            (c * r ^ (Module.finrank ℝ E - 1)) * ‖q‖ := by ring
        _ ≤ (c * r ^ (Module.finrank ℝ E - 1)) *
              (4 * r * (N + 1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hQ hcoef
        _ = ((N + 1 : ℝ) * v *
              (r ^ (Module.finrank ℝ E - 1) * r)) /
              (2 : ℝ) ^ Module.finrank ℝ E := by
          dsimp [c]
          field_simp [show (2 : ℝ) ≠ 0 by norm_num]
          ring
        _ = (N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v := by
          rw [hp, div_pow]
          ring
    have hv : ENNReal.ofReal v = volume (ball (0 : E) 1) :=
      ENNReal.ofReal_toReal hv_top
    have hcast :
        ENNReal.ofReal ((N : ℝ) + 1) =
          (N : ℝ≥0∞) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENNReal.ofReal_natCast (N + 1))
    have hEq :
        ENNReal.ofReal
            ((N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v) =
          ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) := by
      calc
        ENNReal.ofReal
            ((N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v) =
            ENNReal.ofReal
              (((N : ℝ) + 1) *
                (((r / 2) ^ Module.finrank ℝ E) * v)) := by
                  congr 1
                  ring
        _ = ENNReal.ofReal ((N : ℝ) + 1) *
              ENNReal.ofReal (((r / 2) ^ Module.finrank ℝ E) * v) := by
              rw [ENNReal.ofReal_mul (by positivity)]
        _ = ((N : ℝ≥0∞) + 1) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              rw [hcast, ENNReal.ofReal_mul (by positivity), hv]
        _ = ((N + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              norm_num
    calc
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
          ENNReal.ofReal
            ((N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) := hEq
      _ ≤ volume (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := hmeasure
  · have hsub : Subsingleton E :=
      not_nontrivial_iff_subsingleton.mp hE
    refine ⟨1, zero_lt_one, ?_⟩
    intro r hr q hq
    have hq0 : q = 0 := hsub.elim q 0
    rw [hq0, norm_zero] at hq
    linarith

end FunctionalInequalities.Analysis

end LT11C4ConeVolume

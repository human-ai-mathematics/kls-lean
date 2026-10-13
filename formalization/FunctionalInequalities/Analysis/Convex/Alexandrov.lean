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

section LT11C5AlexandrovMaximumPrinciple

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-! The Alexandrov maximum principle (task L-T11c5). -/

namespace FunctionalInequalities.Analysis

private lemma alexandrov_frontier_nonempty {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    {Ω : Set E} (hb : Bornology.IsBounded Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (frontier Ω).Nonempty := by
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
    let e : E := ‖v‖⁻¹ • v
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hvpos.le)]
      exact inv_mul_cancel₀ hvpos.ne'
    let y : E := x₀ + (s + 1) • e
    have hyΩ : y ∈ Ω := by
      rw [hΩuniv]
      exact mem_univ y
    have hyball : y ∈ closedBall x₀ s := hs hyΩ
    have hnorm : ‖y - x₀‖ = s + 1 := by
      dsimp [y]
      rw [add_sub_cancel_left, norm_smul, he, mul_one]
      exact abs_of_nonneg (by linarith)
    have hydist : dist y x₀ ≤ s := hyball
    rw [dist_eq_norm, hnorm] at hydist
    linarith

private lemma alexandrov_diam_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    0 < diam Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let e : E := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hvpos.le)]
    exact inv_mul_cancel₀ hvpos.ne'
  let y : E := x₀ + (r / 2) • e
  have hy : y ∈ Ω := by
    apply hball
    rw [mem_ball, dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r / 2)]
    linarith
  have hdist : dist x₀ y ≤ diam Ω :=
    Metric.dist_le_diam_of_mem hb hx₀ hy
  have hdist' : dist x₀ y = r / 2 := by
    rw [dist_eq_norm, norm_sub_rev]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r / 2)]
  rw [hdist'] at hdist
  linarith

private lemma alexandrov_infDist_frontier_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    0 < infDist x₀ (frontier Ω) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  have hne : (frontier Ω).Nonempty :=
    alexandrov_frontier_nonempty hb hx₀
  apply lt_of_lt_of_le hr
  apply (Metric.le_infDist hne).2
  intro y hy
  have hyn : y ∉ Ω := by
    intro hyΩ
    apply hy.2
    rw [hΩ.interior_eq]
    exact hyΩ
  have hnot : ¬ dist y x₀ < r := by
    intro hdist
    exact hyn (hball (mem_ball.mpr hdist))
  simpa [dist_comm] using (le_of_not_gt hnot)

private lemma alexandrov_frontier_distance_le_diam {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    {_Ω : Set E} (_hΩ : IsOpen _Ω) (hb : Bornology.IsBounded _Ω)
    {x₀ : E} (hx₀ : x₀ ∈ _Ω) :
    infDist x₀ (frontier _Ω) ≤ diam _Ω := by
  obtain ⟨r, hr⟩ := hb.subset_closedBall x₀
  have hcompact_ball : IsCompact (closedBall x₀ r) :=
    isCompact_closedBall x₀ r
  have hcompact_frontier : IsCompact (frontier _Ω) :=
    hcompact_ball.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (closure_minimal hr isClosed_closedBall))
  obtain ⟨y, hy, hyeq⟩ :=
    hcompact_frontier.exists_infDist_eq_dist
      (alexandrov_frontier_nonempty hb hx₀) x₀
  have hdist : dist x₀ y ≤ diam _Ω := by
    have hdist' : dist x₀ y ≤ diam (closure _Ω) :=
      Metric.dist_le_diam_of_mem hb.closure
        (subset_closure hx₀) (frontier_subset_closure hy)
    simpa only [Metric.diam_closure] using hdist'
  exact hyeq.trans_le hdist

private lemma alexandrov_affine_set_convex {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u : E → ℝ} {x₀ : E}
    {Ω : Set E} :
    Convex ℝ {p : E | ∀ x ∈ closure Ω,
      u x₀ + ⟪p, x - x₀⟫ ≤ 0} := by
  intro p hp q hq a b ha hb hab x hx
  have hp' := hp x hx
  have hq' := hq x hx
  have hi :
      ⟪a • p + b • q, x - x₀⟫ =
        a * ⟪p, x - x₀⟫ + b * ⟪q, x - x₀⟫ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc
    u x₀ + ⟪a • p + b • q, x - x₀⟫ =
        u x₀ + (a * ⟪p, x - x₀⟫ + b * ⟪q, x - x₀⟫) := by
          rw [hi]
    _ = (a + b) * u x₀ +
          (a * ⟪p, x - x₀⟫ + b * ⟪q, x - x₀⟫) := by
          rw [hab]
          ring
    _ = a * (u x₀ + ⟪p, x - x₀⟫) +
          b * (u x₀ + ⟪q, x - x₀⟫) := by
          ring
    _ ≤ 0 := by
      simpa using add_le_add
        (mul_nonpos_of_nonneg_of_nonpos ha hp')
        (mul_nonpos_of_nonneg_of_nonpos hb hq')

/-- **Alexandrov maximum principle** (Gutiérrez, *The Monge–Ampère equation*, Theorem 1.4.2; weak
Letwin route, Caffarelli block T11c): there is `c > 0` depending only on `E` such that for every
convex `u`, bounded open convex `Ω`, `u ≥ 0` on `∂Ω` and `x₀ ∈ Ω` with `u x₀ < 0`,
`c · (−u x₀)^n ≤ vol (∂u(Ω)) · diam(Ω)^(n−1) · dist(x₀, ∂Ω)`, `n = dim E`. -/
theorem exists_pos_alexandrov_maximum_principle {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : E → ℝ), ConvexOn ℝ univ u → ∀ (Ω : Set E), IsOpen Ω → Convex ℝ Ω →
      Bornology.IsBounded Ω → (∀ x ∈ frontier Ω, 0 ≤ u x) → ∀ x₀ ∈ Ω, u x₀ < 0 →
      ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) ≤
        (volume : Measure E) (subgradientImage u Ω) *
          ENNReal.ofReal (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x₀ (frontier Ω)) := by
  obtain ⟨c, hc, hcone⟩ :=
    exists_pos_volume_convexHull_closedBall_union_singleton_ge (E := E)
  refine ⟨c, hc, ?_⟩
  intro u hconv Ω hΩ hΩconv hb hfr x₀ hx₀ hneg
  let m : ℝ := -u x₀
  let D : ℝ := diam Ω
  let d : ℝ := infDist x₀ (frontier Ω)
  have hm : 0 < m := by
    dsimp [m]
    linarith
  have hD : 0 < D := alexandrov_diam_pos hΩ hb hx₀
  have hd : 0 < d := alexandrov_infDist_frontier_pos hΩ hb hx₀
  have hdd : d ≤ D :=
    alexandrov_frontier_distance_le_diam hΩ hb hx₀
  obtain ⟨e, he, heΩ⟩ :=
    exists_unit_inner_le_infDist_frontier hΩ hΩconv hb hx₀
  let r : ℝ := m / D
  let q : E := (m / d) • e
  have hr : 0 < r := div_pos hm hD
  have hqnorm : ‖q‖ = m / d := by
    dsimp [q]
    rw [norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos (div_pos hm hd)]
  have hrq : r ≤ ‖q‖ := by
    rw [hqnorm]
    exact div_le_div_of_nonneg_left hm.le hd hdd
  let A : Set E := {p : E | ∀ x ∈ closure Ω,
      u x₀ + ⟪p, x - x₀⟫ ≤ 0}
  have hAconv : Convex ℝ A :=
    alexandrov_affine_set_convex
  have hballA : closedBall (0 : E) r ⊆ A := by
    intro p hp x hx
    have hdist := Metric.dist_le_diam_of_mem hb.closure
      hx (subset_closure hx₀)
    have hxd : ‖x - x₀‖ ≤ D := by
      simpa only [dist_eq_norm, Metric.diam_closure] using hdist
    have hpnorm : ‖p‖ ≤ r := by
      simpa [mem_closedBall, dist_zero_right] using hp
    have hinner : ⟪p, x - x₀⟫ ≤ ‖p‖ * ‖x - x₀‖ :=
      le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    have hmul : ‖p‖ * ‖x - x₀‖ ≤ r * D :=
      mul_le_mul hpnorm hxd (norm_nonneg _) (by positivity)
    have hzero : u x₀ + r * D = 0 := by
      dsimp [r, m]
      rw [div_mul_cancel₀ _ hD.ne']
      ring
    calc
      u x₀ + ⟪p, x - x₀⟫ ≤ u x₀ + ‖p‖ * ‖x - x₀‖ := by
        exact add_le_add (le_refl _) hinner
      _ ≤ u x₀ + r * D := by
        exact add_le_add (le_refl _) hmul
      _ = 0 := hzero
  have hqA : q ∈ A := by
    intro x hx
    have hΩbound : ∀ y ∈ Ω, u x₀ + ⟪q, y - x₀⟫ ≤ 0 := by
      intro y hy
      have hey := heΩ y hy
      have hey' : ⟪e, y - x₀⟫ ≤ d := by
        simpa only [real_inner_comm] using hey
      have hi :
          ⟪q, y - x₀⟫ =
            (m / d) * ⟪e, y - x₀⟫ := by
        rw [real_inner_smul_left]
      have hmul :
          (m / d) * ⟪e, y - x₀⟫ ≤ (m / d) * d :=
        mul_le_mul_of_nonneg_left hey' (div_pos hm hd).le
      calc
        u x₀ + ⟪q, y - x₀⟫ =
            u x₀ + (m / d) * ⟪e, y - x₀⟫ := by rw [hi]
        _ ≤ u x₀ + (m / d) * d := by
          exact add_le_add (le_refl _) hmul
        _ = 0 := by
          dsimp [m]
          rw [div_mul_cancel₀ _ hd.ne']
          ring
    have hcont : Continuous (fun y : E =>
        u x₀ + ⟪q, y - x₀⟫) :=
      continuous_const.add
        ((continuous_const : Continuous (fun _ : E => q)).inner
          (continuous_id.sub continuous_const))
    have hclosed :
        IsClosed {y : E | u x₀ + ⟪q, y - x₀⟫ ≤ 0} :=
      isClosed_Iic.preimage hcont
    exact closure_minimal hΩbound hclosed hx
  have hHullA :
      convexHull ℝ (closedBall (0 : E) r ∪ {q}) ⊆ A :=
    convexHull_min (by
      intro p hp
      rcases hp with hp | hp
      · exact hballA hp
      · rw [Set.mem_singleton_iff] at hp
        rw [hp]
        exact hqA) hAconv
  have hsub :
      convexHull ℝ (closedBall (0 : E) r ∪ {q}) ⊆
        subgradientImage u Ω := by
    exact hHullA.trans (by
      intro p hp
      exact mem_subgradientImage_of_affine_le_of_nonneg_frontier
        hconv hΩ hb hfr hx₀ hneg hp)
  have hvol :
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
        (volume : Measure E) (subgradientImage u Ω) :=
    (hcone r hr q hrq).trans (measure_mono hsub)
  have hn : 1 ≤ Module.finrank ℝ E :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Module.finrank_pos (R := ℝ) (M := E)))
  have hcancel :
      (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
        c * m ^ (Module.finrank ℝ E - 1) * m := by
    rw [hqnorm]
    change
      (c * (m / D) ^ (Module.finrank ℝ E - 1) * (m / d)) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
        c * m ^ (Module.finrank ℝ E - 1) * m
    simp only [div_eq_mul_inv, mul_pow]
    have hpowD :
        D ^ (Module.finrank ℝ E - 1) *
            D⁻¹ ^ (Module.finrank ℝ E - 1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hD.ne', one_pow]
    calc
      (c * (m ^ (Module.finrank ℝ E - 1) *
          D⁻¹ ^ (Module.finrank ℝ E - 1)) *
          (m * d⁻¹)) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
          c * m ^ (Module.finrank ℝ E - 1) * m *
            (D ^ (Module.finrank ℝ E - 1) *
              D⁻¹ ^ (Module.finrank ℝ E - 1)) *
            (d⁻¹ * d) := by ring
      _ = c * m ^ (Module.finrank ℝ E - 1) * m := by
        rw [hpowD, inv_mul_cancel₀ hd.ne']
        ring
  have hEq :
      (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
        c * m ^ Module.finrank ℝ E := by
    calc
      (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
          c * m ^ (Module.finrank ℝ E - 1) * m := hcancel
      _ = c * (m ^ (Module.finrank ℝ E - 1) * m) := by ring
      _ = c * m ^ ((Module.finrank ℝ E - 1) + 1) := by
        rw [pow_succ]
      _ = c * m ^ Module.finrank ℝ E := by
        rw [Nat.sub_add_cancel hn]
  have hreal :
      c * m ^ Module.finrank ℝ E ≤
        (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) := by
    rw [hEq]
  have hreal' :
      ENNReal.ofReal (c * m ^ Module.finrank ℝ E) ≤
        ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          ENNReal.ofReal (D ^ (Module.finrank ℝ E - 1) * d) := by
    rw [← ENNReal.ofReal_mul (by positivity :
      0 ≤ c * r ^ (Module.finrank ℝ E - 1) * ‖q‖)]
    exact ENNReal.ofReal_mono hreal
  calc
    ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) =
        ENNReal.ofReal (c * m ^ Module.finrank ℝ E) := by
          rfl
    _ ≤ ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          ENNReal.ofReal (D ^ (Module.finrank ℝ E - 1) * d) := hreal'
    _ ≤ (volume : Measure E) (subgradientImage u Ω) *
          ENNReal.ofReal (D ^ (Module.finrank ℝ E - 1) * d) :=
      mul_le_mul' hvol (le_refl _)
    _ = (volume : Measure E) (subgradientImage u Ω) *
          ENNReal.ofReal (diam Ω ^ (Module.finrank ℝ E - 1) *
            infDist x₀ (frontier Ω)) := by
      rfl

end FunctionalInequalities.Analysis

end LT11C5AlexandrovMaximumPrinciple

section LT12C1QuadraticSubgradientImage

open MeasureTheory Set Matrix
open scoped RealInnerProductSpace ENNReal

/-! Subgradient images of quadratic functions (task L-T12c1). -/

namespace FunctionalInequalities.Analysis

/-- The quadratic function with constant `c`, slope `b` and Hessian matrix `A` centred at `x₀`:
`Q x = c + ⟪b, x − x₀⟫ + ½ ⟪x − x₀, A (x − x₀)⟫` (weak Letwin route, N8 viscosity tests). -/
def quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  c + ⟪b, x - x₀⟫ + (1 / 2) * ⟪x - x₀, Matrix.toEuclideanLin A (x - x₀)⟫

private lemma quadraticAt_inner_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, Matrix.toEuclideanLin A y⟫ = ⟪Matrix.toEuclideanLin A x, y⟫ := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  have hT : LinearMap.adjoint T = T := by
    calc
      LinearMap.adjoint T = Matrix.toEuclideanLin Aᴴ := by
        symm
        exact Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
      _ = T := by
        rw [hA.eq]
  change ⟪x, T y⟫ = ⟪T x, y⟫
  simpa [hT] using LinearMap.adjoint_inner_right T x y

private lemma quadraticAt_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪x, Matrix.toEuclideanLin A x⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change 0 ≤ (A *ᵥ x.ofLp) ⬝ᵥ star x.ofLp
  simpa [dotProduct_comm] using
    (posSemidef_iff_dotProduct_mulVec.mp hA).2 x.ofLp

private lemma quadraticAt_quadratic_expand {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) :
    quadraticAt A x₀ b c (x + v) =
      quadraticAt A x₀ b c x +
        ⟪b + Matrix.toEuclideanLin A (x - x₀), v⟫ +
          (1 / 2) * ⟪v, Matrix.toEuclideanLin A v⟫ := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  have hq (z w : EuclideanSpace ℝ (Fin n)) :
      ⟪z + w, T (z + w)⟫ =
        ⟪z, T z⟫ + 2 * ⟪T z, w⟫ + ⟪w, T w⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    rw [quadraticAt_inner_symm hA z w, real_inner_comm w (T z)]
    ring
  have harg : x + v - x₀ = (x - x₀) + v := by
    abel
  dsimp [quadraticAt]
  dsimp [T] at hq ⊢
  rw [harg, hq]
  have hlin :
      ⟪b + Matrix.toEuclideanLin A (x - x₀), v⟫ =
        ⟪b, v⟫ + ⟪Matrix.toEuclideanLin A (x - x₀), v⟫ := by
    rw [inner_add_left]
  rw [hlin, inner_add_right]
  ring

private lemma quadraticAt_subgradient_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) :
    (∀ y, quadraticAt A x₀ b c x + ⟪p, y - x⟫ ≤ quadraticAt A x₀ b c y) ↔
      p = b + Matrix.toEuclideanLin A (x - x₀) := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => b + T (z - x₀)
  constructor
  · intro hp
    have hineq (w : EuclideanSpace ℝ (Fin n)) :
        ⟪p - g x, w⟫ ≤ (1 / 2) * ⟪w, T w⟫ := by
      have h₁ := hp (x + w)
      have h₂ := quadraticAt_quadratic_expand hA.1 x₀ b c x w
      have h₁' :
          quadraticAt A x₀ b c x + ⟪p, w⟫ ≤ quadraticAt A x₀ b c (x + w) := by
        simpa only [add_sub_cancel_left] using h₁
      have h₃ : ⟪p, w⟫ = ⟪g x, w⟫ + ⟪p - g x, w⟫ := by
        rw [← inner_add_left]
        congr 1
        abel
      rw [h₂, h₃] at h₁'
      linarith
    have hv : p - g x = 0 := by
      by_contra hv
      let r : ℝ := ⟪p - g x, p - g x⟫
      let q : ℝ := ⟪p - g x, T (p - g x)⟫
      have hr : 0 < r := by
        dsimp [r]
        rw [real_inner_self_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hv)
      have hq : 0 ≤ q := by
        dsimp [q]
        exact quadraticAt_nonneg hA _
      let t : ℝ := r / (q + 1)
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hs : ⟪p - g x, t • (p - g x)⟫ = t * r := by
        calc
          ⟪p - g x, t • (p - g x)⟫ =
              t * ⟪p - g x, p - g x⟫ := by
                rw [real_inner_smul_right]
          _ = t * r := by rfl
      have hsmul (z : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
          ⟪s • z, T (s • z)⟫ = s ^ 2 * ⟪z, T z⟫ := by
        rw [map_smul]
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
      have hqs :
          ⟪t • (p - g x), T (t • (p - g x))⟫ =
            t ^ 2 * q := by
        rw [hsmul]
      have hi := hineq (t • (p - g x))
      rw [hs, hqs] at hi
      have htq : t * (q + 1) = r := by
        dsimp [t]
        exact div_mul_cancel₀ r (by positivity)
      nlinarith [sq_pos_of_pos ht, hr, hq, htq]
    exact sub_eq_zero.mp hv
  · intro hp y
    have hinc := quadraticAt_quadratic_expand hA.1 x₀ b c x (y - x)
    have harg : x + (y - x) = y := by
      abel
    rw [harg] at hinc
    rw [hp]
    nlinarith [quadraticAt_nonneg hA (y - x)]

private lemma quadraticAt_mix_identity {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (a r : ℝ) (har : a + r = 1) :
    quadraticAt A x₀ b c (a • x + r • y) =
      a * quadraticAt A x₀ b c x + r * quadraticAt A x₀ b c y -
        (1 / 2) * (a * r) *
          ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  have hr : r = 1 - a := by
    linarith
  have hcross (u v : EuclideanSpace ℝ (Fin n)) :
      ⟪v, T u⟫ = ⟪u, T v⟫ := by
    calc
      ⟪v, T u⟫ = ⟪T u, v⟫ := real_inner_comm _ _
      _ = ⟪u, T v⟫ := (quadraticAt_inner_symm hA.1 u v).symm
  have hquad (u v : EuclideanSpace ℝ (Fin n)) :
      ⟪a • u + r • v, T (a • u + r • v)⟫ =
        a * ⟪u, T u⟫ + r * ⟪v, T v⟫ -
          a * r * ⟪u - v, T (u - v)⟫ := by
    rw [hr]
    simp only [map_add, map_smul, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [hcross u v]
    ring
  have harg :
      a • x + r • y - x₀ = a • (x - x₀) + r • (y - x₀) := by
    calc
      a • x + r • y - x₀ =
          a • x + r • y - (a + r) • x₀ := by
            rw [har, one_smul]
      _ = a • (x - x₀) + r • (y - x₀) := by
        module
  have hdiff : (x - x₀) - (y - x₀) = x - y := by
    abel
  dsimp [quadraticAt]
  dsimp [T] at hquad ⊢
  rw [harg, hquad, hdiff]
  have hlin :
      ⟪b, a • (x - x₀) + r • (y - x₀)⟫ =
        a * ⟪b, x - x₀⟫ + r * ⟪b, y - x₀⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hlin, hr]
  ring

/-- A quadratic with positive semidefinite Hessian is convex. -/
theorem convexOn_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ConvexOn ℝ univ (quadraticAt A x₀ b c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a r ha hr har
  change quadraticAt A x₀ b c (a • x + r • y) ≤
    a * quadraticAt A x₀ b c x + r * quadraticAt A x₀ b c y
  rw [quadraticAt_mix_identity hA x₀ b c x y a r har]
  have hcoeff : 0 ≤ (1 / 2 : ℝ) * (a * r) := by
    positivity
  have hq :
      0 ≤ ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ :=
    quadraticAt_nonneg hA (x - y)
  have hprod :
      0 ≤ (1 / 2 : ℝ) * (a * r) *
        ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ :=
    mul_nonneg hcoeff hq
  nlinarith

private lemma volume_subgradientImage_quadraticAt_aux
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    {G : Set (EuclideanSpace ℝ (Fin n))} :
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (subgradientImage (quadraticAt A x₀ b c) G) =
      ENNReal.ofReal A.det *
        (volume : Measure (EuclideanSpace ℝ (Fin n))) G := by
  let E := EuclideanSpace ℝ (Fin n)
  let T : E →ₗ[ℝ] E := Matrix.toEuclideanLin A
  let g : E → E := fun x => b + T (x - x₀)
  have himage :
      subgradientImage (quadraticAt A x₀ b c) G = g '' G := by
    ext p
    constructor
    · rintro ⟨x, hx, hp⟩
      refine ⟨x, hx, ?_⟩
      have heq :=
        (quadraticAt_subgradient_iff hA.posSemidef x₀ b c x p).mp hp
      simpa [g] using heq.symm
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      apply (quadraticAt_subgradient_iff hA.posSemidef x₀ b c x (g x)).mpr
      rfl
  let d : E := b - T x₀
  have hg (x : E) : g x = d + T x := by
    dsimp [g, d]
    rw [map_sub]
    abel
  have haffine :
      g '' G = (fun z : E => d + z) '' (T '' G) := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨T x, ⟨x, hx, rfl⟩, ?_⟩
      exact (hg x).symm
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, hg x⟩
  have htrans :
      (volume : Measure E) ((fun z : E => d + z) '' (T '' G)) =
        (volume : Measure E) (T '' G) := by
    rw [image_add_left]
    exact measure_preimage_add volume (-d) (T '' G)
  have hdet : LinearMap.det T = A.det := by
    change LinearMap.det (Matrix.toLpLin 2 2 A) = A.det
    rw [Matrix.toLpLin_eq_toLin]
    exact LinearMap.det_toLin (PiLp.basisFun 2 ℝ (Fin n)) A
  have hdetpos : 0 < A.det := Matrix.PosDef.det_pos hA
  calc
    (volume : Measure E) (subgradientImage (quadraticAt A x₀ b c) G) =
        (volume : Measure E) (g '' G) := by rw [himage]
    _ = (volume : Measure E) ((fun z : E => d + z) '' (T '' G)) := by
      rw [haffine]
    _ = (volume : Measure E) (T '' G) := htrans
    _ = ENNReal.ofReal |LinearMap.det T| * (volume : Measure E) G :=
      Measure.addHaar_image_linearMap volume T G
    _ = ENNReal.ofReal A.det * (volume : Measure E) G := by
      rw [hdet, abs_of_pos hdetpos]

/-- **Subgradient images of a positive definite quadratic are exact affine images, with volume
`det A · vol G`** (weak Letwin route, N8). -/
theorem volume_subgradientImage_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) {G : Set (EuclideanSpace ℝ (Fin n))}
    (hG : MeasurableSet G) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage (quadraticAt A x₀ b c) G) =
      ENNReal.ofReal A.det * (volume : Measure (EuclideanSpace ℝ (Fin n))) G := by
  have _hG : MeasurableSet G := hG
  exact volume_subgradientImage_quadraticAt_aux hA x₀ b c

end FunctionalInequalities.Analysis

end LT12C1QuadraticSubgradientImage

section LT11E2InfdistLeWidth

open Set Metric
open scoped RealInnerProductSpace

/-! Distance to the frontier is bounded by the directional width (weak Letwin route, Caffarelli step G3, task L-T11e2). -/

namespace FunctionalInequalities.Analysis

/-- **Distance to the frontier is at most the width in any direction** (weak Letwin route, Caffarelli
block T11e, step G3): for a bounded open `S`, a point `x ∈ S` and a unit vector `θ`, if
`⟪y − x, θ⟫ ≤ t` for all `y ∈ S`, then `infDist x (frontier S) ≤ t`. -/
theorem infDist_frontier_le_of_forall_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {S : Set E} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {t : ℝ} (ht : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ t) :
    infDist x (frontier S) ≤ t := by
  have _ := hb
  have ht0 : 0 ≤ t := by
    simpa using ht x hx
  apply le_of_forall_pos_le_add
  intro η hη
  have ha0 : 0 ≤ t + η := add_nonneg ht0 (le_of_lt hη)
  have hz : x + (t + η) • θ ∉ S := by
    intro hzS
    have hle := ht (x + (t + η) • θ) hzS
    have heq : ⟪(x + (t + η) • θ) - x, θ⟫ = t + η := by
      simp only [add_sub_cancel_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        hθ, one_pow, mul_one]
    rw [heq] at hle
    linarith
  let f : ℝ → E := fun r => x + r • θ
  let T : Set E := f '' Icc 0 (t + η)
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hTpc : IsPreconnected T := by
    exact isPreconnected_Icc.image f hf.continuousOn
  have hxT : (T ∩ S).Nonempty := by
    refine ⟨x, ?_, hx⟩
    refine ⟨0, ⟨le_rfl, ha0⟩, ?_⟩
    simp [f]
  have hzT : x + (t + η) • θ ∈ T := by
    refine ⟨t + η, ⟨ha0, le_rfl⟩, ?_⟩
    rfl
  have hfront : (frontier S ∩ T).Nonempty := by
    by_contra hne
    have hclosure : closure S ∩ T ⊆ S := by
      intro y hy
      by_contra hys
      have hyf : y ∈ frontier S := by
        rw [hS.frontier_eq]
        exact ⟨hy.1, hys⟩
      exact hne ⟨y, hyf, hy.2⟩
    have hsub : T ⊆ S :=
      hTpc.subset_of_closure_inter_subset hS hxT hclosure
    exact hz (hsub hzT)
  rcases hfront with ⟨y, hyfront, hyT⟩
  rcases hyT with ⟨r, hr, rfl⟩
  change x + r • θ ∈ frontier S at hyfront
  calc
    infDist x (frontier S) ≤ dist x (x + r • θ) :=
      Metric.infDist_le_dist_of_mem hyfront
    _ = r := by
      rw [dist_self_add_right, norm_smul, Real.norm_eq_abs, hθ, mul_one,
        abs_of_nonneg hr.1]
    _ ≤ t + η := hr.2

end FunctionalInequalities.Analysis

end LT11E2InfdistLeWidth

section LT11E1AffineTransportSubgradientimage

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

/-! Subgradient images under affine changes of variables and their volume (task L-T11e1). -/

namespace FunctionalInequalities.Analysis

private lemma affineEquiv_linear_sub {E : Type*} [NormedAddCommGroup E]
    [Module ℝ E] (e : E ≃ᵃ[ℝ] E) (a b : E) :
    (e.linear : E →ₗ[ℝ] E) (a - b) = e a - e b := by
  change (AffineEquiv.toAffineMap e).linear (a - b) =
    (AffineEquiv.toAffineMap e) a - (AffineEquiv.toAffineMap e) b
  exact (AffineEquiv.toAffineMap e).linearMap_vsub a b

/-- **Affine transport of subgradient images** (weak Letwin route, Caffarelli block T11e, step G5):
under an affine equivalence `e` with linear part `T`, the subgradient image of `u ∘ e.symm` over
`e '' G` is the image of `∂u(G)` under the adjoint of `T⁻¹`. -/
theorem subgradientImage_comp_affineEquiv_symm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    subgradientImage (u ∘ e.symm) (e '' G) =
      (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) '' subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, hq⟩
    let p : E := LinearMap.adjoint (e.linear : E →ₗ[ℝ] E) q
    have hcomp :
        (e.linear : E →ₗ[ℝ] E) ∘ₗ (e.linear.symm : E →ₗ[ℝ] E) =
          LinearMap.id := by
      ext v
      simp
    have hadjcomp :
        LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) ∘ₗ
            LinearMap.adjoint (e.linear : E →ₗ[ℝ] E) =
          LinearMap.id := by
      calc
        LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) ∘ₗ
              LinearMap.adjoint (e.linear : E →ₗ[ℝ] E) =
            LinearMap.adjoint
              ((e.linear : E →ₗ[ℝ] E) ∘ₗ (e.linear.symm : E →ₗ[ℝ] E)) :=
          (LinearMap.adjoint_comp (e.linear : E →ₗ[ℝ] E)
            (e.linear.symm : E →ₗ[ℝ] E)).symm
        _ = LinearMap.adjoint LinearMap.id := by rw [hcomp]
        _ = LinearMap.id := LinearMap.adjoint_id
    have hadj :
        LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) p = q := by
      have h := congrArg (fun f : E →ₗ[ℝ] E => f q) hadjcomp
      simpa [p] using h
    have hp : p ∈ subgradientImage u G := by
      refine ⟨x, hx, ?_⟩
      intro y
      have hi :
          inner ℝ q (e y - e x) = inner ℝ p (y - x) := by
        calc
          inner ℝ q (e y - e x) =
              inner ℝ ((e.linear : E →ₗ[ℝ] E) (y - x)) q := by
            rw [affineEquiv_linear_sub e y x]
            exact (real_inner_comm q (e y - e x)).symm
          _ = inner ℝ (y - x) p := by
            simpa [p] using
              (LinearMap.adjoint_inner_right (e.linear : E →ₗ[ℝ] E) (y - x) q).symm
          _ = inner ℝ p (y - x) := real_inner_comm p (y - x)
      calc
        u x + inner ℝ p (y - x) =
            u x + inner ℝ q (e y - e x) := by rw [hi]
        _ ≤ u y := by
          simpa only [Function.comp_apply, e.symm_apply_apply] using hq (e y)
    refine ⟨p, hp, ?_⟩
    exact hadj
  · rintro ⟨p, hp, hpq⟩
    rcases hp with ⟨x, hx, hpx⟩
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hpq]
    intro z
    have hlin :
        (e.symm.linear : E →ₗ[ℝ] E) =
          (e.linear.symm : E →ₗ[ℝ] E) := by
      ext v
      simp
    have hv :
        (e.linear.symm : E →ₗ[ℝ] E) (z - e x) = e.symm z - x := by
      calc
        (e.linear.symm : E →ₗ[ℝ] E) (z - e x) =
            (e.symm.linear : E →ₗ[ℝ] E) (z - e x) := by
              rw [hlin]
        _ = e.symm z - e.symm (e x) :=
          affineEquiv_linear_sub e.symm z (e x)
        _ = e.symm z - x := by rw [e.symm_apply_apply]
    have hi :
        inner ℝ (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) p) (z - e x) =
          inner ℝ p (e.symm z - x) := by
      calc
        inner ℝ (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) p) (z - e x) =
            inner ℝ (z - e x)
              (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) p) := by
          rw [real_inner_comm]
        _ = inner ℝ ((e.linear.symm : E →ₗ[ℝ] E) (z - e x)) p :=
          LinearMap.adjoint_inner_right (e.linear.symm : E →ₗ[ℝ] E) (z - e x) p
        _ = inner ℝ (e.symm z - x) p := by rw [hv]
        _ = inner ℝ p (e.symm z - x) :=
          real_inner_comm p (e.symm z - x)
    simpa only [Function.comp_apply, e.symm_apply_apply, hi] using hpx (e.symm z)

/-- The volume of the transported subgradient image is `vol (∂u(G)) / |det T|`. -/
theorem volume_subgradientImage_comp_affineEquiv_symm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    (volume : Measure E) (subgradientImage (u ∘ e.symm) (e '' G)) =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
        (volume : Measure E) (subgradientImage u G) := by
  let b := stdOrthonormalBasis ℝ E
  have hdetadj :
      LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) =
        LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) := by
    calc
      LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) =
          (LinearMap.toMatrix b.toBasis b.toBasis
            (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))).det :=
        (LinearMap.det_toMatrix b.toBasis
          (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))).symm
      _ = (LinearMap.toMatrix b.toBasis b.toBasis
            (e.linear.symm : E →ₗ[ℝ] E)).conjTranspose.det := by
        rw [LinearMap.toMatrix_adjoint b b]
      _ = (LinearMap.toMatrix b.toBasis b.toBasis
            (e.linear.symm : E →ₗ[ℝ] E)).det := by
        rw [Matrix.det_conjTranspose]
        simp
      _ = LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) :=
        LinearMap.det_toMatrix b.toBasis (e.linear.symm : E →ₗ[ℝ] E)
  have hcomp :
      (e.linear.symm : E →ₗ[ℝ] E) ∘ₗ (e.linear : E →ₗ[ℝ] E) =
        LinearMap.id := by
    ext v
    simp
  have hprod :
      LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
          LinearMap.det (e.linear : E →ₗ[ℝ] E) = 1 := by
    calc
      LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
          LinearMap.det (e.linear : E →ₗ[ℝ] E) =
          LinearMap.det
            ((e.linear.symm : E →ₗ[ℝ] E) ∘ₗ (e.linear : E →ₗ[ℝ] E)) :=
        (LinearMap.det_comp (e.linear.symm : E →ₗ[ℝ] E)
          (e.linear : E →ₗ[ℝ] E)).symm
      _ = LinearMap.det LinearMap.id := by rw [hcomp]
      _ = 1 := LinearMap.det_id
  have hdet_ne :
      LinearMap.det (e.linear : E →ₗ[ℝ] E) ≠ 0 := by
    intro hzero
    have hbad : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) =
            LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
              LinearMap.det (e.linear : E →ₗ[ℝ] E) := hprod.symm
        _ = 0 := by rw [hzero]; simp
    exact zero_ne_one hbad.symm
  have hdet_symm :
      LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) =
        (LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹ := by
    calc
      LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) =
          LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) * 1 := by simp
      _ = LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
          (LinearMap.det (e.linear : E →ₗ[ℝ] E) *
            (LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹) := by
        rw [mul_inv_cancel₀ hdet_ne]
      _ = (LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) *
          LinearMap.det (e.linear : E →ₗ[ℝ] E)) *
            (LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹ := by ring
      _ = (LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹ := by
        rw [hprod]
        simp
  have hdetabs :
      |LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))| =
        |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ := by
    calc
      |LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))| =
          |LinearMap.det (e.linear.symm : E →ₗ[ℝ] E)| :=
        congrArg abs hdetadj
      _ = |(LinearMap.det (e.linear : E →ₗ[ℝ] E))⁻¹| :=
        congrArg abs hdet_symm
      _ = |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ :=
        abs_inv _
  rw [subgradientImage_comp_affineEquiv_symm]
  rw [MeasureTheory.Measure.addHaar_image_linearMap]
  rw [hdetabs]

end FunctionalInequalities.Analysis

end LT11E1AffineTransportSubgradientimage

section LT11E4NormalizedMinEstimate

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-! Minimum estimate for a normalized convex function from a lower Alexandrov bound (task L-T11e4). -/

namespace FunctionalInequalities.Analysis

/-- **Minimum estimate on a normalised section by quadratic comparison** (weak Letwin route, Caffarelli
block T11e, step (b); Gutiérrez Lemma via the comparison with `½κ(‖x‖² − 1)`): if `v` is convex, `≤ 0` on
the frontier of a bounded open `S ⊇ closedBall 0 1`, and `a · vol G ≤ vol ∂v(G)` for open `G ⊆ S`, then
`v 0 ≤ −½ (a/2)^{1/n}`. -/
theorem le_neg_of_lower_alexandrov_bound {n : ℕ} (hn : 0 < n) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ v) {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsOpen S)
    (hb : Bornology.IsBounded S) (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ S)
    (hfr : ∀ x ∈ frontier S, v x ≤ 0) {a : ℝ} (ha : 0 < a)
    (hA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ S →
      ENNReal.ofReal a * (volume : Measure (EuclideanSpace ℝ (Fin n))) G ≤
        (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage v G)) :
    v 0 ≤ -(1 / 2) * (a / 2) ^ (1 / (n : ℝ)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let κ : ℝ := (a / 2) ^ (1 / (n : ℝ))
  let M : Matrix (Fin n) (Fin n) ℝ := κ • (1 : Matrix (Fin n) (Fin n) ℝ)
  let w : E → ℝ := quadraticAt M 0 0 (-κ / 2)
  have hκ : 0 < κ := by
    dsimp [κ]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hκpow : κ ^ n = a / 2 := by
    dsimp [κ]
    simpa only [one_div] using
      (Real.rpow_inv_natCast_pow (show 0 ≤ a / 2 by positivity) (Nat.ne_of_gt hn))
  have hMpos : M.PosDef := by
    dsimp [M]
    exact Matrix.PosDef.one.smul hκ
  have hMdet : M.det = κ ^ n := by
    dsimp [M]
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hMaction (x : E) :
      Matrix.toEuclideanLin M x = κ • x := by
    change Matrix.toLpLin 2 2 (κ • (1 : Matrix (Fin n) (Fin n) ℝ)) x = κ • x
    rw [map_smul, Matrix.toLpLin_one]
    simp
  have hwformula (x : E) :
      w x = (κ / 2) * (‖x‖ ^ 2 - 1) := by
    dsimp [w, quadraticAt]
    rw [hMaction]
    simp only [sub_zero, inner_zero_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  have hvc : Continuous v := by
    apply continuousOn_univ.mp
    exact hconv.continuousOn isOpen_univ
  have hwconv : ConvexOn ℝ univ w := by
    dsimp [w]
    exact convexOn_quadraticAt hMpos.posSemidef 0 0 (-κ / 2)
  have hwc : Continuous w := by
    apply continuousOn_univ.mp
    exact hwconv.continuousOn isOpen_univ
  have hwfront : ∀ x ∈ frontier S, 0 < w x := by
    intro x hx
    have hxnotS : x ∉ S := by
      rw [hS.frontier_eq] at hx
      exact fun hxs => hx.2 hxs
    have hnorm : 1 < ‖x‖ := by
      apply lt_of_not_ge
      intro hle
      apply hxnotS
      apply hball
      simpa [mem_closedBall, dist_zero_right] using hle
    have hsq : 0 < ‖x‖ ^ 2 - 1 := by
      nlinarith [norm_nonneg x]
    rw [hwformula]
    exact mul_pos (half_pos hκ) hsq
  let G : Set E := S ∩ {x | w x < v x}
  have hGopen : IsOpen G := by
    dsimp [G]
    exact hS.inter (isOpen_lt hwc hvc)
  have hGsub : G ⊆ S := by
    intro x hx
    exact hx.1
  have hGb : Bornology.IsBounded G := hb.subset hGsub
  have hGeq : ∀ x ∈ frontier G, w x = v x := by
    intro x hx
    have hxclG : x ∈ closure G := frontier_subset_closure hx
    have hxclS : x ∈ closure S := closure_mono hGsub hxclG
    have hle : w x ≤ v x := by
      apply closure_minimal
        (s := G) (t := {y | w y ≤ v y}) ?_ (isClosed_le hwc hvc) hxclG
      intro y hy
      change w y ≤ v y
      exact le_of_lt (show w y < v y from hy.2)
    by_cases hxs : x ∈ S
    · have hxnotG : x ∉ G := by
        have hx' := hx
        rw [hGopen.frontier_eq] at hx'
        exact fun hxg => hx'.2 hxg
      apply le_antisymm hle
      exact le_of_not_gt (fun hlt => hxnotG ⟨hxs, hlt⟩)
    · have hxf : x ∈ frontier S := by
        rw [hS.frontier_eq]
        exact ⟨hxclS, hxs⟩
      exfalso
      linarith [hfr x hxf, hwfront x hxf]
  have hGempty : G = ∅ := by
    by_contra hGne
    have hGnonempty : G.Nonempty := nonempty_iff_ne_empty.mpr hGne
    have hGpos : 0 < (volume : Measure E) G :=
      IsOpen.measure_pos volume hGopen hGnonempty
    have hGtop : (volume : Measure E) G < ∞ := hGb.measure_lt_top
    have hcomp : subgradientImage v G ⊆ subgradientImage w G :=
      subgradientImage_subset_of_le hwconv hconv hGopen hGb
        (fun x hx => le_of_lt hx.2) hGeq
    have hmul :
        ENNReal.ofReal a * (volume : Measure E) G ≤
          ENNReal.ofReal M.det * (volume : Measure E) G := by
      calc
        ENNReal.ofReal a * (volume : Measure E) G ≤
            (volume : Measure E) (subgradientImage v G) :=
          hA G hGopen hGsub
        _ ≤ (volume : Measure E) (subgradientImage w G) :=
          measure_mono hcomp
        _ = ENNReal.ofReal M.det * (volume : Measure E) G :=
          volume_subgradientImage_quadraticAt hMpos 0 0 (-κ / 2) hGopen.measurableSet
    have hcoef : ENNReal.ofReal a ≤ ENNReal.ofReal M.det := by
      exact
        (ENNReal.mul_le_mul_iff_right
          (a := (volume : Measure E) G) (ne_of_gt hGpos) (ne_of_lt hGtop)).mp
          (by simpa [mul_comm] using hmul)
    have hreal : a ≤ M.det :=
      (ENNReal.ofReal_le_ofReal_iff hMpos.det_pos.le).mp hcoef
    rw [hMdet, hκpow] at hreal
    linarith
  have hvw : ∀ x ∈ S, v x ≤ w x := by
    intro x hxs
    by_contra hnot
    have hlt : w x < v x := lt_of_not_ge hnot
    have hxg : x ∈ G := ⟨hxs, hlt⟩
    rw [hGempty] at hxg
    exact hxg
  have hzeroS : (0 : E) ∈ S := by
    apply hball
    simp [mem_closedBall]
  calc
    v 0 ≤ w 0 := hvw 0 hzeroS
    _ = -(1 / 2) * (a / 2) ^ (1 / (n : ℝ)) := by
      rw [hwformula]
      dsimp [κ]
      simp
      ring

end FunctionalInequalities.Analysis

end LT11E4NormalizedMinEstimate

section LT11E6SubgradientimageSubAffine

open MeasureTheory Set
open scoped RealInnerProductSpace

/-! Subgradient images after subtracting an affine function, and their volume (task L-T11e6). -/

namespace FunctionalInequalities.Analysis

/-- **Subtracting an affine function translates subgradient images** (weak Letwin route, Caffarelli
block T11e, bookkeeping): `∂(u − ⟪p, ·⟫ − c)(G) = ∂u(G) − p`, hence the volumes agree. -/
theorem subgradientImage_sub_inner_add_const {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : E → ℝ) (p : E) (c : ℝ) (G : Set E) :
    subgradientImage (fun x => u x - (⟪p, x⟫ + c)) G = (fun q => q - p) '' subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨q + p, ?_, add_sub_cancel_right q p⟩
    refine ⟨x, hx, ?_⟩
    intro y
    have h := hq y
    simp only [inner_sub_right] at h
    simp only [inner_add_left, inner_sub_right]
    linarith
  · rintro ⟨r, ⟨x, hx, hr⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    intro y
    have h := hr y
    simp only [inner_sub_right] at h
    simp only [inner_sub_left, inner_sub_right]
    linarith

theorem volume_subgradientImage_sub_inner_add_const {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (p : E) (c : ℝ) (G : Set E) :
    (volume : Measure E) (subgradientImage (fun x => u x - (⟪p, x⟫ + c)) G) =
      (volume : Measure E) (subgradientImage u G) := by
  rw [subgradientImage_sub_inner_add_const]
  simp only [sub_eq_add_neg, Set.image_add_right, neg_neg]
  exact measure_preimage_add_right (volume : Measure E) p (subgradientImage u G)

end FunctionalInequalities.Analysis

end LT11E6SubgradientimageSubAffine

section LT14DAlexandrovIdentityOpen

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

/-! The Alexandrov identity on open sets: the volume of the subgradient image equals the integral of the Monge–Ampère density (task L-T14d). -/

namespace FunctionalInequalities.Analysis

private lemma t14d_isClosed_subgradientImage {E : Type*} [NormedAddCommGroup E]
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

/-- **Alexandrov identity on open sets for the moment potential** (weak Letwin route, N5/N8, task T14d):
if `u` is convex, Lipschitz, `ν = e^{-u} dx` is normalised and `ν.map ∇u = μ = 1_K e^{-V} dx` for a closed convex
`K` and a measurable `V`, then the subgradient image of every open `G` has volume `∫_G e^{-u + V(∇u)}`. -/
theorem volume_subgradientImage_eq_lintegral_of_isOpen {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K) {V : E → ℝ} (hV : Measurable V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    {G : Set E} (hG : IsOpen G) :
    (volume : Measure E) (subgradientImage u G) =
      ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + V (gradient u x))) ∂(volume : Measure E) := by
  classical
  let ρ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-u x))
  let f : E → ℝ≥0∞ := K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))
  let g : E → ℝ≥0∞ := K.indicator fun p => ENNReal.ofReal (Real.exp (V p))
  let F : E → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-u x + V (gradient u x)))
  have hρ : Measurable ρ := hu.continuous.measurable.neg.exp.ennreal_ofReal
  have hf : Measurable f :=
    hV.neg.exp.ennreal_ofReal.indicator hK.measurableSet
  have hg : Measurable g :=
    hV.exp.ennreal_ofReal.indicator hK.measurableSet
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have htilt : (volume : Measure E).tilted (-u) = volume.withDensity ρ := by
    change (volume : Measure E).withDensity
      (fun x => ENNReal.ofReal
        (Real.exp (-u x) / ∫ y, Real.exp (-u y) ∂(volume : Measure E))) =
      volume.withDensity ρ
    simp only [hnorm, div_one, ρ]
  have hmap' :
      ((volume : Measure E).withDensity ρ).map (gradient u) =
        volume.withDensity f := by
    rw [← htilt]
    exact hmap
  have hμK : ∀ᵐ p ∂(volume : Measure E).withDensity f, p ∈ K := by
    apply (ae_withDensity_iff hf).2
    exact Filter.Eventually.of_forall fun p hp => by
      by_contra h
      exact hp (Set.indicator_of_notMem h _)
  have hνK :
      ∀ᵐ x ∂(volume : Measure E).withDensity ρ, gradient u x ∈ K := by
    apply ae_of_ae_map hgrad.aemeasurable
    rw [hmap']
    exact hμK
  have hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K := by
    have h := (ae_withDensity_iff hρ).1 hνK
    filter_upwards [h] with x hx
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-u x))))
  have hsub (S : Set E) : subgradientImage u S ⊆ K := by
    rintro p ⟨x, _, hp⟩
    exact subgradient_mem_of_ae_gradient_mem hu hconv hK hKc hae hp
  have hcancel (p : E) (hp : p ∈ K) : (f * g) p = 1 := by
    change
      (K.indicator (fun q => ENNReal.ofReal (Real.exp (-V q))) p) *
        (K.indicator (fun q => ENNReal.ofReal (Real.exp (V q))) p) = 1
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  have hprod :
      (fun x => (ρ * (g ∘ gradient u)) x) =ᵐ[volume] F := by
    filter_upwards [hae] with x hx
    change ENNReal.ofReal (Real.exp (-u x)) *
      (K.indicator (fun p => ENNReal.ofReal (Real.exp (V p))) (gradient u x)) =
        ENNReal.ofReal (Real.exp (-u x + V (gradient u x)))
    rw [Set.indicator_of_mem hx,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  have hcompact {S : Set E} (hS : IsCompact S) :
      (volume : Measure E) (subgradientImage u S) =
        ((volume : Measure E).withDensity F) S := by
    have hT : MeasurableSet (subgradientImage u S) :=
      (t14d_isClosed_subgradientImage hu.continuous hS).measurableSet
    have hleft :
        ∫⁻ p in subgradientImage u S, g p ∂(volume : Measure E).withDensity f =
          (volume : Measure E) (subgradientImage u S) := by
      calc
        ∫⁻ p in subgradientImage u S, g p ∂(volume : Measure E).withDensity f =
            ∫⁻ p in subgradientImage u S, (f * g) p ∂(volume : Measure E) :=
          setLIntegral_withDensity_eq_setLIntegral_mul volume hf hg hT
        _ = ∫⁻ p in subgradientImage u S, 1 ∂(volume : Measure E) :=
          setLIntegral_congr_fun hT fun p hp => hcancel p (hsub S hp)
        _ = (volume : Measure E) (subgradientImage u S) := by
          rw [lintegral_one, Measure.restrict_apply_univ]
    calc
      (volume : Measure E) (subgradientImage u S) =
          ∫⁻ p in subgradientImage u S, g p ∂(volume : Measure E).withDensity f :=
        hleft.symm
      _ = ∫⁻ x in S, g (gradient u x) ∂(volume : Measure E).withDensity ρ :=
        lintegral_subgradientImage_eq_of_map_gradient hu hconv
          (withDensity_absolutelyContinuous volume ρ) hmap'
          (withDensity_absolutelyContinuous volume f) hS g hg
      _ = ∫⁻ x in S, (ρ * (g ∘ gradient u)) x ∂(volume : Measure E) :=
        setLIntegral_withDensity_eq_setLIntegral_mul volume hρ
          (hg.comp hgrad) hS.measurableSet
      _ = ∫⁻ x in S, F x ∂(volume : Measure E) :=
        lintegral_congr_ae (ae_restrict_of_ae hprod)
      _ = ((volume : Measure E).withDensity F) S :=
        (withDensity_apply F hS.measurableSet).symm
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let S : ℕ → Set E := fun n => Subtype.val '' compactCovering G n
  have hScompact (n : ℕ) : IsCompact (S n) :=
    (isCompact_compactCovering G n).image continuous_subtype_val
  have hSmono : Monotone S := fun _ _ hij =>
    Set.image_mono (compactCovering_subset G hij)
  have hSunion : (⋃ n, S n) = G := by
    change (⋃ n, Subtype.val '' compactCovering G n) = G
    rw [← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe]
  have hTmono : Monotone (fun n => subgradientImage u (S n)) := by
    intro i j hij p hp
    rcases hp with ⟨x, hx, hp⟩
    exact ⟨x, hSmono hij hx, hp⟩
  have hTunion : subgradientImage u G = ⋃ n, subgradientImage u (S n) := by
    rw [← hSunion]
    ext p
    constructor
    · rintro ⟨x, hx, hp⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n, x, hn, hp⟩
    · intro hp
      obtain ⟨n, x, hx, hp⟩ := mem_iUnion.mp hp
      exact ⟨x, mem_iUnion.mpr ⟨n, hx⟩, hp⟩
  calc
    (volume : Measure E) (subgradientImage u G) =
        (volume : Measure E) (⋃ n, subgradientImage u (S n)) := by
      rw [hTunion]
    _ = ⨆ n, (volume : Measure E) (subgradientImage u (S n)) :=
      hTmono.measure_iUnion
    _ = ⨆ n, ((volume : Measure E).withDensity F) (S n) := by
      congr 1
      funext n
      exact hcompact (hScompact n)
    _ = ((volume : Measure E).withDensity F) (⋃ n, S n) :=
      hSmono.measure_iUnion.symm
    _ = ((volume : Measure E).withDensity F) G := by rw [hSunion]
    _ = ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + V (gradient u x)))
        ∂(volume : Measure E) :=
      withDensity_apply F hG.measurableSet

end FunctionalInequalities.Analysis

end LT14DAlexandrovIdentityOpen

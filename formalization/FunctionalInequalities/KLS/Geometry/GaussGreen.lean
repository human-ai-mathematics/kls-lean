import FunctionalInequalities.KLS.Geometry.LocalGaussGreen
import FunctionalInequalities.Analysis.PartitionOfUnity
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Gauss–Green theorem for a smooth domain

Application layer: the chart-local identity of `KLS/Geometry/LocalGaussGreen.lean`, the
divergence-free identity `Analysis.integral_divergence_eq_zero` of
`Analysis/SubgraphDivergence.lean` and the finite smooth decomposition of
`Analysis/PartitionOfUnity.lean`, glued into the global statement.  Every statement here is proved
and uses only the standard axioms; the module contains **no** `sorry`.

## The statement

`SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal`: for a smooth domain `U` in a
finite-dimensional real inner-product space `V` and a compactly supported `C¹` vector field `F`,

  `∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n-1}`,

with the normalized surface measure `KLS.surfaceMeasure` and the outward unit normal
`SmoothDomain.outwardNormal`.  Neither `U` nor `∂U` is assumed bounded, `∂U` is not assumed to have
finite total surface measure, `F` is not assumed smoother than `C¹`, and `V` is not assumed
nontrivial.

## The three kinds of local block

The compact set `K = tsupport F` is covered by three families of **open** sets, and it takes all
three: the support of `F` may lie entirely inside `U`, entirely outside `closure U`, or straddle
the boundary.

* **Boundary cylinders.**  For every frontier point `z` the chart of
  `SmoothDomain.exists_boundaryChart` provides an open cylinder containing `z`
  (`BoundaryChart.self_mem_cylinder`).  A piece supported there is handled by the chart-local
  Gauss–Green identity.
* **The domain `U` itself.**  A piece supported inside the open set `U` has both `F` and `div F`
  vanishing outside `U`, so its volume integral is the integral over the *whole* space, which is
  zero by `Analysis.integral_divergence_eq_zero`; and its flux vanishes because `∂U` is disjoint
  from `U`.
* **The complement of `closure U`.**  A piece supported there vanishes on `U` and on `∂U`, so both
  sides are zero.

Since `V = U ⊔ ∂U ⊔ (closure U)ᶜ` for an open `U`, these three families cover `K`, and
`Analysis.exists_finset_sum_eq_of_isOpen_cover` turns the cover into a **finite** family `G i` of
compactly supported `C¹` fields with `tsupport (G i)` inside the corresponding open set and
`F = ∑ i ∈ s, G i` as an identity of functions on all of `V`.  The identity is global, so it may
be differentiated: `Analysis.divergence_finset_sum` splits `div F` and `sum_inner` splits the flux
integrand, with no partition-derivative terms left to cancel.

## Integrability, not assumption

Every exchange of a finite sum with an integral is justified, never assumed.

* `div (G i)` is continuous (`Analysis.continuous_divergence`) with compact support
  (`Analysis.hasCompactSupport_divergence`), hence integrable on `U` for Lebesgue measure.
* `⟪G i, ν⟫` is integrable on `∂U` for the surface measure by `integrableOn_inner_outwardNormal`,
  which uses only `‖ν‖ ≤ 1`, the measurability of `ν` and the local finiteness of the restricted
  surface measure (`isLocallyFiniteMeasure_surfaceMeasure_frontier`).  No global bound on
  `surfaceMeasure (∂U)` is used, so an unbounded frontier of infinite total measure stays in scope.

## Migration

`isLocallyFiniteMeasure_surfaceMeasure_frontier` and `integrableOn_smul_outwardNormal` were proved
in `KLS/WIP/AnalyticPrerequisites.lean`; they move here unchanged (same namespace, same names,
same statements — no alias, no duplicate, no forwarding declaration) together with the theorem they
support. The scalar test-function consequence also lives here; the mollified gradient formula
and its norm bound live above this module in `Geometry/MollifiedBoundary.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FunctionalInequalities

universe u

namespace KLS.SmoothDomain

section GaussGreen

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

set_option linter.unusedSectionVars false in
/-- The normalized surface measure restricted to a smooth frontier is locally finite,
including for unbounded domains and in dimension zero. -/
theorem isLocallyFiniteMeasure_surfaceMeasure_frontier (U : SmoothDomain V) :
    IsLocallyFiniteMeasure ((surfaceMeasure V).restrict (frontier U.carrier)) := by
  have hfrmeas : MeasurableSet (frontier U.carrier) := isClosed_frontier.measurableSet
  constructor
  intro x
  by_cases hx : x ∈ frontier U.carrier
  · -- A nonempty frontier forces a positive dimension, so `n - 1` is the honest exponent.
    have hpos : 1 ≤ Module.finrank ℝ V := by
      by_contra hcon
      have h0 : Module.finrank ℝ V = 0 := by omega
      have hss : Subsingleton V := Module.finrank_zero_iff.mp h0
      have hemp : frontier U.carrier = ∅ := by
        rcases Set.eq_empty_or_nonempty U.carrier with he | hne
        · rw [he, frontier_empty]
        · rw [Subsingleton.eq_univ_of_nonempty hne, frontier_univ]
      rw [hemp] at hx
      exact hx
    have hcast : ((Module.finrank ℝ V - 1 : ℕ) : ℝ) = (Module.finrank ℝ V : ℝ) - 1 := by
      rw [Nat.cast_sub hpos, Nat.cast_one]
    obtain ⟨W, φ, hW, hxW, hφ, hφ', hU⟩ := U.exists_defining x hx
    obtain ⟨N, hN, hNfin⟩ := Analysis.exists_hausdorffMeasure_levelSet_lt_top
      (hφ.of_le (by simp)) (hφ' x hxW)
    refine ⟨N ∩ W, Filter.inter_mem hN (hW.mem_nhds hxW), ?_⟩
    have hsub : N ∩ W ∩ frontier U.carrier ⊆ N ∩ {y | φ y = φ x} := by
      have hfr := U.frontier_inter_eq hW hφ hφ' hU
      have hφx : φ x = 0 := by
        have hmem : x ∈ {y ∈ W | φ y = 0} := by rw [← hfr]; exact ⟨hx, hxW⟩
        exact hmem.2
      rintro y ⟨⟨hyN, hyW⟩, hyfr⟩
      have hmem : y ∈ {y ∈ W | φ y = 0} := by rw [← hfr]; exact ⟨hyfr, hyW⟩
      exact ⟨hyN, by simp only [Set.mem_ofPred_eq, hφx]; exact hmem.2⟩
    rw [Measure.restrict_apply' hfrmeas, surfaceMeasure, hausdorffNormalized,
      Measure.smul_apply, smul_eq_mul, hcast]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (measure_mono hsub) hNfin)
  · refine ⟨(frontier U.carrier)ᶜ, isClosed_frontier.isOpen_compl.mem_nhds hx, ?_⟩
    rw [Measure.restrict_apply' hfrmeas, Set.compl_inter_self]
    simp

/-- A continuous compactly supported scalar test times the outward unit normal is integrable
on the frontier with respect to the normalized surface measure. -/
theorem integrableOn_smul_outwardNormal (U : SmoothDomain V) {η : V → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η) :
    IntegrableOn (fun x ↦ η x • U.outwardNormal x) (frontier U.carrier)
      (surfaceMeasure V) := by
  have hloc := U.isLocallyFiniteMeasure_surfaceMeasure_frontier
  set μ : Measure V := (surfaceMeasure V).restrict (frontier U.carrier)
  have hint : Integrable η μ := hη.integrable_of_hasCompactSupport hηc
  have hmeas : AEStronglyMeasurable (fun x => η x • U.outwardNormal x) μ :=
    (hη.measurable.smul U.measurable_outwardNormal).aestronglyMeasurable
  have hnorm : ∀ x : V, ‖η x • U.outwardNormal x‖ ≤ ‖η x‖ := by
    intro x
    rw [norm_smul]
    by_cases hx : x ∈ frontier U.carrier
    · rw [U.norm_outwardNormal hx, mul_one]
    · rw [outwardNormal, dif_neg hx]
      simp
  exact hint.mono hmeas (Eventually.of_forall hnorm)

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-- The outward normal is a contraction everywhere: a unit vector on the frontier and zero off
it. -/
theorem norm_outwardNormal_le_one (U : SmoothDomain V) (x : V) : ‖U.outwardNormal x‖ ≤ 1 := by
  by_cases hx : x ∈ frontier U.carrier
  · rw [U.norm_outwardNormal hx]
  · rw [outwardNormal, dif_neg hx]
    simp

/-- The flux integrand of a continuous compactly supported vector field is integrable on the
frontier with respect to the normalized surface measure.  Only `‖ν‖ ≤ 1`, the measurability of `ν`
and the local finiteness of the restricted surface measure are used; the total surface measure of
the frontier may be infinite. -/
theorem integrableOn_inner_outwardNormal (U : SmoothDomain V) {G : V → V}
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    IntegrableOn (fun x ↦ (⟪G x, U.outwardNormal x⟫ : ℝ)) (frontier U.carrier)
      (surfaceMeasure V) := by
  have hloc := U.isLocallyFiniteMeasure_surfaceMeasure_frontier
  set μ : Measure V := (surfaceMeasure V).restrict (frontier U.carrier)
  have hint : Integrable (fun x => ‖G x‖) μ :=
    hG.norm.integrable_of_hasCompactSupport hGc.norm
  have hmeas : AEStronglyMeasurable (fun x => (⟪G x, U.outwardNormal x⟫ : ℝ)) μ :=
    (Measurable.inner (𝕜 := ℝ) hG.measurable U.measurable_outwardNormal).aestronglyMeasurable
  refine hint.mono hmeas (Eventually.of_forall fun x => ?_)
  calc ‖(⟪G x, U.outwardNormal x⟫ : ℝ)‖ ≤ ‖G x‖ * ‖U.outwardNormal x‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖G x‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (U.norm_outwardNormal_le_one x) (norm_nonneg _)
    _ = ‖‖G x‖‖ := by rw [mul_one, norm_norm]

/-! ### The three kinds of local block -/

/-- **Interior block.**  A compactly supported `C¹` field whose closed support lies inside the
domain has no flux through the frontier, and its divergence integrates to zero over the domain
because it integrates to zero over the whole space. -/
theorem integral_divergence_eq_integral_inner_outwardNormal_of_tsupport_subset_carrier
    (U : SmoothDomain V) {G : V → V} (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G)
    (hsupp : tsupport G ⊆ U.carrier) :
    ∫ x in U.carrier, Analysis.divergence G x
      = ∫ x in frontier U.carrier, (⟪G x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V) := by
  have hL : ∫ x in U.carrier, Analysis.divergence G x = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => Analysis.divergence_eq_zero_of_notMem_tsupport fun h => hx (hsupp h))]
    exact Analysis.integral_divergence_eq_zero hG hGc
  have hR : ∫ x in frontier U.carrier, (⟪G x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V) = 0 := by
    rw [setIntegral_congr_fun (f := fun x => (⟪G x, U.outwardNormal x⟫ : ℝ)) (g := fun _ => (0 : ℝ))
      isClosed_frontier.measurableSet fun x hx => ?_, integral_zero]
    have hxU : x ∉ U.carrier := by
      have h := hx.2
      rwa [U.isOpen.interior_eq] at h
    show (⟪G x, U.outwardNormal x⟫ : ℝ) = 0
    rw [image_eq_zero_of_notMem_tsupport fun h => hxU (hsupp h), inner_zero_left]
  rw [hL, hR]

/-- **Exterior block.**  A compactly supported field whose closed support avoids `closure U`
contributes nothing to either side. -/
theorem integral_divergence_eq_integral_inner_outwardNormal_of_tsupport_subset_compl_closure
    (U : SmoothDomain V) {G : V → V} (hsupp : tsupport G ⊆ (closure U.carrier)ᶜ) :
    ∫ x in U.carrier, Analysis.divergence G x
      = ∫ x in frontier U.carrier, (⟪G x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V) := by
  have hout : ∀ x ∈ closure U.carrier, x ∉ tsupport G := fun x hx h => hsupp h hx
  have hL : ∫ x in U.carrier, Analysis.divergence G x = 0 := by
    rw [setIntegral_congr_fun (f := Analysis.divergence G) (g := fun _ => (0 : ℝ))
      U.measurableSet fun x hx => ?_, integral_zero]
    show Analysis.divergence G x = 0
    exact Analysis.divergence_eq_zero_of_notMem_tsupport (hout x (subset_closure hx))
  have hR : ∫ x in frontier U.carrier, (⟪G x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V) = 0 := by
    rw [setIntegral_congr_fun (f := fun x => (⟪G x, U.outwardNormal x⟫ : ℝ)) (g := fun _ => (0 : ℝ))
      isClosed_frontier.measurableSet fun x hx => ?_, integral_zero]
    show (⟪G x, U.outwardNormal x⟫ : ℝ) = 0
    rw [image_eq_zero_of_notMem_tsupport (hout x (frontier_subset_closure hx)), inner_zero_left]
  rw [hL, hR]

/-! ### The global theorem -/

/-- **Gauss–Green theorem** for a smooth domain and a compactly supported `C¹` vector field:
`∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n-1}`, with the normalized surface measure and the outward unit
normal.  Neither the domain nor its frontier is assumed bounded. -/
theorem integral_divergence_eq_integral_inner_outwardNormal (U : SmoothDomain V) {F : V → V}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ∫ x in U.carrier, Analysis.divergence F x =
      ∫ x in frontier U.carrier, ⟪F x, U.outwardNormal x⟫ ∂(surfaceMeasure V) := by
  classical
  -- the open cover of the compact support: one cylinder per frontier point, the domain, and the
  -- complement of its closure
  set chartOf : ∀ z : (frontier U.carrier : Set V), U.BoundaryChart (z : V) :=
    fun z => Classical.choice (U.exists_boundaryChart z.2) with hchartOf
  set cover : Bool ⊕ (frontier U.carrier : Set V) → Set V :=
    Sum.elim (fun b => cond b U.carrier (closure U.carrier)ᶜ)
      (fun z => (chartOf z).cylinder) with hcoverdef
  have hopen : ∀ i, IsOpen (cover i) := by
    rintro (b | z)
    · cases b
      · exact isClosed_closure.isOpen_compl
      · exact U.isOpen
    · exact (chartOf z).isOpen_cylinder
  have hsub : tsupport F ⊆ ⋃ i, cover i := by
    intro x _
    by_cases hxU : x ∈ U.carrier
    · exact Set.mem_iUnion.mpr ⟨Sum.inl true, hxU⟩
    · by_cases hxfr : x ∈ frontier U.carrier
      · exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨x, hxfr⟩, (chartOf ⟨x, hxfr⟩).self_mem_cylinder⟩
      · refine Set.mem_iUnion.mpr ⟨Sum.inl false, ?_⟩
        intro hxcl
        exact hxfr ⟨hxcl, by rwa [U.isOpen.interior_eq]⟩
  obtain ⟨s, G, hGcd, hGcs, hGts, hGsum⟩ :=
    Analysis.exists_finset_sum_eq_of_isOpen_cover (n := 1) (by exact_mod_cast hF) hFc hopen hsub
  have hFeq : F = fun x => ∑ i ∈ s, G i x := funext fun x => (hGsum x).symm
  have hGcd' : ∀ i, ContDiff ℝ 1 (G i) := fun i => by exact_mod_cast hGcd i
  -- integrability of every piece on both sides
  have hvol : ∀ i, IntegrableOn (Analysis.divergence (G i)) U.carrier volume := fun i =>
    ((Analysis.continuous_divergence (hGcd' i)).integrable_of_hasCompactSupport
      (Analysis.hasCompactSupport_divergence (hGcs i))).integrableOn
  have hbd : ∀ i, IntegrableOn (fun x => (⟪G i x, U.outwardNormal x⟫ : ℝ)) (frontier U.carrier)
      (surfaceMeasure V) := fun i =>
    U.integrableOn_inner_outwardNormal ((hGcd' i).continuous) (hGcs i)
  -- the three kinds of local block
  have hblock : ∀ i, ∫ x in U.carrier, Analysis.divergence (G i) x
      = ∫ x in frontier U.carrier, (⟪G i x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V) := by
    rintro (b | z)
    · cases b
      · exact U.integral_divergence_eq_integral_inner_outwardNormal_of_tsupport_subset_compl_closure
          (hGts (Sum.inl false))
      · exact U.integral_divergence_eq_integral_inner_outwardNormal_of_tsupport_subset_carrier
          (hGcd' (Sum.inl true)) (hGcs (Sum.inl true)) (hGts (Sum.inl true))
    · exact BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal z.2 (chartOf z)
        (hGcd' (Sum.inr z)) (hGcs (Sum.inr z)) (hGts (Sum.inr z))
  calc ∫ x in U.carrier, Analysis.divergence F x
      = ∫ x in U.carrier, ∑ i ∈ s, Analysis.divergence (G i) x := by
        refine setIntegral_congr_fun U.measurableSet fun x _ => ?_
        rw [hFeq]
        exact Analysis.divergence_finset_sum s fun i _ => (hGcd' i).differentiable one_ne_zero x
    _ = ∑ i ∈ s, ∫ x in U.carrier, Analysis.divergence (G i) x :=
        integral_finsetSum s fun i _ => hvol i
    _ = ∑ i ∈ s, ∫ x in frontier U.carrier, (⟪G i x, U.outwardNormal x⟫ : ℝ)
          ∂(surfaceMeasure V) := Finset.sum_congr rfl fun i _ => hblock i
    _ = ∫ x in frontier U.carrier, ∑ i ∈ s, (⟪G i x, U.outwardNormal x⟫ : ℝ)
          ∂(surfaceMeasure V) := (integral_finsetSum s fun i _ => hbd i).symm
    _ = ∫ x in frontier U.carrier, (⟪F x, U.outwardNormal x⟫ : ℝ) ∂(surfaceMeasure V) := by
        refine setIntegral_congr_fun isClosed_frontier.measurableSet fun x _ => ?_
        rw [hFeq]
        exact (sum_inner s (fun i => G i x) (U.outwardNormal x)).symm

set_option maxHeartbeats 1000000 in
/-- The distributional gradient of the indicator of a smooth domain is the oriented surface
measure: `∫_U ∇η = ∫_{∂U} η ν dℋ^{n-1}` for every compactly supported `C¹` test function `η`.
Equivalently `D𝟙_U = -ν ℋ^{n-1}⌊∂U`.

**Reduction, not a proof from scratch:** this is derived from the vector-field form
`integral_divergence_eq_integral_inner_outwardNormal` of `KLS/Geometry/GaussGreen.lean` by taking
`F x = η x • v` for each fixed `v` (`Analysis.divergence_smul_const` turns `div F` into
`⟪∇η, v⟫`) and commuting both integrals with the inner product (`integral_inner`, whose
boundary-side hypothesis is `integrableOn_smul_outwardNormal`).  It is *not* an independent
Gauss–Green proof, but the theorem it reduces to is proved, so this one uses only the standard
axioms. -/
theorem setIntegral_gradient_eq_integral_smul_outwardNormal (U : SmoothDomain V) {η : V → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ x in U.carrier, gradient η x =
      ∫ x in frontier U.carrier, η x • U.outwardNormal x ∂(surfaceMeasure V) := by
  have hcont : Continuous η := hη.continuous
  have hgradeq : (gradient η) = fun x => (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ η x) := by
    funext x; rw [gradient]
  have hgradcont : Continuous (gradient η) := by
    rw [hgradeq]
    exact (InnerProductSpace.toDual ℝ V).symm.continuous.comp
      (hη.continuous_fderiv one_ne_zero)
  have hgradcs : HasCompactSupport (gradient η) := by
    rw [hgradeq]
    exact (hηc.fderiv ℝ).comp_left
      (g := fun L : V →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ V).symm L) (by simp)
  have hgradint : IntegrableOn (gradient η) U.carrier volume :=
    (hgradcont.integrable_of_hasCompactSupport hgradcs).integrableOn
  have hbdint : IntegrableOn (fun x => η x • U.outwardNormal x) (frontier U.carrier)
      (surfaceMeasure V) := U.integrableOn_smul_outwardNormal hcont hηc
  refine ext_inner_left ℝ fun v => ?_
  -- the vector field `x ↦ η x • v`
  have hFcd : ContDiff ℝ 1 (fun x : V => η x • v) := hη.smul contDiff_const
  have hFcs : HasCompactSupport (fun x : V => η x • v) := by
    refine HasCompactSupport.intro hηc fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have hGG := U.integral_divergence_eq_integral_inner_outwardNormal hFcd hFcs
  have hdiv : ∀ x : V, ⟪v, gradient η x⟫ = Analysis.divergence (fun y : V => η y • v) x := by
    intro x
    rw [Analysis.divergence_smul_const (hη.differentiable one_ne_zero x) v,
      ← toDual_gradient (𝕜 := ℝ) (f := η) (x := x), InnerProductSpace.toDual_apply_apply,
      real_inner_comm]
  have hinner : ∀ x : V, ⟪η x • v, U.outwardNormal x⟫ = ⟪v, η x • U.outwardNormal x⟫ := by
    intro x
    rw [real_inner_smul_left, real_inner_smul_right]
  calc ⟪v, ∫ x in U.carrier, gradient η x⟫
      = ∫ x in U.carrier, ⟪v, gradient η x⟫ := (integral_inner hgradint v).symm
    _ = ∫ x in U.carrier, Analysis.divergence (fun y : V => η y • v) x :=
        setIntegral_congr_fun U.measurableSet fun x _ => hdiv x
    _ = ∫ x in frontier U.carrier, ⟪η x • v, U.outwardNormal x⟫ ∂(surfaceMeasure V) := hGG
    _ = ∫ x in frontier U.carrier, ⟪v, η x • U.outwardNormal x⟫ ∂(surfaceMeasure V) :=
        setIntegral_congr_fun isClosed_frontier.measurableSet fun x _ => hinner x
    _ = ⟪v, ∫ x in frontier U.carrier, η x • U.outwardNormal x ∂(surfaceMeasure V)⟫ :=
        integral_inner hbdint v

end GaussGreen

end KLS.SmoothDomain

end FunctionalInequalities

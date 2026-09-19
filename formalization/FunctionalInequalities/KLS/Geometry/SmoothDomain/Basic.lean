import FunctionalInequalities.KLS.Geometry.Surface.Measure
import FunctionalInequalities.Analysis.Hausdorff.LevelSet
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Smooth domains and their boundary measure

Foundations independent of perimeter recovery, coarea and Sard. -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.KLS

universe u

/-! ### Normalized Hausdorff measure

The definitions `unitBallVolume`, `hausdorffNormalized` and `surfaceMeasure` now live in the
base module `KLS/Geometry/Surface/Measure.lean`, below the general Hausdorff geometry of
`Analysis/Hausdorff/LevelSet.lean`; the convention check and smooth-domain geometry are proved here. -/

section Normalization

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]

/-- Convention check: the normalized top-dimensional Hausdorff measure is Lebesgue measure on the
inner-product space (the isodiametric inequality).  Recorded so that the normalization of
`surfaceMeasure` is pinned by a statement rather than by a comment.

Proved from `Analysis.hausdorffMeasure_finrank_eq_smul_volume`, which pins Mathlib's diameter-gauge
`μH[n]` as `(2^n / ω_n) • volume`; the normalizing factor `ω_n / 2^n` of `hausdorffNormalized` is
its exact inverse, and `ω_n > 0` in every dimension.  In dimension zero the general input already
covers the subsingleton case and `ω_0 = 1`, so both sides are the unit mass at the single point. -/
theorem hausdorffNormalized_finrank_eq_volume :
    hausdorffNormalized V (Module.finrank ℝ V) = (volume : Measure V) := by
  have hωpos : 0 < unitBallVolume (Module.finrank ℝ V) := by
    unfold unitBallVolume; positivity
  rw [hausdorffNormalized, Analysis.hausdorffMeasure_finrank_eq_smul_volume V, smul_smul,
    ← ENNReal.ofReal_mul (by positivity),
    show unitBallVolume (Module.finrank ℝ V) / 2 ^ Module.finrank ℝ V
        * (2 ^ Module.finrank ℝ V / unitBallVolume (Module.finrank ℝ V)) = 1 by
      field_simp,
    ENNReal.ofReal_one, one_smul]

end Normalization

/-! ### Smooth domains -/

/-- A smooth domain: an open set that locally lies on one side of its `C^∞` boundary.  Every
frontier point has an open neighbourhood `W` and a globally `C^∞` defining function `φ` with
nonvanishing derivative on `W` such that the domain meets `W` exactly in `{φ < 0}`. -/
structure SmoothDomain (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- The underlying open set. -/
  carrier : Set V
  /-- The domain is open. -/
  isOpen : IsOpen carrier
  /-- Local defining functions at frontier points. -/
  exists_defining : ∀ x ∈ frontier carrier, ∃ (W : Set V) (φ : V → ℝ),
    IsOpen W ∧ x ∈ W ∧ ContDiff ℝ ∞ φ ∧ (∀ y ∈ W, fderiv ℝ φ y ≠ 0) ∧
      carrier ∩ W = {y ∈ W | φ y < 0}

namespace SmoothDomain

section NormedSpace

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

instance : CoeOut (SmoothDomain V) (Set V) := ⟨carrier⟩

/-- Inside a defining neighbourhood the frontier is the zero set of the defining function. -/
theorem frontier_inter_eq (U : SmoothDomain V) {W : Set V} {φ : V → ℝ} (hW : IsOpen W)
    (hφ : ContDiff ℝ ∞ φ) (hφ' : ∀ y ∈ W, fderiv ℝ φ y ≠ 0)
    (hU : U.carrier ∩ W = {y ∈ W | φ y < 0}) :
    frontier U.carrier ∩ W = {y ∈ W | φ y = 0} := by
  have hcont : Continuous φ := hφ.continuous
  have hopenlt : IsOpen {z ∈ W | φ z < 0} :=
    hW.inter (isOpen_Iio.preimage hcont)
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyfr, hyW⟩
    refine ⟨hyW, ?_⟩
    rcases lt_trichotomy (φ y) 0 with hlt | he | hgt
    · exfalso
      have hyS : y ∈ {z ∈ W | φ z < 0} := ⟨hyW, hlt⟩
      have hsub : {z ∈ W | φ z < 0} ⊆ U.carrier := by
        rw [← hU]; exact Set.inter_subset_left
      exact hyfr.2 (interior_maximal hsub hopenlt hyS)
    · exact he
    · exfalso
      have hnhds : {z | 0 < φ z} ∈ 𝓝 y := (isOpen_lt continuous_const hcont).mem_nhds hgt
      have hballnhds : {z | 0 < φ z} ∩ W ∈ 𝓝 y := Filter.inter_mem hnhds (hW.mem_nhds hyW)
      have hdisj : ({z | 0 < φ z} ∩ W) ∩ U.carrier = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hz0, hzW⟩, hzU⟩
        have hzS : z ∈ U.carrier ∩ W := ⟨hzU, hzW⟩
        rw [hU] at hzS
        exact absurd hzS.2 (not_lt.mpr hz0.le)
      have hnotclosure : y ∉ closure U.carrier := by
        rw [mem_closure_iff_nhds]
        intro hcon
        obtain ⟨z, hz⟩ := hcon _ hballnhds
        rw [Set.mem_inter_iff] at hz
        have : z ∈ ({w | 0 < φ w} ∩ W) ∩ U.carrier := ⟨hz.1, hz.2⟩
        rw [hdisj] at this
        exact this
      exact hnotclosure hyfr.1
  · rintro ⟨hyW, hy0⟩
    have hynotU : y ∉ U.carrier := by
      intro hyU
      have hmem : y ∈ {z ∈ W | φ z < 0} := hU ▸ ⟨hyU, hyW⟩
      exact absurd hy0 hmem.2.ne
    have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
    obtain ⟨v, hv⟩ : ∃ v : V, fderiv ℝ φ y v ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_ne_iff] at hcon
      exact hφ' y hyW (ContinuousLinearMap.ext hcon)
    have hfd : HasFDerivAt φ (fderiv ℝ φ y) y := (hdiff y).hasFDerivAt
    have hpath : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add y
    have hcurve : HasDerivAt (φ ∘ (fun t : ℝ => y + t • v)) (fderiv ℝ φ y v) 0 :=
      hfd.comp_hasDerivAt_of_eq 0 hpath (by simp)
    have hcurve0 : (φ ∘ (fun t : ℝ => y + t • v)) 0 = 0 := by simp [hy0]
    have hcontpath : Continuous fun t : ℝ => y + t • v :=
      continuous_const.add (continuous_id.smul continuous_const)
    refine ⟨?_, hyW⟩
    rw [U.isOpen.frontier_eq]
    refine ⟨?_, hynotU⟩
    rw [mem_closure_iff_nhds]
    intro N hN
    have hNW : N ∩ W ∈ 𝓝 y := Filter.inter_mem hN (hW.mem_nhds hyW)
    have hpathnhds : (fun t : ℝ => y + t • v) ⁻¹' (N ∩ W) ∈ 𝓝 (0 : ℝ) := by
      have hy0' : y + (0 : ℝ) • v = y := by simp
      have := hcontpath.continuousAt (x := (0 : ℝ))
      rw [ContinuousAt, hy0'] at this
      exact this hNW
    have hslope := hasDerivAt_iff_tendsto_slope.mp hcurve
    rcases lt_or_gt_of_ne hv with hcneg | hcpos
    · -- c < 0: use the positive side, t > 0
      have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ,
          slope (φ ∘ (fun t : ℝ => y + t • v)) 0 t < 0 :=
        hslope.eventually_lt_const hcneg
      have hpos' : ∀ᶠ t in 𝓝 (0 : ℝ),
          t ≠ 0 → slope (φ ∘ (fun t : ℝ => y + t • v)) 0 t < 0 := by
        have := eventually_nhdsWithin_iff.mp hpos
        simpa using this
      obtain ⟨t, ht0, hslope_t, hpath_t⟩ :=
        (hpos'.and hpathnhds).exists_gt
      have ht0' : t ≠ 0 := ht0.ne'
      have hslope_lt : slope (φ ∘ (fun t : ℝ => y + t • v)) 0 t < 0 := hslope_t ht0'
      have hgt_eq : (φ ∘ (fun t : ℝ => y + t • v)) t
          = slope (φ ∘ (fun t : ℝ => y + t • v)) 0 t * t := by
        rw [slope_def_field, hcurve0]
        field_simp
        ring
      have hgt_neg : φ (y + t • v) < 0 := by
        have : (φ ∘ (fun t : ℝ => y + t • v)) t < 0 := by
          rw [hgt_eq]; exact mul_neg_of_neg_of_pos hslope_lt ht0
        simpa using this
      refine ⟨y + t • v, ?_, ?_⟩
      · exact (Set.inter_subset_left) hpath_t
      · have hzW : y + t • v ∈ W := (Set.inter_subset_right) hpath_t
        have : y + t • v ∈ U.carrier ∩ W := by rw [hU]; exact ⟨hzW, hgt_neg⟩
        exact this.1
    · -- c > 0: use the negative side, t < 0
      have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ,
          0 < slope (φ ∘ (fun t : ℝ => y + t • v)) 0 t :=
        hslope.eventually_const_lt hcpos
      have hpos' : ∀ᶠ t in 𝓝 (0 : ℝ),
          t ≠ 0 → 0 < slope (φ ∘ (fun t : ℝ => y + t • v)) 0 t := by
        have := eventually_nhdsWithin_iff.mp hpos
        simpa using this
      obtain ⟨t, ht0, hslope_t, hpath_t⟩ :=
        (hpos'.and hpathnhds).exists_lt
      have ht0' : t ≠ 0 := ht0.ne
      have hslope_pos : 0 < slope (φ ∘ (fun t : ℝ => y + t • v)) 0 t := hslope_t ht0'
      have hgt_eq : (φ ∘ (fun t : ℝ => y + t • v)) t
          = slope (φ ∘ (fun t : ℝ => y + t • v)) 0 t * t := by
        rw [slope_def_field, hcurve0]
        field_simp
        ring
      have hgt_neg : φ (y + t • v) < 0 := by
        have : (φ ∘ (fun t : ℝ => y + t • v)) t < 0 := by
          rw [hgt_eq]; exact mul_neg_of_pos_of_neg hslope_pos ht0
        simpa using this
      refine ⟨y + t • v, ?_, ?_⟩
      · exact (Set.inter_subset_left) hpath_t
      · have hzW : y + t • v ∈ W := (Set.inter_subset_right) hpath_t
        have : y + t • v ∈ U.carrier ∩ W := by rw [hU]; exact ⟨hzW, hgt_neg⟩
        exact this.1

/-- The empty set and the whole space are smooth domains with empty frontier. -/
def empty : SmoothDomain V where
  carrier := ∅
  isOpen := isOpen_empty
  exists_defining := by
    simp [frontier_empty]

/-- The whole space as a smooth domain. -/
def univ : SmoothDomain V where
  carrier := Set.univ
  isOpen := isOpen_univ
  exists_defining := by
    simp [frontier_univ]

/-- A strict superlevel set `{x | t < u x}` of a `C^∞` function is a smooth domain as soon as the
derivative of `u` does not vanish on its frontier.  The defining function is `φ = t - u`, matching
the structure's convention that the domain is the *negative* sublevel set of `φ` inside the
defining neighbourhood, and the neighbourhood is the open set `{y | fderiv ℝ u y ≠ 0}`.

Only nonvanishing of `fderiv ℝ u` on `frontier {x | t < u x}` is required, not on the whole level
set `{x | u x = t}` and not on the whole space.  Nothing is assumed about the dimension, the
boundedness of the superlevel set or its nonemptiness: an empty or full carrier has empty frontier,
so the hypothesis is vacuous and the construction still applies. -/
def ofSuperlevel {u : V → ℝ} (hu : ContDiff ℝ ∞ u) {t : ℝ}
    (ht : ∀ x ∈ frontier {x | t < u x}, fderiv ℝ u x ≠ 0) : SmoothDomain V where
  carrier := {x | t < u x}
  isOpen := isOpen_lt continuous_const hu.continuous
  exists_defining := by
    intro x hx
    refine ⟨{y | fderiv ℝ u y ≠ 0}, fun y ↦ t - u y,
      isOpen_compl_singleton.preimage (hu.continuous_fderiv (by simp)), ht x hx,
      contDiff_const.sub hu, ?_, ?_⟩
    · intro y hy
      rw [fderiv_const_sub, neg_ne_zero]
      exact hy
    · ext y
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, sub_neg, and_comm]

/-- The carrier of the superlevel domain is the strict superlevel set. -/
@[simp]
theorem ofSuperlevel_carrier {u : V → ℝ} (hu : ContDiff ℝ ∞ u) {t : ℝ}
    (ht : ∀ x ∈ frontier {x | t < u x}, fderiv ℝ u x ≠ 0) :
    (ofSuperlevel hu ht).carrier = {x | t < u x} :=
  rfl

omit [NormedSpace ℝ V] in
/-- On a subsingleton space every set is clopen, so every frontier is empty. -/
private theorem frontier_eq_empty_of_subsingleton [Subsingleton V] (s : Set V) :
    frontier s = ∅ := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact frontier_empty
  · have hs : s = Set.univ := Set.eq_univ_of_forall fun y ↦ by rwa [Subsingleton.elim y x]
    rw [hs, frontier_univ]

/-- The homothety with nonzero ratio, as a homeomorphism of the ambient space. -/
def homothetyHomeomorph (a : V) {c : ℝ} (hc : c ≠ 0) : V ≃ₜ V where
  toFun := AffineMap.homothety a c
  invFun := AffineMap.homothety a c⁻¹
  left_inv := fun x ↦ by
    simp [AffineMap.homothety_apply, smul_smul, inv_mul_cancel₀ hc]
  right_inv := fun x ↦ by
    simp [AffineMap.homothety_apply, smul_smul, mul_inv_cancel₀ hc]
  continuous_toFun := AffineMap.homothety_continuous a c
  continuous_invFun := AffineMap.homothety_continuous a c⁻¹

@[simp]
theorem coe_homothetyHomeomorph (a : V) {c : ℝ} (hc : c ≠ 0) :
    ⇑(homothetyHomeomorph a hc) = AffineMap.homothety a c := rfl

@[simp]
theorem coe_homothetyHomeomorph_symm (a : V) {c : ℝ} (hc : c ≠ 0) :
    ⇑(homothetyHomeomorph a hc).symm = AffineMap.homothety a c⁻¹ := rfl

/-- A homothety image is the preimage under the inverse homothety. -/
private theorem image_homothety_eq_preimage (a : V) {c : ℝ} (hc : c ≠ 0) (s : Set V) :
    AffineMap.homothety a c '' s = AffineMap.homothety a c⁻¹ ⁻¹' s := by
  exact congrFun (Set.image_eq_preimage_of_inverse
    (f := (AffineMap.homothety a c : V → V)) (g := (AffineMap.homothety a c⁻¹ : V → V))
    (fun x ↦ by simp [AffineMap.homothety_apply, smul_smul, inv_mul_cancel₀ hc])
    (fun x ↦ by simp [AffineMap.homothety_apply, smul_smul, mul_inv_cancel₀ hc])) s

/-- Homotheties are `C^∞`. -/
private theorem contDiff_homothety (a : V) (c : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (AffineMap.homothety a c) := by
  have h : (AffineMap.homothety a c : V → V) = fun x ↦ c • (x - a) + a := by
    funext x; simp [AffineMap.homothety_apply]
  rw [h]
  exact ((contDiff_id.sub contDiff_const).const_smul c).add contDiff_const

/-- The derivative of a homothety is the scalar multiple of the identity. -/
private theorem hasFDerivAt_homothety (a : V) (c : ℝ) (x : V) :
    HasFDerivAt (AffineMap.homothety a c) (c • ContinuousLinearMap.id ℝ V) x := by
  have h : (AffineMap.homothety a c : V → V) = fun x ↦ c • (x - a) + a := by
    funext y; simp [AffineMap.homothety_apply]
  rw [h]
  exact (((hasFDerivAt_id x).sub_const a).const_smul c).add_const a

/-- The image of a smooth domain under a homothety with nonzero ratio is a smooth domain.  The
Blueprint's outward dilation `v_s(x) = 𝟙_U(a + s(x - a))` is the indicator of
`homothety a (1 / s) '' U`. -/
def homothety (U : SmoothDomain V) (a : V) {c : ℝ} (hc : c ≠ 0) : SmoothDomain V where
  carrier := AffineMap.homothety a c '' U.carrier
  isOpen := AffineMap.homothety_isOpenMap a c hc _ U.isOpen
  exists_defining := by
    intro x hx
    have hfr : frontier (AffineMap.homothety a c '' U.carrier)
        = AffineMap.homothety a c '' frontier U.carrier := by
      simpa using ((homothetyHomeomorph a hc).image_frontier U.carrier).symm
    rw [hfr] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨W, φ, hWopen, hyW, hφ, hφ', hUW⟩ := U.exists_defining y hy
    refine ⟨AffineMap.homothety a c '' W, φ ∘ AffineMap.homothety a c⁻¹,
      AffineMap.homothety_isOpenMap a c hc _ hWopen, ⟨y, hyW, rfl⟩,
      hφ.comp (contDiff_homothety a c⁻¹), ?_, ?_⟩
    · intro z hz
      have hz' : AffineMap.homothety a c⁻¹ z ∈ W := by
        rwa [image_homothety_eq_preimage a hc] at hz
      have hcomp : HasFDerivAt (φ ∘ AffineMap.homothety a c⁻¹)
          ((fderiv ℝ φ (AffineMap.homothety a c⁻¹ z)).comp
            (c⁻¹ • ContinuousLinearMap.id ℝ V)) z :=
        ((hφ.differentiable (by simp) _).hasFDerivAt).comp z (hasFDerivAt_homothety a c⁻¹ z)
      rw [hcomp.fderiv]
      intro hcon
      apply hφ' _ hz'
      have := congrArg (fun L : V →L[ℝ] ℝ ↦ c • L) hcon
      simp only [smul_zero] at this
      rw [← this]
      ext v
      simp [smul_smul, mul_inv_cancel₀ hc]
    · rw [image_homothety_eq_preimage a hc, image_homothety_eq_preimage a hc,
        ← Set.preimage_inter, hUW]
      rfl

/-- The carrier of the dilated domain. -/
@[simp]
theorem homothety_carrier (U : SmoothDomain V) (a : V) {c : ℝ} (hc : c ≠ 0) :
    (U.homothety a hc).carrier = AffineMap.homothety a c '' U.carrier :=
  rfl

/-- The frontier is transported by a nonzero homothety. -/
theorem frontier_homothety (U : SmoothDomain V) (a : V) {c : ℝ} (hc : c ≠ 0) :
    frontier (U.homothety a hc).carrier = AffineMap.homothety a c '' frontier U.carrier := by
  exact ((homothetyHomeomorph a hc).image_frontier U.carrier).symm

/-- The indicator of the dilated domain is the dilated indicator with the inverse ratio. -/
theorem indicator_homothety (U : SmoothDomain V) (a : V) {c : ℝ} (hc : c ≠ 0) (x : V) :
    (U.homothety a hc).carrier.indicator (1 : V → ℝ) x =
      U.carrier.indicator 1 (AffineMap.homothety a c⁻¹ x) := by
  show (AffineMap.homothety a c '' U.carrier).indicator (1 : V → ℝ) x = _
  rw [image_homothety_eq_preimage a hc]
  by_cases hmem : AffineMap.homothety a c⁻¹ x ∈ U.carrier
  · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hmem), Set.indicator_of_mem hmem]
    simp
  · rw [Set.indicator_of_notMem (fun h' ↦ hmem (Set.mem_preimage.mp h')),
      Set.indicator_of_notMem hmem]

end NormedSpace

section Measure

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The carrier is measurable. -/
theorem measurableSet (U : SmoothDomain V) : MeasurableSet U.carrier :=
  U.isOpen.measurableSet

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The `(n-1)`-dimensional Hausdorff measure of a smooth boundary is locally finite: the surface
measure of a `C^∞` hypersurface is finite on compact pieces.

Proved from the pointwise level-set bound `Analysis.exists_hausdorffMeasure_levelSet_lt_top`, one
defining neighbourhood at a time: inside a defining neighbourhood `W` the frontier is the zero set
of the defining function `φ`, which is a regular level set there.  Neither the domain nor its
frontier is assumed bounded, and the total measure of the frontier may be infinite; away from the
frontier the complement of the (closed) frontier is a null neighbourhood.  In dimension zero the
frontier of a smooth domain is empty, so only the second branch occurs. -/
theorem isLocallyFiniteMeasure_hausdorff_frontier (U : SmoothDomain V) :
    IsLocallyFiniteMeasure
      ((μH[(Module.finrank ℝ V : ℝ) - 1] : Measure V).restrict (frontier U.carrier)) := by
  have hfrmeas : MeasurableSet (frontier U.carrier) := isClosed_frontier.measurableSet
  constructor
  intro x
  by_cases hx : x ∈ frontier U.carrier
  · obtain ⟨W, φ, hW, hxW, hφ, hφ', hU⟩ := U.exists_defining x hx
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
    rw [Measure.restrict_apply' hfrmeas]
    exact lt_of_le_of_lt (measure_mono hsub) hNfin
  · refine ⟨(frontier U.carrier)ᶜ, isClosed_frontier.isOpen_compl.mem_nhds hx, ?_⟩
    rw [Measure.restrict_apply' hfrmeas, Set.compl_inter_self]
    simp

omit [CompleteSpace V] in
/-- A smooth boundary is Haar-null.  Near a frontier point the boundary lies in `{φ = 0}` for a
defining function whose derivative is positive in some direction `n` on a ball; along `n` the
function is then strictly increasing, so the ball piece of the boundary is disjoint from all of
its own translates `+ u n`, `u > 0`.  Countably many such translates sit in a ball of finite
Haar measure, forcing the piece to be null. -/
theorem addHaar_frontier (U : SmoothDomain V) (m : Measure V) [m.IsAddHaarMeasure] :
    m (frontier U.carrier) = 0 := by
  refine measure_null_of_locally_null _ fun y hy ↦ ?_
  obtain ⟨W, φ, hWopen, hyW, hφ, hφ', hUW⟩ := U.exists_defining y hy
  have hfr := U.frontier_inter_eq hWopen hφ hφ' hUW
  obtain ⟨v, hv⟩ : ∃ v : V, fderiv ℝ φ y v ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_ne_iff] at hcon
    exact hφ' y hyW (ContinuousLinearMap.ext hcon)
  obtain ⟨n, hn⟩ : ∃ n : V, 0 < fderiv ℝ φ y n := by
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · exact ⟨-v, by simpa using hlt⟩
    · exact ⟨v, hgt⟩
  have hcontd : Continuous fun z ↦ fderiv ℝ φ z n :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hopen : IsOpen ({z | 0 < fderiv ℝ φ z n} ∩ W) :=
    (isOpen_lt continuous_const hcontd).inter hWopen
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen y ⟨hn, hyW⟩
  set S : Set V := frontier U.carrier ∩ Metric.ball y r with hS
  have hSmeas : MeasurableSet S :=
    isClosed_frontier.measurableSet.inter Metric.isOpen_ball.measurableSet
  have hSzero : ∀ z ∈ S, φ z = 0 := by
    intro z hz
    have hz' : z ∈ frontier U.carrier ∩ W := ⟨hz.1, (hball hz.2).2⟩
    rw [hfr] at hz'
    exact hz'.2
  refine ⟨S, Filter.inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds y hr)), ?_⟩
  -- no point of `S` can be translated into `S` along a positive multiple of `n`
  have hkey : ∀ (z : V) (u : ℝ), 0 < u → z ∈ S → z + u • n ∈ S → False := by
    intro z u hu hz hzu
    have hmem : ∀ t ∈ Set.Icc (0 : ℝ) u, z + t • n ∈ Metric.ball y r := by
      intro t ht
      have hb0 : 0 ≤ t / u := div_nonneg ht.1 hu.le
      have hb1 : t / u ≤ 1 := (div_le_one hu).mpr ht.2
      have hcv := (convex_ball y r) hz.2 hzu.2 (by linarith : (0:ℝ) ≤ 1 - t / u) hb0 (by ring)
      have hmul : t / u * u = t := div_mul_cancel₀ t hu.ne'
      have heq : (1 - t / u) • z + (t / u) • (z + u • n) = z + t • n := by
        rw [smul_add, smul_smul, hmul]; module
      rwa [heq] at hcv
    set g : ℝ → ℝ := fun t ↦ φ (z + t • n) with hg
    have hpath : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ z + t • n) n t := by
      intro t
      simpa using ((hasDerivAt_id t).smul_const n).const_add z
    have hgd : ∀ t : ℝ, HasDerivAt g (fderiv ℝ φ (z + t • n) n) t := by
      intro t
      exact ((hφ.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t (hpath t)
    have hgcont : ContinuousOn g (Set.Icc 0 u) :=
      (hφ.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    have hgpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) u), 0 < deriv g t := by
      intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) u := interior_subset ht
      rw [(hgd t).deriv]
      exact (hball (hmem t htI)).1
    have hmono := strictMonoOn_of_deriv_pos (convex_Icc 0 u) hgcont hgpos
    have hlt := hmono (Set.left_mem_Icc.mpr hu.le) (Set.right_mem_Icc.mpr hu.le) hu
    rw [hg] at hlt
    simp only [zero_smul, add_zero] at hlt
    rw [hSzero z hz, hSzero _ hzu] at hlt
    exact lt_irrefl 0 hlt
  -- countably many pairwise disjoint translates of `S`
  set t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hts
  have htpos : ∀ k, 0 < t k := fun k ↦ by positivity
  have htle : ∀ k, t k ≤ 1 := by
    intro k
    rw [hts]
    rw [div_le_one (by positivity)]
    simp [le_add_iff_nonneg_left]
  have htinj : ∀ k l : ℕ, k ≠ l → t k ≠ t l := by
    intro k l hkl hcon
    apply hkl
    rw [hts] at hcon
    have h1 : ((k : ℝ) + 1) = ((l : ℝ) + 1) := by
      field_simp at hcon
      linarith
    exact_mod_cast (by linarith : (k : ℝ) = (l : ℝ))
  set T : ℕ → Set V := fun k ↦ (fun w ↦ -(t k • n) + w) ⁻¹' S with hT
  have hTmem : ∀ (k : ℕ) (w : V), w ∈ T k ↔ w - t k • n ∈ S := by
    intro k w
    rw [hT]
    simp only [Set.mem_preimage]
    rw [sub_eq_neg_add]
  have hTmeas : ∀ k, MeasurableSet (T k) := fun k ↦ hSmeas.preimage (measurable_const_add _)
  have hTmeasure : ∀ k, m (T k) = m S := fun k ↦ measure_preimage_add m _ S
  have hdisj2 : ∀ k l : ℕ, t k < t l → Disjoint (T k) (T l) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro w hwk hwl
    refine hkey (w - t l • n) (t l - t k) (by linarith) ((hTmem l w).mp hwl) ?_
    have heq : w - t l • n + (t l - t k) • n = w - t k • n := by
      rw [sub_smul]; module
    rw [heq]
    exact (hTmem k w).mp hwk
  have hTdisj : Pairwise (Function.onFun Disjoint T) := by
    intro k l hkl
    rcases lt_or_gt_of_ne (htinj k l hkl) with h | h
    · exact hdisj2 k l h
    · exact (hdisj2 l k h).symm
  have hTsub : (⋃ k, T k) ⊆ Metric.ball y (r + ‖n‖) := by
    intro w hw
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
    have hk' : w - t k • n ∈ Metric.ball y r := ((hTmem k w).mp hk).2
    rw [Metric.mem_ball, dist_eq_norm] at hk' ⊢
    have hsplit : w - y = (w - t k • n - y) + t k • n := by module
    calc ‖w - y‖ ≤ ‖w - t k • n - y‖ + ‖t k • n‖ := by rw [hsplit]; exact norm_add_le _ _
      _ < r + ‖n‖ := by
          have : ‖t k • n‖ ≤ ‖n‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos k)]
            exact mul_le_of_le_one_left (norm_nonneg n) (htle k)
          linarith
  have hfin : ∑' _ : ℕ, m S ≤ m (Metric.ball y (r + ‖n‖)) := by
    have h1 : m (⋃ k, T k) ≤ m (Metric.ball y (r + ‖n‖)) := measure_mono hTsub
    rw [measure_iUnion hTdisj hTmeas] at h1
    simpa only [hTmeasure] using h1
  by_contra hS0
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hS0] at hfin
  exact absurd (hfin.trans_lt measure_ball_lt_top) (lt_irrefl _)

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- Dilation multiplies the surface measure of the boundary by `|c|^{n-1}`; this is the factor
`s^{1-n}` of the Blueprint for the outward dilation by `1 / s`. -/
theorem hausdorff_frontier_homothety (U : SmoothDomain V) (a : V) {c : ℝ} (hc : c ≠ 0) :
    μH[(Module.finrank ℝ V : ℝ) - 1] (frontier (U.homothety a hc).carrier) =
      (‖c‖₊ : ℝ≥0∞) ^ ((Module.finrank ℝ V : ℝ) - 1) *
        μH[(Module.finrank ℝ V : ℝ) - 1] (frontier U.carrier) := by
  have hfr := U.frontier_homothety a hc
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with h0 | hpos
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    rw [frontier_eq_empty_of_subsingleton (U.homothety a hc).carrier,
      frontier_eq_empty_of_subsingleton U.carrier]
    simp
  · have hd : (0 : ℝ) ≤ (Module.finrank ℝ V : ℝ) - 1 := by
      have h1 : (1 : ℝ) ≤ (Module.finrank ℝ V : ℝ) := by exact_mod_cast hpos
      linarith
    have hcnn : (‖c‖₊ : ℝ≥0) ≠ 0 := by simpa using hc
    rw [hfr, MeasureTheory.hausdorffMeasure_homothety_image hd a hc,
      ← ENNReal.coe_rpow_of_ne_zero hcnn, ENNReal.smul_def, smul_eq_mul]

end Measure

end SmoothDomain

end FunctionalInequalities.KLS

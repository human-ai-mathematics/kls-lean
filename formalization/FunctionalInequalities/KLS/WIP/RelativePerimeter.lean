import FunctionalInequalities.KLS.LogConcave.BorellRepresentation
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Smooth domains, relative perimeter, and the expansion–smoothing lemma

Work-in-progress module for Blueprint `lem:relative-perimeter-smoothing`
(Appendix A, "Relative perimeter without carrier-boundary charges").  The module is not imported
by the library root, not registered in the ledger, and not anchored from the Blueprint.  Read
`SmoothDomain`, `relativePerimeter`, the intermediate obligations, then
`RelativePerimeter.exists_smooth_recovery_sequence`.

Five proof bodies remain `sorry`: `hausdorffNormalized_finrank_eq_volume`, `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`
(local finiteness of the `(n-1)`-dimensional surface measure of a `C^∞` hypersurface),
`SmoothDomain.enorm_gradient_mollified_le` (the Gauss–Green consequence; Mathlib's divergence
theorem is available only for boxes), and the two statements that depend on them,
`RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le` and
`RelativePerimeter.exists_smooth_recovery_sequence`. Other proof bodies are filled but may
inherit these holes. The companion `KLS/WIP/AnalyticPrerequisites.lean` already proves the general
Hausdorff normalization and regular-level-set local finiteness with standard axioms. Those inputs
have not been integrated here; the companion currently imports this module, so integration needs
a lower-level split to avoid an import cycle. Gauss–Green and its downstream estimates remain
unfinished. All five placeholders are retained by the owner's 2026-09-12 instruction; this update
changes documentation only.

## Definitions made explicit

* A **smooth domain** (`SmoothDomain V`) is an open set `U` such that every frontier point has an
  open neighbourhood `W` and a globally `C^∞` function `φ` with nonvanishing derivative on `W`
  and `U ∩ W = {φ < 0} ∩ W`.  This is the Blueprint's "open and locally on one side of its
  `C^∞` boundary"; the local defining function makes "one side" precise and yields
  `frontier U ∩ W = {φ = 0} ∩ W` (`SmoothDomain.frontier_inter_eq`).
* The **relative perimeter** `relativePerimeter ρ Ω U = ∫_{∂U ∩ Ω} ρ dℋ^{n-1}` integrates against
  the **normalized** `(n-1)`-dimensional Hausdorff measure `surfaceMeasure V`, with `n = finrank ℝ V`.
  Mathlib's `μH[d]` uses the gauge `diam ^ d` without the factor `ω_d / 2^d`, so on a Euclidean space
  it is `2^d / ω_d` times the standard `d`-dimensional Hausdorff measure (`ω_d` the volume of the
  unit ball of `ℝ^d`); for `d ≥ 2` the two differ.  `hausdorffNormalized V d := (ω_d / 2^d) • μH[d]`
  restores the standard normalization, in which `ℋ^n = Lebesgue` on `V`
  (`hausdorffNormalized_finrank_eq_volume`, an obligation recording the convention) and `ℋ^{n-1}` is
  the surface measure of the Blueprint.  The weight `ρ` and the open set `Ω` are explicit
  parameters; the lemma instantiates them with a Borell density relative to **Lebesgue measure**
  `IsBorellDensity ν volume ρ` and `Ω = interior ν.support`.  The reference measure must be
  Lebesgue (`volume` of the inner-product space), not an arbitrary Haar measure `m = c · volume`:
  the density then rescales to `ρ / c` while `∫ ‖∇u‖ dν` does not, so the bound
  `limsup ∫ ‖∇u_j‖ dν ≤ P_ρ(U)` would fail for `c > 1`.  (Statement correction of 2026-09-11,
  evening: the first version used `μH[n-1]` unnormalized and an arbitrary Haar `m`.)

## Claimed, not claimed, restricted scope, dimension zero

Claimed (`RelativePerimeter.exists_smooth_recovery_sequence`): for a probability law `ν` on a
finite-dimensional real inner-product space with a Borell density `ρ` relative to Lebesgue
measure `volume`, and a smooth domain `U` of finite relative perimeter, there are globally `C^∞`,
globally Lipschitz functions `0 ≤ u_j ≤ 1` with `u_j → 𝟙_U` in `L¹(ν)` and
`limsup_j ∫ ‖∇u_j‖ dν ≤ relativePerimeter ρ (interior ν.support) U`.  Neither `U` nor the
convex carrier is assumed bounded.  Lean is stronger than the Blueprint in taking any law with
a Borell density rather than the intrinsic law of a log-concave `μ`
(`KLS.LogConcave.exists_isBorellDensity` supplies the latter).

Not claimed: a Gauss–Green theorem for smooth domains in general form, existence of an outward
normal field, sets of finite perimeter or several-variable BV functions, the reverse inequality
`P_ρ(U) ≤ liminf ∫‖∇u_j‖ dν` (lower semicontinuity of perimeter), or any statement about
`lem:relative-perimeter-cheeger-infimum`.  `KLS.Isoperimetry.boundaryContent` (Minkowski
content) is a different object and is not compared here.

Restricted scope: none of the statements assumes `dim V ≥ 1`; the Blueprint's section
preamble fixes `n ≥ 1`.

Dimension zero: `V` is a point, every open set has empty frontier, the relative perimeter is
zero, and the constant sequence `u_j = 𝟙_U` realizes the lemma.  For `n = 0` the index of the
normalized surface measure is `0` (natural-number subtraction), while the separate unnormalized
frontier lemmas use the real exponent `-1`; both integrate over the empty frontier and vanish.

## Intermediate obligations named here

`SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier` (local finiteness of the surface
measure), `SmoothDomain.addHaar_frontier` (the boundary is Haar-null),
`SmoothDomain.hausdorff_frontier_homothety` (dilation scaling `c^{n-1}`),
`SmoothDomain.enorm_gradient_mollified_le` (the Gauss–Green consequence
`‖∇(η ⋆ 𝟙_U)(x)‖ ≤ ∫_{∂U} η(x - y) dℋ^{n-1}(y)`), `IsBorellDensity.exists_le` (`M = sup ρ < ∞`),
`IsBorellDensity.le_rpow_mul_of_combination` (the log-concave comparison
`ρ x ≤ (M / b₀)^{(1-s)/s} ρ y` for `y = s x + (1 - s) b`, `ρ b ≥ b₀`), and
`RelativePerimeter.tendsto_indicator_homothety` (`L¹(ν)` convergence of the dilated indicators).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace FunctionalInequalities.KLS

universe u

/-! ### Normalized Hausdorff measure -/

section Normalization

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]

/-- The volume `ω_d = π^{d/2} / Γ(d/2 + 1)` of the unit ball of `ℝ^d`. -/
def unitBallVolume (d : ℕ) : ℝ := Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)

/-- The standard `d`-dimensional Hausdorff measure `(ω_d / 2^d) • μH[d]`: Mathlib's `μH[d]` uses the
gauge `diam ^ d`, the classical definition uses `ω_d (diam / 2)^d`. -/
def hausdorffNormalized (d : ℕ) : Measure V :=
  ENNReal.ofReal (unitBallVolume d / 2 ^ d) • (μH[(d : ℝ)] : Measure V)

/-- The surface measure `ℋ^{n-1}` of the Blueprint, `n = finrank ℝ V`, in the standard
normalization.  For `n = 0` the natural subtraction gives `ℋ^0`, which only meets the empty
frontier of a smooth domain in a one-point space. -/
def surfaceMeasure : Measure V := hausdorffNormalized V (Module.finrank ℝ V - 1)

/-- Convention check: the normalized top-dimensional Hausdorff measure is Lebesgue measure on the
inner-product space (the isodiametric inequality).  Recorded so that the normalization of
`surfaceMeasure` is pinned by a statement rather than by a comment. -/
theorem hausdorffNormalized_finrank_eq_volume :
    hausdorffNormalized V (Module.finrank ℝ V) = (volume : Measure V) := by
  -- Route (not completed): `μH[n]` is a translation-invariant, locally finite, positive Borel
  -- measure on `V` (finrank `n`), hence by Haar uniqueness (`Measure.addHaarMeasure_unique` /
  -- `isAddLeftInvariant_eq_smul`) equals `c • volume` for some constant `c : ℝ≥0∞`. Evaluating
  -- both sides on a ball of radius `1` centred at `0` pins `c`: `volume (ball 0 1) = ω_n`
  -- (`InnerProductSpace.volume_ball`), while `μH[n] (ball 0 1)` is `2^n` (Mathlib's `μH[n]` uses
  -- the diameter gauge `diam ^ n`, i.e. `(2 * radius) ^ n` on the ball itself, which needs no
  -- extremal input) *only after* one knows the ball realizes its own diametric extremal case,
  -- i.e. the classical isodiametric/isoperimetric inequality "every set of diameter `d` has
  -- Lebesgue measure at most `ω_n (d / 2) ^ n`, with equality only for a ball" — this is what
  -- pins `unitBallVolume n / 2 ^ n` as the correct normalizing constant in `hausdorffNormalized`
  -- rather than some other value. Mathlib has no isodiametric/isoperimetric inequality (checked:
  -- no `isodiametric`/`isoperimetric` identifier in the pinned `Mathlib` snapshot), so the last
  -- step is missing infrastructure, not a tactic gap. Left as `sorry`.
  sorry

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

omit [NormedSpace ℝ V] in
/-- On a subsingleton space every set is clopen, so every frontier is empty. -/
private theorem frontier_eq_empty_of_subsingleton [Subsingleton V] (s : Set V) :
    frontier s = ∅ := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact frontier_empty
  · have hs : s = Set.univ := Set.eq_univ_of_forall fun y ↦ by rwa [Subsingleton.elim y x]
    rw [hs, frontier_univ]

/-- The homothety with nonzero ratio, as a homeomorphism of the ambient space. -/
private def homothetyHomeomorph (a : V) {c : ℝ} (hc : c ≠ 0) : V ≃ₜ V where
  toFun := AffineMap.homothety a c
  invFun := AffineMap.homothety a c⁻¹
  left_inv := fun x ↦ by
    simp [AffineMap.homothety_apply, smul_smul, inv_mul_cancel₀ hc]
  right_inv := fun x ↦ by
    simp [AffineMap.homothety_apply, smul_smul, mul_inv_cancel₀ hc]
  continuous_toFun := AffineMap.homothety_continuous a c
  continuous_invFun := AffineMap.homothety_continuous a c⁻¹

@[simp]
private theorem coe_homothetyHomeomorph (a : V) {c : ℝ} (hc : c ≠ 0) :
    ⇑(homothetyHomeomorph a hc) = AffineMap.homothety a c := rfl

@[simp]
private theorem coe_homothetyHomeomorph_symm (a : V) {c : ℝ} (hc : c ≠ 0) :
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

/-- The `(n-1)`-dimensional Hausdorff measure of a smooth boundary is locally finite: the surface
measure of a `C^∞` hypersurface is finite on compact pieces. -/
theorem isLocallyFiniteMeasure_hausdorff_frontier (U : SmoothDomain V) :
    IsLocallyFiniteMeasure
      ((μH[(Module.finrank ℝ V : ℝ) - 1] : Measure V).restrict (frontier U.carrier)) := by
  sorry

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
  have hfr : frontier (U.homothety a hc).carrier
      = AffineMap.homothety a c '' frontier U.carrier := by
    show frontier (AffineMap.homothety a c '' U.carrier) = _
    simpa using ((homothetyHomeomorph a hc).image_frontier U.carrier).symm
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

/-- The mollified indicator `η ⋆ 𝟙_U` for a normalized bump `η = φ.normed m`. -/
def mollifiedIndicator (U : SmoothDomain V) (φ : ContDiffBump (0 : V)) (m : Measure V)
    (x : V) : ℝ :=
  ∫ y, φ.normed m (x - y) * U.carrier.indicator 1 y ∂m

/-- Gauss–Green consequence for smooth domains: the gradient of the mollified indicator at `x` is
the boundary integral of the outward normal against `η(x - ·)`, hence its norm is at most the
boundary integral of `η(x - ·)` against the surface measure.  This is the "distributional
derivative of `𝟙_U` is its oriented surface measure" step of the Blueprint, in the only form
the proof uses. -/
theorem enorm_gradient_mollified_le (U : SmoothDomain V) (φ : ContDiffBump (0 : V)) (x : V) :
    ‖gradient (U.mollifiedIndicator φ volume) x‖ₑ ≤
      ∫⁻ y in frontier U.carrier, ENNReal.ofReal (φ.normed volume (x - y))
        ∂(surfaceMeasure V) := by
  sorry

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The indicator of a smooth domain is bounded and measurable, hence locally integrable. -/
private theorem locallyIntegrable_indicator (U : SmoothDomain V) (m : Measure V)
    [IsLocallyFiniteMeasure m] : LocallyIntegrable (U.carrier.indicator (1 : V → ℝ)) m := by
  intro x
  obtain ⟨s, hs, hsfin⟩ := m.finiteAt_nhds x
  refine ⟨s, hs, Measure.integrableOn_of_bounded hsfin.ne
    (measurable_one.indicator U.isOpen.measurableSet).aestronglyMeasurable (M := 1) ?_⟩
  filter_upwards with y
  by_cases hy : y ∈ U.carrier
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

omit [MeasurableSpace V] [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The indicator of a smooth domain takes values in `[0, 1]`. -/
private theorem indicator_mem_Icc (U : SmoothDomain V) (y : V) :
    U.carrier.indicator (1 : V → ℝ) y ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hy : y ∈ U.carrier
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

omit [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The mollified indicator is the convolution of the indicator with the normalized bump. -/
private theorem mollifiedIndicator_eq (U : SmoothDomain V) (φ : ContDiffBump (0 : V))
    (m : Measure V) :
    U.mollifiedIndicator φ m
      = (U.carrier.indicator (1 : V → ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] φ.normed m := by
  funext x
  rw [convolution_def]
  simp only [mollifiedIndicator, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact integral_congr_ae (Eventually.of_forall fun t ↦ mul_comm _ _)

omit [CompleteSpace V] in
/-- The mollified indicator is globally `C^∞`, globally Lipschitz, and takes values in `[0, 1]`. -/
theorem mollifiedIndicator_contDiff_lipschitz_mem_Icc (U : SmoothDomain V)
    (φ : ContDiffBump (0 : V)) (m : Measure V) [m.IsAddHaarMeasure] :
    ContDiff ℝ ∞ (U.mollifiedIndicator φ m) ∧
      (∃ K : ℝ≥0, LipschitzWith K (U.mollifiedIndicator φ m)) ∧
      ∀ x, U.mollifiedIndicator φ m x ∈ Set.Icc (0 : ℝ) 1 := by
  set f : V → ℝ := U.carrier.indicator 1 with hfdef
  set η : V → ℝ := φ.normed m with hηdef
  have hloc : LocallyIntegrable f m := U.locallyIntegrable_indicator m
  have hcs : HasCompactSupport η := φ.hasCompactSupport_normed
  have hcd : ContDiff ℝ ∞ η := φ.contDiff_normed
  have hηnn : ∀ t, 0 ≤ η t := fun t ↦ φ.nonneg_normed t
  have hintη : Integrable η m := φ.integrable_normed
  have hfmeas : Measurable f := measurable_one.indicator U.isOpen.measurableSet
  have hconv : U.mollifiedIndicator φ m
      = f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] η := U.mollifiedIndicator_eq φ m
  refine ⟨by rw [hconv]; exact hcs.contDiff_convolution_right _ hloc hcd, ?_, ?_⟩
  · -- globally Lipschitz, with constant the total mass of `‖∇η‖`
    have hcsd : HasCompactSupport (fderiv ℝ η) := hcs.fderiv (𝕜 := ℝ)
    have hcontd : Continuous (fderiv ℝ η) := hcd.continuous_fderiv (by simp)
    have hintd : Integrable (fun t ↦ ‖fderiv ℝ η t‖) m :=
      (hcontd.integrable_of_hasCompactSupport hcsd).norm
    set C : ℝ := ∫ t, ‖fderiv ℝ η t‖ ∂m with hC
    have hC0 : 0 ≤ C := integral_nonneg fun t ↦ norm_nonneg _
    have hD : ∀ x : V, HasFDerivAt (U.mollifiedIndicator φ m)
        ((f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR V, m] fderiv ℝ η) x) x := by
      intro x
      rw [hconv]
      exact hcs.hasFDerivAt_convolution_right _ hloc (hcd.of_le (by simp)) x
    refine ⟨⟨C, hC0⟩, lipschitzWith_of_nnnorm_fderiv_le
      (fun x ↦ (hD x).differentiableAt) fun x ↦ ?_⟩
    have hbound : ‖fderiv ℝ (U.mollifiedIndicator φ m) x‖ ≤ C := by
      rw [(hD x).fderiv]
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun v ↦ ?_
      rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hloc hcsd hcontd x v,
        convolution_eq_swap]
      have hbd : Integrable (fun t ↦ ‖fderiv ℝ η t‖ * ‖v‖) m := hintd.mul_const _
      refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun t ↦ ?_)).trans_eq ?_
      · have h1 : |f (x - t)| ≤ 1 := by
          rw [abs_of_nonneg (U.indicator_mem_Icc (x - t)).1]
          exact (U.indicator_mem_Icc (x - t)).2
        have h2 : |fderiv ℝ η t v| ≤ ‖fderiv ℝ η t‖ * ‖v‖ := by
          simpa [Real.norm_eq_abs] using (fderiv ℝ η t).le_opNorm v
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
        calc |f (x - t)| * |fderiv ℝ η t v| ≤ 1 * (‖fderiv ℝ η t‖ * ‖v‖) :=
              mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = ‖fderiv ℝ η t‖ * ‖v‖ := one_mul _
      · rw [integral_mul_const]
    exact hbound
  · -- values in `[0, 1]`
    intro x
    have hswap : U.mollifiedIndicator φ m x = ∫ t, f (x - t) * η t ∂m := by
      rw [hconv, convolution_eq_swap]
      simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have hint : Integrable (fun t ↦ f (x - t) * η t) m := by
      refine hintη.mono' ((hfmeas.comp (measurable_const.sub measurable_id)).mul
        φ.continuous_normed.measurable).aestronglyMeasurable ?_
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (U.indicator_mem_Icc (x - t)).1,
        abs_of_nonneg (hηnn t)]
      exact mul_le_of_le_one_left (hηnn t) (U.indicator_mem_Icc (x - t)).2
    refine ⟨?_, ?_⟩
    · rw [hswap]
      exact integral_nonneg fun t ↦ mul_nonneg (U.indicator_mem_Icc (x - t)).1 (hηnn t)
    · rw [hswap]
      calc ∫ t, f (x - t) * η t ∂m ≤ ∫ t, η t ∂m :=
            integral_mono hint hintη fun t ↦
              mul_le_of_le_one_left (hηnn t) (U.indicator_mem_Icc (x - t)).2
        _ = 1 := φ.integral_normed

end Measure

end SmoothDomain

/-! ### Relative perimeter -/

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The relative perimeter `P_ρ(U) = ∫_{∂U ∩ Ω} ρ dℋ^{n-1}` of a smooth domain with respect to a
weight `ρ` inside the open set `Ω`, against the `(n-1)`-dimensional Hausdorff measure of `V`
(`n = finrank ℝ V`).  Boundary pieces outside `Ω` carry no charge. -/
def relativePerimeter (ρ : V → ℝ) (Ω : Set V) (U : SmoothDomain V) : ℝ≥0∞ :=
  ∫⁻ x in frontier U.carrier ∩ Ω, ENNReal.ofReal (ρ x) ∂(surfaceMeasure V)

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Domains with empty frontier have zero relative perimeter; dimension zero is included. -/
theorem relativePerimeter_eq_zero_of_frontier_eq_empty (ρ : V → ℝ) (Ω : Set V)
    (U : SmoothDomain V) (h : frontier U.carrier = ∅) :
    relativePerimeter ρ Ω U = 0 := by
  unfold relativePerimeter
  rw [h, Set.empty_inter, Measure.restrict_empty, lintegral_zero_measure]

/-! ### Density comparisons from log-concavity -/

namespace IsBorellDensity

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The positivity set of a Borell density of a probability law has nonempty interior. -/
private theorem nonempty_interior_pos {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) :
    (interior {y : V | 0 < ρ y}).Nonempty := by
  set S : Set V := {y | 0 < ρ y} with hS
  have hSconv : Convex ℝ S := h.convex_pos
  have hmeas : MeasurableSet S := measurableSet_lt measurable_const h.measurable
  have hνSc : (ν : Measure V) Sᶜ = 0 := h.measure_compl_pos
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hspan : affineSpan ℝ S ≠ ⊤ := by
    intro htop
    have hne := hSconv.interior_nonempty_iff_affineSpan_eq_top.mpr htop
    rw [hemp] at hne
    exact Set.not_nonempty_empty hne
  have hmS : m (affineSpan ℝ S : Set V) = 0 := Measure.addHaar_affineSubspace m _ hspan
  have hνS : (ν : Measure V) S = 0 := by
    rw [← h.withDensity_eq, withDensity_apply _ hmeas]
    exact setLIntegral_measure_zero _ _ (measure_mono_null (subset_affineSpan ℝ S) hmS)
  have huniv : (ν : Measure V) Set.univ = 0 := by
    rw [← Set.union_compl_self S]
    exact measure_union_null hνS hνSc
  simp at huniv

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- A Borell density of a probability law is bounded below by a positive constant on some ball. -/
private theorem exists_ball_le {ν : ProbabilityMeasure V} {m : Measure V} [m.IsAddHaarMeasure]
    {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) :
    ∃ (a : V) (r b₀ : ℝ), 0 < r ∧ 0 < b₀ ∧ ∀ z ∈ Metric.ball a r, b₀ ≤ ρ z := by
  obtain ⟨a, ha⟩ := h.nonempty_interior_pos
  have haS : a ∈ {y : V | 0 < ρ y} := interior_subset ha
  have hpos : 0 < ρ a := haS
  have hca : ContinuousAt ρ a :=
    h.continuousOn_interior_pos.continuousAt (isOpen_interior.mem_nhds ha)
  have hmem : ρ ⁻¹' Set.Ioi (ρ a / 2) ∈ 𝓝 a :=
    hca (Ioi_mem_nhds (by linarith))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  exact ⟨a, r, ρ a / 2, hr, by linarith, fun z hz ↦ (hsub hz).le⟩

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- A Borell density of a probability law is bounded: `M = sup ρ < ∞`.  On a ball where
`ρ ≥ b₀ > 0`, log-concavity gives `ρ ≥ √(b₀ ρ(x))` on a half-size ball, whose mass is at most
one. -/
theorem exists_le {ν : ProbabilityMeasure V} {m : Measure V} [m.IsAddHaarMeasure] {ρ : V → ℝ}
    (h : IsBorellDensity (ν : Measure V) m ρ) :
    ∃ M : ℝ, ∀ x, ρ x ≤ M := by
  obtain ⟨a, r, b₀, hr, hb₀, hball⟩ := h.exists_ball_le
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  set K₀ : ℝ≥0∞ := m (Metric.ball (0 : V) (r / 2)) with hK₀
  have hK₀pos : 0 < K₀ := Metric.measure_ball_pos m 0 hr2
  have hK₀top : K₀ ≠ ⊤ := measure_ball_lt_top.ne
  set K : ℝ := K₀.toReal with hK
  have hKpos : 0 < K := ENNReal.toReal_pos hK₀pos.ne' hK₀top
  refine ⟨1 / (K ^ 2 * b₀), fun x ↦ ?_⟩
  set c : V := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • a with hc
  have hsqrt : ∀ z ∈ Metric.ball c (r / 2), Real.sqrt (ρ x * b₀) ≤ ρ z := by
    intro z hz
    set b : V := (2 : ℝ) • z - x with hb
    have hbmem : b ∈ Metric.ball a r := by
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have hbe : b - a = (2 : ℝ) • (z - c) := by rw [hb, hc]; module
      rw [hbe, norm_smul]
      simp only [Real.norm_ofNat]
      linarith [hz]
    have hlc := h.logConcave x b (1 / 2) (by norm_num) (by norm_num)
    have hzeq : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • b = z := by rw [hb]; module
    rw [hzeq] at hlc
    have hb₀b : b₀ ≤ ρ b := hball b hbmem
    calc Real.sqrt (ρ x * b₀) = ρ x ^ (1 / 2 : ℝ) * b₀ ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, Real.mul_rpow (h.nonneg x) hb₀.le]
      _ ≤ ρ x ^ (1 / 2 : ℝ) * ρ b ^ (1 - 1 / 2 : ℝ) := by
          have hexp : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
          rw [hexp]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb₀.le hb₀b (by norm_num))
            (Real.rpow_nonneg (h.nonneg x) _)
      _ ≤ ρ z := hlc
  have hcball : m (Metric.ball c (r / 2)) = K₀ := Measure.addHaar_ball_center m c (r / 2)
  have hint : ENNReal.ofReal (Real.sqrt (ρ x * b₀)) * K₀
      ≤ (ν : Measure V) (Metric.ball c (r / 2)) := by
    rw [← h.withDensity_eq, withDensity_apply _ Metric.isOpen_ball.measurableSet]
    calc ENNReal.ofReal (Real.sqrt (ρ x * b₀)) * K₀
        = ∫⁻ _ in Metric.ball c (r / 2), ENNReal.ofReal (Real.sqrt (ρ x * b₀)) ∂m := by
          rw [setLIntegral_const, hcball]
      _ ≤ ∫⁻ z in Metric.ball c (r / 2), ENNReal.ofReal (ρ z) ∂m :=
          setLIntegral_mono h.measurable.ennreal_ofReal
            (fun z hz ↦ ENNReal.ofReal_le_ofReal (hsqrt z hz))
  have hle1 : ENNReal.ofReal (Real.sqrt (ρ x * b₀)) * K₀ ≤ 1 := hint.trans prob_le_one
  -- transfer to the reals
  have hreal : Real.sqrt (ρ x * b₀) * K ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hle1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_one]
      at this
  have hsq : Real.sqrt (ρ x * b₀) ≤ 1 / K := by
    rw [le_div_iff₀ hKpos]; linarith
  have hmul : ρ x * b₀ ≤ (1 / K) ^ 2 := by
    have := Real.sq_sqrt (mul_nonneg (h.nonneg x) hb₀.le)
    nlinarith [Real.sqrt_nonneg (ρ x * b₀), hsq]
  rw [le_div_iff₀ (by positivity)]
  have : (1 / K) ^ 2 = 1 / K ^ 2 := by rw [div_pow, one_pow]
  rw [this] at hmul
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  calc ρ x * (K ^ 2 * b₀) = (ρ x * b₀) * K ^ 2 := by ring
    _ ≤ (1 / K ^ 2) * K ^ 2 := by
        exact mul_le_mul_of_nonneg_right hmul hK2.le
    _ = 1 := by field_simp

omit [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The log-concave comparison of the Blueprint: if `y = s x + (1 - s) b` with `0 < s < 1`,
`b₀ ≤ ρ b`, `0 < b₀`, and `ρ ≤ M` everywhere, then `ρ x ≤ (M / b₀)^{(1-s)/s} ρ y`.  Applied with
`b` in the ball where `ρ ≥ b₀`, it lets the weight at `x` be paid by the weight at the nearby
point `y` of the undilated domain. -/
theorem le_rpow_mul_of_combination {ν m : Measure V} {ρ : V → ℝ} (h : IsBorellDensity ν m ρ)
    {M b₀ s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) (hb₀ : 0 < b₀) (hM : ∀ z, ρ z ≤ M)
    {x y b : V} (hb : b₀ ≤ ρ b) (hy : y = s • x + (1 - s) • b) :
    ρ x ≤ (M / b₀) ^ ((1 - s) / s) * ρ y := by
  have hρx := h.nonneg x
  have hρy := h.nonneg y
  have hs' : (0 : ℝ) < 1 - s := by linarith
  have hM0 : 0 ≤ M := le_trans hρy (hM y)
  have hexp : 0 ≤ (1 - s) / s := (div_pos hs' hs₀).le
  rcases eq_or_lt_of_le hρx with hx0 | hxpos
  · rw [← hx0]
    positivity
  have hlc := h.logConcave x b s hs₀ hs₁
  rw [← hy] at hlc
  have hb₁ : b₀ ^ (1 - s) ≤ ρ b ^ (1 - s) := Real.rpow_le_rpow hb₀.le hb hs'.le
  have key : ρ x ^ s * b₀ ^ (1 - s) ≤ ρ y :=
    le_trans (mul_le_mul_of_nonneg_left hb₁ (Real.rpow_nonneg hρx s)) hlc
  have hb₀p : (0 : ℝ) < b₀ ^ (1 - s) := Real.rpow_pos_of_pos hb₀ _
  have hxsp : (0 : ℝ) < ρ x ^ s := Real.rpow_pos_of_pos hxpos s
  have hypos : 0 < ρ y := lt_of_lt_of_le (mul_pos hxsp hb₀p) key
  have key2 : ρ x ^ s ≤ ρ y / b₀ ^ (1 - s) := (le_div_iff₀ hb₀p).mpr key
  have hid : (ρ x ^ s) ^ (1 / s) = ρ x := by
    rw [← Real.rpow_mul hρx, mul_one_div, div_self hs₀.ne', Real.rpow_one]
  have h1 : ρ x ≤ (ρ y / b₀ ^ (1 - s)) ^ (1 / s) := by
    rw [← hid]
    exact Real.rpow_le_rpow hxsp.le key2 (by positivity)
  have h2 : (ρ y / b₀ ^ (1 - s)) ^ (1 / s) = ρ y ^ (1 / s) / b₀ ^ ((1 - s) / s) := by
    rw [Real.div_rpow hρy hb₀p.le, ← Real.rpow_mul hb₀.le, mul_one_div]
  have hsum : (1 : ℝ) + (1 - s) / s = 1 / s := by field_simp; ring
  have h3 : ρ y ^ (1 / s) = ρ y * ρ y ^ ((1 - s) / s) := by
    rw [← hsum, Real.rpow_add hypos, Real.rpow_one]
  have h4 : ρ y ^ ((1 - s) / s) ≤ M ^ ((1 - s) / s) := Real.rpow_le_rpow hρy (hM y) hexp
  have h5 : (M / b₀) ^ ((1 - s) / s) = M ^ ((1 - s) / s) / b₀ ^ ((1 - s) / s) :=
    Real.div_rpow hM0 hb₀.le _
  calc ρ x ≤ ρ y ^ (1 / s) / b₀ ^ ((1 - s) / s) := h2 ▸ h1
    _ = ρ y * ρ y ^ ((1 - s) / s) / b₀ ^ ((1 - s) / s) := by rw [h3]
    _ ≤ ρ y * M ^ ((1 - s) / s) / b₀ ^ ((1 - s) / s) := by
        gcongr
    _ = (M / b₀) ^ ((1 - s) / s) * ρ y := by rw [h5]; ring

end IsBorellDensity

/-! ### The expansion–smoothing lemma -/

namespace RelativePerimeter

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Dilated indicators converge to the indicator in `L¹(ν)` as the ratio tends to one, for an
open set whose frontier is `ν`-null. -/
theorem tendsto_indicator_homothety (ν : ProbabilityMeasure V) {U : Set V} (hU : IsOpen U)
    (hfr : (ν : Measure V) (frontier U) = 0) (a : V) :
    Tendsto (fun c : ℝ ↦ ∫⁻ x, ‖U.indicator (1 : V → ℝ) (AffineMap.homothety a c x) -
        U.indicator 1 x‖ₑ ∂(ν : Measure V)) (𝓝 1) (𝓝 0) := by
  have hind : Measurable (U.indicator (1 : V → ℝ)) := measurable_one.indicator hU.measurableSet
  have hIcc : ∀ y : V, U.indicator (1 : V → ℝ) y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    by_cases hy : y ∈ U
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have hzero : ∫⁻ _ : V, (0 : ℝ≥0∞) ∂(ν : Measure V) = 0 := lintegral_zero
  rw [← hzero]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ 1) ?_ ?_ ?_ ?_
  · filter_upwards with c
    exact ((hind.comp (AffineMap.homothety_continuous a c).measurable).sub hind).enorm
  · filter_upwards with c
    filter_upwards with x
    have h1 := hIcc (AffineMap.homothety a c x)
    have h2 := hIcc x
    rw [Real.enorm_eq_ofReal_abs, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_le]
    exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  · rw [lintegral_one]
    exact measure_ne_top _ _
  · have hae : ∀ᵐ x ∂(ν : Measure V), x ∉ frontier U := by
      rw [ae_iff]; simpa using hfr
    filter_upwards [hae] with x hx
    have hpath : Tendsto (fun c : ℝ ↦ AffineMap.homothety a c x) (𝓝 1) (𝓝 x) := by
      have heq : (fun c : ℝ ↦ AffineMap.homothety a c x) = fun c : ℝ ↦ c • (x - a) + a := by
        funext c; simp [AffineMap.homothety_apply]
      rw [heq]
      have hc : Continuous fun c : ℝ ↦ c • (x - a) + a :=
        (continuous_id.smul continuous_const).add continuous_const
      simpa using hc.tendsto 1
    by_cases hxU : x ∈ U
    · refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
      filter_upwards [hpath (hU.mem_nhds hxU)] with c hc
      have hc' : AffineMap.homothety a c x ∈ U := hc
      simp [Set.indicator_of_mem hc', Set.indicator_of_mem hxU]
    · have hxc : x ∉ closure U := fun hcl ↦ hx ⟨hcl, by rwa [hU.interior_eq]⟩
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
      filter_upwards [hpath (isClosed_closure.isOpen_compl.mem_nhds hxc)] with c hc
      have hc' : AffineMap.homothety a c x ∈ (closure U)ᶜ := hc
      have hcU : AffineMap.homothety a c x ∉ U := fun hmem ↦ hc' (subset_closure hmem)
      simp [Set.indicator_of_notMem hcU, Set.indicator_of_notMem hxU]

/-- Blueprint `lem:relative-perimeter-smoothing`.  Let `ν` be a probability law on a
finite-dimensional real inner-product space with a Borell density `ρ` relative to the Haar
measure `m`, and put `Ω = interior ν.support`.  For every smooth domain `U` with finite relative
perimeter there are globally `C^∞`, globally Lipschitz functions `0 ≤ u_j ≤ 1` such that
`u_j → 𝟙_U` in `L¹(ν)` and `limsup_j ∫ ‖∇u_j‖ dν ≤ P_ρ(U)`.  The domain and the carrier may be
unbounded; a piece of `∂U` on `∂(supp ν)` costs nothing. -/
theorem exists_smooth_recovery_sequence {ν : ProbabilityMeasure V}
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    (U : SmoothDomain V)
    (hU : relativePerimeter ρ (interior (ν : Measure V).support) U ≠ ⊤) :
    ∃ u : ℕ → V → ℝ,
      (∀ j, ContDiff ℝ ∞ (u j) ∧ (∃ K : ℝ≥0, LipschitzWith K (u j)) ∧
        ∀ x, u j x ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫⁻ x, ‖u j x - U.carrier.indicator 1 x‖ₑ ∂(ν : Measure V))
        atTop (𝓝 0) ∧
      limsup (fun j ↦ ∫⁻ x, ‖gradient (u j) x‖ₑ ∂(ν : Measure V)) atTop ≤
        relativePerimeter ρ (interior (ν : Measure V).support) U := by
  sorry

/-- The one-step quantitative bound behind the lemma: for `0 < s < 1`, a ball `closedBall a r ⊆ Ω`
on which `ρ ≥ b₀ > 0`, `ρ ≤ M`, and a bump of outer radius `ε` with `s ε / (1 - s) < r`, the
mollified outward dilation `u = η_ε ⋆ 𝟙_{U_{1/s}}` satisfies
`∫ ‖∇u‖ dν ≤ s^{1-n} (M / b₀)^{(1-s)/s} P_ρ(U)`. -/
theorem lintegral_enorm_gradient_mollified_homothety_le {ν : ProbabilityMeasure V}
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    (U : SmoothDomain V) {a : V} {r b₀ M s : ℝ} (hr : 0 < r)
    (haΩ : Metric.closedBall a r ⊆ interior (ν : Measure V).support)
    (hb₀ : 0 < b₀) (hball : ∀ z ∈ Metric.closedBall a r, b₀ ≤ ρ z) (hM : ∀ z, ρ z ≤ M)
    (hs₀ : 0 < s) (hs₁ : s < 1) (φ : ContDiffBump (0 : V)) (hε : s * φ.rOut / (1 - s) < r) :
    ∫⁻ x, ‖gradient ((U.homothety a (inv_ne_zero hs₀.ne')).mollifiedIndicator φ volume) x‖ₑ
        ∂(ν : Measure V) ≤
      ENNReal.ofReal (s ^ (1 - (Module.finrank ℝ V : ℝ)) * (M / b₀) ^ ((1 - s) / s)) *
        relativePerimeter ρ (interior (ν : Measure V).support) U := by
  sorry

end RelativePerimeter

end FunctionalInequalities.KLS

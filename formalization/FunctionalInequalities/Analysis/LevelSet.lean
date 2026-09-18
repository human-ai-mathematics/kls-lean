import FunctionalInequalities.KLS.Geometry.SurfaceMeasure
import FunctionalInequalities.Probability.Line.BrunnMinkowski
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Hausdorff normalization and regular level sets

General geometric analysis on a finite-dimensional real inner-product space `V`, independent of
the KLS objects and of the relative-perimeter statements that consume it.  Every statement here
is proved and uses only the standard axioms; the module contains no hole.

## A. Prékopa–Leindler, Brunn–Minkowski, and the isodiametric inequality

Mathlib's `μH[d]` uses the gauge `diam ^ d`; the classical `d`-dimensional Hausdorff measure uses
`ω_d (diam / 2) ^ d`.  Haar uniqueness gives `μH[n] = c • volume` for some `c ∈ (0, ∞)` for free;
pinning `c = 2^n / ω_n` is exactly the isodiametric inequality `volume S ≤ ω_n (diam S / 2)^n`.
The route chosen here is through Brunn–Minkowski rather than Steiner symmetrization:
`volume S ≤ volume (½ S + ½ (-S)) ≤ volume (closedBall 0 (diam S / 2))`, where the middle step is
the multiplicative Brunn–Minkowski inequality on `V`, itself a consequence of the
`n`-dimensional Prékopa–Leindler inequality by induction on the dimension.  The one-dimensional
base case is `FunctionalInequalities.Probability.Line.prekopaLeindler`, with no boundedness
hypothesis.

`hausdorffMeasure_finrank_eq_smul_volume` is the general form of
`KLS.hausdorffNormalized_finrank_eq_volume` (`KLS/Geometry/SmoothDomain.lean`): unfolding
`KLS.hausdorffNormalized` and `smul_smul` turns one into the other.  The half
`volume ≤ (ω_n / 2^n) • μH[n]` (`volume_le_ofReal_mul_hausdorffMeasure`) follows from the
isodiametric inequality by covering; the other half uses the Besicovitch covering theorem
(`Besicovitch.exists_disjoint_closedBall_covering_ae`).

## B. Regular level sets are locally Lipschitz graphs of finite `ℋ^{n-1}`

`exists_hausdorffMeasure_levelSet_lt_top`: at a point where a `C¹` function has nonzero
derivative, the level set through that point has finite `μH[n-1]` in some neighbourhood.  Its
route is `exists_lipschitzOnWith_levelSet_subset_image`: the level set is locally contained in a
Lipschitz image of a bounded subset of the tangent hyperplane `ker (Dφ x)`; Mathlib then supplies
`LipschitzOnWith.hausdorffMeasure_image_le` and the fact that `μH[finrank]` of an
`(n-1)`-dimensional inner-product space is a Haar measure, hence finite on bounded sets.  This is
the general proposition behind `KLS.SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier` and
`KLS.SmoothDomain.isLocallyFiniteMeasure_surfaceMeasure_frontier`.

The statement is deliberately pointwise.  "`μH[n-1]` restricted to the level set is a locally
finite measure" is **false** for a level set inside an open set `W` (the graph of `sin (1/x)`
over `x > 0` has infinite length near the origin); it becomes true for the closed frontier of a
smooth domain because every frontier point has its own defining neighbourhood.

## Dimension zero

All statements hold on a one-point space: `ω_0 = 1`, `μH[0]` is counting measure, and the
regular-point hypotheses are vacuous.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Pointwise

namespace FunctionalInequalities

universe u

namespace Analysis

/-! ### A. Prékopa–Leindler, Brunn–Minkowski, and the isodiametric inequality -/

section Isodiametric

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- A positive real power commutes with suprema in `ℝ≥0∞` (copy of the private helper of
`FunctionalInequalities.Probability.Line.BrunnMinkowski`, which is not exported). -/
private theorem rpow_iSup {ι : Sort*} (u : ι → ENNReal) {t : ℝ} (ht : 0 < t) :
    (⨆ i, u i) ^ t = ⨆ i, u i ^ t :=
  (ENNReal.orderIsoRpow t ht).map_iSup u

/-- The `ℝ≥0∞`-valued Prékopa–Leindler property at exponent `t`. -/
private def IsPL (X : Type*) [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    (μ : Measure X) (t : ℝ) : Prop :=
  ∀ f g h : X → ℝ≥0∞, Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) →
    (∫⁻ x, f x ∂μ) ^ t * (∫⁻ y, g y ∂μ) ^ (1 - t) ≤ ∫⁻ z, h z ∂μ

private theorem iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  by_cases ha : a = ⊤
  · subst ha
    have hmt : ∀ n : ℕ, min (⊤ : ℝ≥0∞) (n : ℝ≥0∞) = (n : ℝ≥0∞) := fun n => min_eq_right le_top
    simp_rw [hmt]
    exact le_of_eq ENNReal.iSup_natCast.symm
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (le_min le_rfl hn.le)

private theorem isPL_real {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IsPL ℝ (volume : Measure ℝ) t := by
  have ht1' : (0:ℝ) < 1 - t := by linarith
  intro f g h hf hg hh hfgh
  have hmin : ∀ (u : ℝ → ℝ≥0∞) (N : ℕ) (x : ℝ), min (u x) (N : ℝ≥0∞) ≠ ⊤ := by
    intro u N x
    exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
  have hstep : ∀ N : ℕ,
      (∫⁻ x, min (f x) (N : ℝ≥0∞)) ^ t * (∫⁻ y, min (g y) (N : ℝ≥0∞)) ^ (1 - t) ≤
        ∫⁻ z, h z := by
    intro N
    have hkey : ∀ x y : ℝ,
        (min (f x) (N : ℝ≥0∞)) ^ t * (min (g y) (N : ℝ≥0∞)) ^ (1 - t)
          ≤ min (h (t * x + (1 - t) * y)) (N : ℝ≥0∞) := by
      intro x y
      refine le_min ?_ ?_
      · refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ht0.le)
          (ENNReal.rpow_le_rpow (min_le_left _ _) ht1'.le)) ?_
        simpa using hfgh x y
      · refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_right _ _) ht0.le)
          (ENNReal.rpow_le_rpow (min_le_right _ _) ht1'.le)) ?_
        rw [← ENNReal.rpow_add_of_nonneg _ _ ht0.le ht1'.le]
        simp
    have hreal : ∀ x y : ℝ,
        ((min (f x) (N : ℝ≥0∞)).toReal) ^ t * ((min (g y) (N : ℝ≥0∞)).toReal) ^ (1 - t)
          ≤ (min (h (t * x + (1 - t) * y)) (N : ℝ≥0∞)).toReal := by
      intro x y
      rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (hmin h N _) (hkey x y)
    have hmeas : ∀ u : ℝ → ℝ≥0∞, Measurable u →
        Measurable fun x => (min (u x) (N : ℝ≥0∞)).toReal :=
      fun u hu => (hu.min measurable_const).ennreal_toReal
    have hPL := Probability.Line.prekopaLeindler
      (hmeas f hf) (hmeas g hg) (hmeas h hh)
      (fun x => ENNReal.toReal_nonneg) (fun y => ENNReal.toReal_nonneg) ht0 ht1 hreal
    have hof : ∀ (u : ℝ → ℝ≥0∞) (x : ℝ),
        ENNReal.ofReal ((min (u x) (N : ℝ≥0∞)).toReal) = min (u x) (N : ℝ≥0∞) :=
      fun u x => ENNReal.ofReal_toReal (hmin u N x)
    simp only [hof] at hPL
    exact hPL.trans (lintegral_mono fun z => min_le_left _ _)
  have hmono : ∀ u : ℝ → ℝ≥0∞, Monotone fun N : ℕ => ∫⁻ x, min (u x) (N : ℝ≥0∞) :=
    fun u a b hab => lintegral_mono fun x => min_le_min le_rfl (by exact_mod_cast hab)
  have hsup : ∀ u : ℝ → ℝ≥0∞, Measurable u →
      (⨆ N : ℕ, ∫⁻ x, min (u x) (N : ℝ≥0∞)) = ∫⁻ x, u x := by
    intro u hu
    rw [← lintegral_iSup (fun N => hu.min measurable_const)
      (fun a b hab x => min_le_min le_rfl (by exact_mod_cast hab))]
    exact lintegral_congr fun x => iSup_min_natCast (u x)
  rw [← hsup f hf, ← hsup g hg, rpow_iSup _ ht0, rpow_iSup _ ht1', ENNReal.iSup_mul]
  refine iSup_le fun N => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun M => ?_
  exact le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (hmono f (le_max_left N M)) ht0.le)
    (ENNReal.rpow_le_rpow (hmono g (le_max_right N M)) ht1'.le)) (hstep (max N M))

private theorem IsPL.comp {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} {t : ℝ}
    (hX : IsPL X μ t) {e : X → Y} (hmp : MeasurePreserving e μ ν)
    (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y) : IsPL Y ν t := by
  intro f g h hf hg hh hfgh
  have hyp : ∀ x y : X, (f ∘ e) x ^ t * ((g ∘ e) y) ^ (1 - t)
      ≤ (h ∘ e) (t • x + (1 - t) • y) := by
    intro x y
    simp only [Function.comp_apply, hlin]
    exact hfgh (e x) (e y)
  have h1 := hX (f ∘ e) (g ∘ e) (h ∘ e) (hf.comp hmp.measurable) (hg.comp hmp.measurable)
    (hh.comp hmp.measurable) hyp
  simp only [Function.comp_apply] at h1
  rwa [hmp.lintegral_comp hf, hmp.lintegral_comp hg, hmp.lintegral_comp hh] at h1

private theorem IsPL.symm {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} {t : ℝ}
    (hY : IsPL Y ν t) (e : X ≃ᵐ Y) (hmp : MeasurePreserving e μ ν)
    (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y) : IsPL X μ t := by
  refine hY.comp (e := ⇑e.symm) (hmp.symm e) ?_
  intro a b x y
  refine e.injective ?_
  rw [hlin, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]

private theorem IsPL.prod {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {t : ℝ}
    (hX : IsPL X μ t) (hY : IsPL Y ν t) : IsPL (X × Y) (μ.prod ν) t := by
  intro f g h hf hg hh hfgh
  have hslice : ∀ (u : X × Y → ℝ≥0∞), Measurable u → ∀ x : X, Measurable fun y => u (x, y) :=
    fun u hu x => hu.comp (measurable_const.prodMk measurable_id)
  have hFGH : ∀ x₁ x₂ : X,
      (∫⁻ y, f (x₁, y) ∂ν) ^ t * (∫⁻ y, g (x₂, y) ∂ν) ^ (1 - t)
        ≤ ∫⁻ y, h (t • x₁ + (1 - t) • x₂, y) ∂ν := by
    intro x₁ x₂
    refine hY (fun y => f (x₁, y)) (fun y => g (x₂, y))
      (fun y => h (t • x₁ + (1 - t) • x₂, y)) (hslice f hf x₁) (hslice g hg x₂)
      (hslice h hh _) ?_
    intro y₁ y₂
    have hxy := hfgh (x₁, y₁) (x₂, y₂)
    simpa [Prod.smul_mk, Prod.mk_add_mk] using hxy
  have h1 := hX (fun x => ∫⁻ y, f (x, y) ∂ν) (fun x => ∫⁻ y, g (x, y) ∂ν)
    (fun x => ∫⁻ y, h (x, y) ∂ν) hf.lintegral_prod_right' hg.lintegral_prod_right'
    hh.lintegral_prod_right' hFGH
  rwa [← lintegral_prod _ hf.aemeasurable, ← lintegral_prod _ hg.aemeasurable,
    ← lintegral_prod _ hh.aemeasurable] at h1

private theorem isPL_pi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ n : ℕ, IsPL (Fin n → ℝ) (volume : Measure (Fin n → ℝ)) t
  | 0 => by
      intro f g h hf hg hh hfgh
      rw [Measure.volume_pi_eq_dirac 0, lintegral_dirac' _ hf, lintegral_dirac' _ hg,
        lintegral_dirac' _ hh]
      simpa using hfgh 0 0
  | (n + 1) => by
      have hprod : IsPL (ℝ × (Fin n → ℝ)) (volume : Measure (ℝ × (Fin n → ℝ))) t := by
        rw [show (volume : Measure (ℝ × (Fin n → ℝ)))
          = (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) from rfl]
        exact (isPL_real ht0 ht1).prod (isPL_pi ht0 ht1 n)
      exact hprod.symm (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)
        (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0) (by intro a b x y; rfl)

private theorem isPL_euclidean {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    IsPL (EuclideanSpace ℝ (Fin n)) (volume : Measure (EuclideanSpace ℝ (Fin n))) t :=
  (isPL_pi ht0 ht1 n).comp (PiLp.volume_preserving_toLp (Fin n)) (by intro a b x y; rfl)

private theorem isPL_volume {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) : IsPL E (volume : Measure E) t :=
  (isPL_euclidean ht0 ht1 (Module.finrank ℝ E)).comp
    ((stdOrthonormalBasis ℝ E).measurePreserving_repr_symm)
    (by intro a b x y; simp)

/-- **Prékopa–Leindler inequality** on a finite-dimensional inner-product space, for Lebesgue
measure.  The one-dimensional case is `FunctionalInequalities.Probability.Line.prekopaLeindler`;
the general case follows by induction on the dimension and Fubini along a line. -/
theorem prekopaLeindler {f g h : V → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hfgh : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, ENNReal.ofReal (f x)) ^ t * (∫⁻ y, ENNReal.ofReal (g y)) ^ (1 - t) ≤
      ∫⁻ z, ENNReal.ofReal (h z) := by
  have ht1' : (0:ℝ) < 1 - t := by linarith
  refine isPL_volume ht0 ht1 (fun x => ENNReal.ofReal (f x)) (fun y => ENNReal.ofReal (g y))
    (fun z => ENNReal.ofReal (h z)) hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal ?_
  intro x y
  rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (hg0 y) ht1'.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) t)]
  exact ENNReal.ofReal_le_ofReal (hfgh x y)

/-- **Multiplicative Brunn–Minkowski inequality**: a convex combination of two nonempty measurable
sets carries at least the geometric mean of their volumes.  The combination set need not be
measurable; the outer-measure bound is what is used. -/
theorem volume_rpow_mul_le_volume_combination {S T : Set V} (hS : MeasurableSet S)
    (hSne : S.Nonempty) (hT : MeasurableSet T) (hTne : T.Nonempty) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    volume S ^ t * volume T ^ (1 - t) ≤
      volume {z : V | ∃ x ∈ S, ∃ y ∈ T, z = t • x + (1 - t) • y} := by
  have ht1' : (0:ℝ) < 1 - t := by linarith
  set C := {z : V | ∃ x ∈ S, ∃ y ∈ T, z = t • x + (1 - t) • y} with hC
  have hind : ∀ A : Set V, MeasurableSet A →
      ∫⁻ x, ENNReal.ofReal (A.indicator (fun _ => (1:ℝ)) x) = volume A := by
    intro A hA
    rw [← lintegral_indicator_one hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A <;> simp [hx]
  have key : ∀ K : Set V, K ⊆ S → IsCompact K →
      ∀ L : Set V, L ⊆ T → IsCompact L →
      volume K ^ t * volume L ^ (1 - t) ≤ volume C := by
    intro K hKS hK L hLT hL
    set D := t • K + (1 - t) • L with hD
    have hDc : IsCompact D := (hK.smul t).add (hL.smul (1 - t))
    have hDS : D ⊆ C := by
      rintro _ ⟨-, ⟨x, hx, rfl⟩, -, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x, hKS hx, y, hLT hy, rfl⟩
    have hhyp : ∀ x y : V, (K.indicator (fun _ => (1:ℝ)) x) ^ t *
        (L.indicator (fun _ => (1:ℝ)) y) ^ (1 - t) ≤
        D.indicator (fun _ => (1:ℝ)) (t • x + (1 - t) • y) := by
      intro x y
      by_cases hx : x ∈ K
      · by_cases hy : y ∈ L
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
            Set.indicator_of_mem (show t • x + (1 - t) • y ∈ D from
              ⟨t • x, ⟨x, hx, rfl⟩, (1 - t) • y, ⟨y, hy, rfl⟩, rfl⟩)]
          simp
        · rw [Set.indicator_of_notMem hy, Real.zero_rpow ht1'.ne', mul_zero]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      · rw [Set.indicator_of_notMem hx, Real.zero_rpow ht0.ne', zero_mul]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hPL := prekopaLeindler (measurable_const.indicator hK.measurableSet)
      (measurable_const.indicator hL.measurableSet)
      (measurable_const.indicator hDc.measurableSet)
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x) ht0 ht1 hhyp
    rw [hind K hK.measurableSet, hind L hL.measurableSet, hind D hDc.measurableSet] at hPL
    exact hPL.trans (measure_mono hDS)
  have hsup : ∀ U : Set V, MeasurableSet U → U.Nonempty →
      volume U = ⨆ K : {K : Set V // K ⊆ U ∧ IsCompact K ∧ K.Nonempty}, volume (K : Set V) := by
    intro U hU hUne
    refine le_antisymm ?_ (iSup_le fun K ↦ measure_mono K.2.1)
    rw [hU.measure_eq_iSup_isCompact volume]
    refine iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦ ?_
    obtain ⟨x₀, hx₀⟩ := hUne
    exact le_iSup_of_le ⟨K ∪ {x₀}, Set.union_subset hKU (by simpa using hx₀),
      hK.union isCompact_singleton, ⟨x₀, by simp⟩⟩ (measure_mono Set.subset_union_left)
  obtain ⟨s₀, hs₀⟩ := hSne
  obtain ⟨t₀, ht₀⟩ := hTne
  have hnS : Nonempty {K : Set V // K ⊆ S ∧ IsCompact K ∧ K.Nonempty} :=
    ⟨⟨{s₀}, by simpa using hs₀, isCompact_singleton, ⟨s₀, rfl⟩⟩⟩
  have hnT : Nonempty {L : Set V // L ⊆ T ∧ IsCompact L ∧ L.Nonempty} :=
    ⟨⟨{t₀}, by simpa using ht₀, isCompact_singleton, ⟨t₀, rfl⟩⟩⟩
  rw [hsup S hS ⟨s₀, hs₀⟩, hsup T hT ⟨t₀, ht₀⟩, rpow_iSup _ ht0, rpow_iSup _ ht1',
    ENNReal.iSup_mul]
  refine iSup_le fun K ↦ ?_
  rw [ENNReal.mul_iSup]
  exact iSup_le fun L ↦ key (K : Set V) K.2.1 K.2.2.1 (L : Set V) L.2.1 L.2.2.1

/-- **Brunn–Minkowski inequality** in its additive form for nonempty compact sets in dimension
`n ≥ 1`: `|S|^{1/n} + |T|^{1/n} ≤ |S + T|^{1/n}`. -/
theorem volume_rpow_add_le_volume_add_rpow [Nontrivial V] {S T : Set V} (hS : IsCompact S)
    (hT : IsCompact T) (hSne : S.Nonempty) (hTne : T.Nonempty) :
    volume S ^ (1 / (Module.finrank ℝ V : ℝ)) + volume T ^ (1 / (Module.finrank ℝ V : ℝ)) ≤
      volume (S + T) ^ (1 / (Module.finrank ℝ V : ℝ)) := by
  have hmono : ∀ {A B : Set V}, A.Nonempty → volume B ≤ volume (A + B) := by
    rintro A B ⟨a, ha⟩
    have hsub : (a + ·) '' B ⊆ A + B := by
      rintro _ ⟨b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
    calc volume B = volume ((a + ·) '' B) := by
          rw [Set.image_add_left, measure_preimage_add]
      _ ≤ volume (A + B) := measure_mono hsub
  have hmono' : volume S ≤ volume (S + T) := by
    rw [add_comm]; exact hmono hTne
  set n := Module.finrank ℝ V with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hexp : (0:ℝ) ≤ 1 / n := by positivity
  -- degenerate cases
  by_cases hA : volume S = 0
  · rw [hA, ENNReal.zero_rpow_of_pos (by positivity), zero_add]
    exact ENNReal.rpow_le_rpow (hmono hSne) hexp
  by_cases hB : volume T = 0
  · rw [hB, ENNReal.zero_rpow_of_pos (by positivity), add_zero]
    exact ENNReal.rpow_le_rpow hmono' hexp
  have hAtop : volume S ≠ ⊤ := hS.measure_lt_top.ne
  have hBtop : volume T ≠ ⊤ := hT.measure_lt_top.ne
  set α : ℝ := (volume S).toReal ^ ((1:ℝ) / n) with hα
  set β : ℝ := (volume T).toReal ^ ((1:ℝ) / n) with hβ
  have hApos : 0 < (volume S).toReal := ENNReal.toReal_pos hA hAtop
  have hBpos : 0 < (volume T).toReal := ENNReal.toReal_pos hB hBtop
  have hαpos : 0 < α := Real.rpow_pos_of_pos hApos _
  have hβpos : 0 < β := Real.rpow_pos_of_pos hBpos _
  have hαn : α ^ n = (volume S).toReal := by
    rw [hα, ← Real.rpow_natCast (_ ^ _) n, ← Real.rpow_mul hApos.le]
    rw [one_div, inv_mul_cancel₀ hnR.ne', Real.rpow_one]
  have hβn : β ^ n = (volume T).toReal := by
    rw [hβ, ← Real.rpow_natCast (_ ^ _) n, ← Real.rpow_mul hBpos.le]
    rw [one_div, inv_mul_cancel₀ hnR.ne', Real.rpow_one]
  have hαE : ENNReal.ofReal α = volume S ^ ((1:ℝ) / n) := by
    rw [hα, ← ENNReal.ofReal_rpow_of_nonneg hApos.le hexp, ENNReal.ofReal_toReal hAtop]
  have hβE : ENNReal.ofReal β = volume T ^ ((1:ℝ) / n) := by
    rw [hβ, ← ENNReal.ofReal_rpow_of_nonneg hBpos.le hexp, ENNReal.ofReal_toReal hBtop]
  set c : ℝ := α + β with hc
  have hcpos : 0 < c := by positivity
  set t : ℝ := α / c with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hcpos, hc]; linarith
  have h1t : 1 - t = β / c := by rw [ht, hc]; field_simp; ring
  have e1 : t * α⁻¹ = c⁻¹ := by rw [ht]; field_simp
  have e2 : (1 - t) * β⁻¹ = c⁻¹ := by rw [h1t]; field_simp
  have hS'c : IsCompact (α⁻¹ • S) := by
    rw [← Set.image_smul]; exact hS.image (continuous_const_smul _)
  have hT'c : IsCompact (β⁻¹ • T) := by
    rw [← Set.image_smul]; exact hT.image (continuous_const_smul _)
  have hvolS' : volume (α⁻¹ • S) = 1 := by
    rw [Measure.addHaar_smul_of_nonneg _ (by positivity), inv_pow, hαn,
      ENNReal.ofReal_inv_of_pos hApos, ENNReal.ofReal_toReal hAtop,
      ENNReal.inv_mul_cancel hA hAtop]
  have hvolT' : volume (β⁻¹ • T) = 1 := by
    rw [Measure.addHaar_smul_of_nonneg _ (by positivity), inv_pow, hβn,
      ENNReal.ofReal_inv_of_pos hBpos, ENNReal.ofReal_toReal hBtop,
      ENNReal.inv_mul_cancel hB hBtop]
  have hset : {z : V | ∃ x ∈ α⁻¹ • S, ∃ y ∈ β⁻¹ • T, z = t • x + (1 - t) • y}
      = c⁻¹ • (S + T) := by
    ext z
    constructor
    · rintro ⟨-, ⟨x, hx, rfl⟩, -, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, by
        rw [smul_smul, smul_smul, e1, e2, ← smul_add]⟩
    · rintro ⟨-, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨α⁻¹ • x, ⟨x, hx, rfl⟩, β⁻¹ • y, ⟨y, hy, rfl⟩, by
        rw [smul_smul, smul_smul, e1, e2, ← smul_add]⟩
  have hBM := volume_rpow_mul_le_volume_combination hS'c.measurableSet (hSne.image _) hT'c.measurableSet (hTne.image _) ht0 ht1
  rw [hvolS', hvolT', ENNReal.one_rpow, ENNReal.one_rpow, one_mul, hset,
    Measure.addHaar_smul_of_nonneg _ (by positivity : (0:ℝ) ≤ c⁻¹), inv_pow,
    ENNReal.ofReal_inv_of_pos (by positivity)] at hBM
  have hK0 : ENNReal.ofReal (c ^ n) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hKtop : ENNReal.ofReal (c ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmain : ENNReal.ofReal (c ^ n) ≤ volume (S + T) := by
    calc ENNReal.ofReal (c ^ n) = ENNReal.ofReal (c ^ n) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (c ^ n) * ((ENNReal.ofReal (c ^ n))⁻¹ * volume (S + T)) :=
          by gcongr
      _ = volume (S + T) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hK0 hKtop, one_mul]
  calc volume S ^ ((1:ℝ) / n) + volume T ^ ((1:ℝ) / n)
      = ENNReal.ofReal α + ENNReal.ofReal β := by rw [hαE, hβE]
    _ = ENNReal.ofReal c := (ENNReal.ofReal_add hαpos.le hβpos.le).symm
    _ = ENNReal.ofReal (c ^ n) ^ ((1:ℝ) / n) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hexp]
        congr 1
        rw [← Real.rpow_natCast c n, ← Real.rpow_mul hcpos.le, mul_one_div, div_self hnR.ne',
          Real.rpow_one]
    _ ≤ volume (S + T) ^ ((1:ℝ) / n) := ENNReal.rpow_le_rpow hmain hexp

/-- **Isodiametric inequality**: a bounded set of diameter `d` has Lebesgue measure at most
`ω_n (d / 2)^n`, the volume of a ball of diameter `d`.  Stated for bounded sets with `Metric.diam`
because `Metric.diam` of an unbounded set is `0`; for unbounded sets the right-hand side with
`EMetric.diam` would be `⊤` in positive dimension and the statement is vacuous.  No measurability
is assumed: `volume` is the outer measure, and `closure S` has the same diameter. -/
theorem isodiametric (S : Set V) (hS : Bornology.IsBounded S) :
    volume S ≤ ENNReal.ofReal
      (KLS.unitBallVolume (Module.finrank ℝ V) * (Metric.diam S / 2) ^ Module.finrank ℝ V) := by
  rcases Set.eq_empty_or_nonempty S with rfl | hSne
  · simp
  have hdiam0 : (0:ℝ) ≤ Metric.diam S := Metric.diam_nonneg
  have hω0 : (0:ℝ) ≤ KLS.unitBallVolume (Module.finrank ℝ V) := by
    unfold KLS.unitBallVolume; positivity
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · have hn0 : Module.finrank ℝ V = 0 := Module.finrank_zero_of_subsingleton
    rw [hn0, pow_zero, mul_one, show KLS.unitBallVolume 0 = 1 by simp [KLS.unitBallVolume],
      ENNReal.ofReal_one]
    refine (measure_mono (Set.subset_univ _)).trans ?_
    have hb := (stdOrthonormalBasis ℝ V).toBasis.addHaar_self
    have hne : (parallelepiped ((stdOrthonormalBasis ℝ V).toBasis)).Nonempty :=
      ⟨0, 0, by simp, by simp⟩
    rw [Subsingleton.eq_univ_of_nonempty hne] at hb
    exact hb.le
  -- the nondegenerate case
  set C := closure S with hC
  have hCc : IsCompact C := hS.isCompact_closure
  have hCne : C.Nonempty := hSne.closure
  have hCb : Bornology.IsBounded C := hCc.isBounded
  have hCdiam : Metric.diam C = Metric.diam S := Metric.diam_closure S
  have hCtop : volume C ≠ ⊤ := hCc.measure_lt_top.ne
  by_cases hC0 : volume C = 0
  · exact le_trans ((measure_mono subset_closure).trans hC0.le) (by simp)
  set T : Set V := (-1 : ℝ) • C with hT
  have hTc : IsCompact T := by rw [hT, ← Set.image_smul]; exact hCc.image (continuous_const_smul _)
  have hTne : T.Nonempty := hCne.image _
  have hTvol : volume T = volume C := by
    rw [hT, Measure.addHaar_smul]
    simp
  have hsub : {z : V | ∃ x ∈ C, ∃ y ∈ T, z = (1/2 : ℝ) • x + (1 - 1/2 : ℝ) • y}
      ⊆ Metric.closedBall (0 : V) (Metric.diam S / 2) := by
    rintro _ ⟨x, hx, -, ⟨y, hy, rfl⟩, rfl⟩
    have hxy : ‖x - y‖ ≤ Metric.diam S := by
      rw [← dist_eq_norm, ← hCdiam]
      exact Metric.dist_le_diam_of_mem hCb hx hy
    simp only [Metric.mem_closedBall, dist_zero_right]
    have : (1/2 : ℝ) • x + (1 - 1/2 : ℝ) • ((-1 : ℝ) • y) = (1/2 : ℝ) • (x - y) := by
      rw [smul_smul]; module
    rw [this, norm_smul]
    simp only [one_div, norm_inv, Real.norm_ofNat]
    rw [inv_mul_eq_div, div_le_div_iff_of_pos_right (by norm_num)]
    exact hxy
  have hBM := volume_rpow_mul_le_volume_combination hCc.measurableSet hCne hTc.measurableSet hTne
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  rw [hTvol] at hBM
  have hhalf : volume C ^ (1/2 : ℝ) * volume C ^ (1 - 1/2 : ℝ) = volume C := by
    rw [← ENNReal.rpow_add_of_nonneg (x := volume C) (1/2) (1 - 1/2) (by norm_num)
      (by norm_num)]
    simp
  rw [hhalf] at hBM
  calc volume S ≤ volume C := measure_mono subset_closure
    _ ≤ volume (Metric.closedBall (0 : V) (Metric.diam S / 2)) :=
        le_trans hBM (measure_mono hsub)
    _ = ENNReal.ofReal (KLS.unitBallVolume (Module.finrank ℝ V)
          * (Metric.diam S / 2) ^ Module.finrank ℝ V) := by
        rw [InnerProductSpace.volume_closedBall, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), KLS.unitBallVolume]
        ring_nf

/-- One half of the normalization identity, by covering: `volume ≤ (ω_n / 2^n) • μH[n]`. -/
theorem volume_le_ofReal_mul_hausdorffMeasure (S : Set V) :
    volume S ≤
      ENNReal.ofReal (KLS.unitBallVolume (Module.finrank ℝ V) / 2 ^ Module.finrank ℝ V) *
        μH[(Module.finrank ℝ V : ℝ)] S := by
  have hωpos : 0 < KLS.unitBallVolume (Module.finrank ℝ V) := by
    unfold KLS.unitBallVolume
    positivity
  have hkey : (ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
      • (volume : Measure V)) ≤ μH[(Module.finrank ℝ V : ℝ)] := by
    refine Measure.le_hausdorffMeasure (Module.finrank ℝ V : ℝ) _ 1 one_pos ?_
    intro s hs
    have hb : Bornology.IsBounded s :=
      Metric.isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top ENNReal.one_ne_top hs)
    have hd0 : (0:ℝ) ≤ Metric.diam s := Metric.diam_nonneg
    rw [Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
          * volume s
        ≤ ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
          * ENNReal.ofReal (KLS.unitBallVolume (Module.finrank ℝ V)
            * (Metric.diam s / 2) ^ Module.finrank ℝ V) := by
          gcongr
          exact isodiametric s hb
      _ = ENNReal.ofReal (Metric.diam s ^ Module.finrank ℝ V) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_pow]
          field_simp
      _ = Metric.ediam s ^ (Module.finrank ℝ V : ℝ) := by
          have hdiam : ENNReal.ofReal (Metric.diam s) = Metric.ediam s := by
            unfold Metric.diam
            rw [ENNReal.ofReal_toReal hb.ediam_ne_top]
          rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow hd0, hdiam]
  have := (Measure.le_iff'.mp hkey) S
  rw [Measure.smul_apply, smul_eq_mul] at this
  calc volume S
      = ENNReal.ofReal (KLS.unitBallVolume (Module.finrank ℝ V) / 2 ^ Module.finrank ℝ V)
        * (ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
          * volume S) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [show KLS.unitBallVolume (Module.finrank ℝ V) / 2 ^ Module.finrank ℝ V
            * (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V)) = 1 by
          field_simp]
        simp
    _ ≤ _ := by gcongr

/-- The unit ball has `μH[n]`-measure at most `2^n / ω_n` times its Lebesgue measure: a
Besicovitch covering by disjoint balls of vanishing radius, at each scale of the `mkMetric`
premeasure.  The leftover set is Lebesgue-null, hence `μH[n]`-null by Haar uniqueness. -/
private theorem hausdorffMeasure_ball_le [Nontrivial V] :
    (μH[(Module.finrank ℝ V : ℝ)] : Measure V) (Metric.ball 0 1)
      ≤ ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V))
        * volume (Metric.ball (0:V) 1) := by
  set n := Module.finrank ℝ V with hn
  have hωpos : 0 < KLS.unitBallVolume n := by unfold KLS.unitBallVolume; positivity
  have hsmul : (μH[(n : ℝ)] : Measure V)
      = (((μH[(n : ℝ)] : Measure V).addHaarScalarFactor (volume : Measure V) : ℝ≥0) : ℝ≥0∞)
        • (volume : Measure V) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set P : ℕ → OuterMeasure V := fun k =>
    OuterMeasure.mkMetric'.pre (fun s : Set V => (Metric.ediam s) ^ (n : ℝ)) (k : ℝ≥0∞)⁻¹ with hP
  have hcoe : ∀ s : Set V, (μH[(n : ℝ)] : Measure V) s = ⨆ k : ℕ, P k s := by
    intro s
    have h1 : (μH[(n : ℝ)] : Measure V) s
        = (OuterMeasure.mkMetric (fun r : ℝ≥0∞ => r ^ (n : ℝ)) : OuterMeasure V) s := by
      rw [OuterMeasure.coe_mkMetric]; rfl
    rw [h1, show (OuterMeasure.mkMetric (fun r : ℝ≥0∞ => r ^ (n : ℝ)) : OuterMeasure V)
      = OuterMeasure.mkMetric' (fun s : Set V => (Metric.ediam s) ^ (n : ℝ)) from rfl,
      OuterMeasure.mkMetric'.eq_iSup_nat, OuterMeasure.iSup_apply]
  have hPle : ∀ (k : ℕ) (s : Set V), P k s ≤ (μH[(n : ℝ)] : Measure V) s := by
    intro k s
    rw [hcoe s]
    exact le_iSup (fun j : ℕ => P j s) k
  rw [hcoe]
  refine iSup_le fun k => ?_
  set δ : ℝ := 1 / (4 * ((k : ℝ) + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨t, r, htc, hts, hr, hnull, hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae (volume : Measure V)
      (fun _ => Set.Ioo 0 δ) (Metric.ball (0 : V) 1)
      (fun x _ δ' hδ' => ⟨min δ δ' / 2, ⟨by positivity, by
          have := min_le_left δ δ'; linarith⟩, ⟨by positivity, by
          have := min_le_right δ δ'; linarith⟩⟩)
      (fun x => min δ (1 - ‖x‖))
      (fun x hx => lt_min hδpos (by
        have : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
        linarith))
  have hsub : ∀ x ∈ t, Metric.closedBall x (r x) ⊆ Metric.ball (0 : V) 1 := by
    intro x hx y hy
    have hrx := (hr x hx).2
    have hx1 : ‖x‖ < 1 := by
      have := hts hx; simpa [Metric.mem_ball, dist_zero_right] using this
    have h1 : ‖y - x‖ ≤ r x := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hy
    have h2 : r x < 1 - ‖x‖ := lt_of_lt_of_le hrx.2 (min_le_right _ _)
    have : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hediam : ∀ x ∈ t, Metric.ediam (Metric.closedBall x (r x))
      ≤ ENNReal.ofReal (2 * r x) := by
    intro x hx
    have hbd : Bornology.IsBounded (Metric.closedBall x (r x)) := Metric.isBounded_closedBall
    have h0 : (0:ℝ) ≤ r x := (hr x hx).2.1.le
    have : Metric.ediam (Metric.closedBall x (r x))
        = ENNReal.ofReal (Metric.diam (Metric.closedBall x (r x))) := by
      unfold Metric.diam
      rw [ENNReal.ofReal_toReal hbd.ediam_ne_top]
    rw [this]
    exact ENNReal.ofReal_le_ofReal (Metric.diam_closedBall h0)
  have hsmall : ∀ x ∈ t, Metric.ediam (Metric.closedBall x (r x)) ≤ (k : ℝ≥0∞)⁻¹ := by
    intro x hx
    refine (hediam x hx).trans ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkpos : (0:ℝ) < (k : ℝ) := by linarith
      have hcast : ((k : ℕ) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (k : ℝ)) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos hkpos, ENNReal.ofReal_natCast]
      rw [hcast]
      refine ENNReal.ofReal_le_ofReal ?_
      have hrx : r x < δ := (hr x hx).1.2
      rw [hδdef] at hrx
      have hpos4 : (0:ℝ) < 4 * ((k:ℝ) + 1) := by positivity
      have hrx' : r x * (4 * ((k:ℝ) + 1)) < 1 := (lt_div_iff₀ hpos4).mp hrx
      have hr0 : 0 < r x := (hr x hx).1.1
      rw [le_div_iff₀ hkpos]
      nlinarith
  have hcover : Metric.ball (0:V) 1 ⊆ (⋃ x ∈ t, Metric.closedBall x (r x))
      ∪ (Metric.ball (0:V) 1 \ ⋃ x ∈ t, Metric.closedBall x (r x)) := by
    intro y hy
    by_cases hmem : y ∈ ⋃ x ∈ t, Metric.closedBall x (r x)
    · exact Or.inl hmem
    · exact Or.inr ⟨hy, hmem⟩
  have hdiff0 : P k (Metric.ball (0:V) 1 \ ⋃ x ∈ t, Metric.closedBall x (r x)) = 0 := by
    refine le_antisymm ((hPle k _).trans ?_) (by simp)
    rw [hsmul, Measure.smul_apply, smul_eq_mul, hnull, mul_zero]
  have hterm : ∀ x ∈ t, P k (Metric.closedBall x (r x))
      ≤ ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) * volume (Metric.closedBall x (r x)) := by
    intro x hx
    have hr0 : 0 < r x := (hr x hx).1.1
    have h1 : P k (Metric.closedBall x (r x))
        ≤ (Metric.ediam (Metric.closedBall x (r x))) ^ (n : ℝ) :=
      OuterMeasure.mkMetric'.pre_le (hsmall x hx)
    have h2 : (Metric.ediam (Metric.closedBall x (r x))) ^ (n : ℝ)
        ≤ (ENNReal.ofReal (2 * r x)) ^ (n : ℝ) :=
      ENNReal.rpow_le_rpow (hediam x hx) (Nat.cast_nonneg _)
    have h3 : (ENNReal.ofReal (2 * r x)) ^ (n : ℝ)
        = ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) * volume (Metric.closedBall x (r x)) := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by positivity),
        InnerProductSpace.volume_closedBall, ← ENNReal.ofReal_pow hr0.le,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold KLS.unitBallVolume
      field_simp
      ring
    exact (h1.trans h2).trans_eq h3
  calc P k (Metric.ball (0:V) 1)
      ≤ P k (⋃ x ∈ t, Metric.closedBall x (r x))
        + P k (Metric.ball (0:V) 1 \ ⋃ x ∈ t, Metric.closedBall x (r x)) :=
        le_trans (measure_mono hcover) (measure_union_le _ _)
    _ = P k (⋃ x ∈ t, Metric.closedBall x (r x)) := by rw [hdiff0, add_zero]
    _ ≤ ∑' x : t, P k (Metric.closedBall (x : V) (r x)) := measure_biUnion_le _ htc _
    _ ≤ ∑' x : t, ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
          * volume (Metric.closedBall (x : V) (r x)) :=
        ENNReal.tsum_le_tsum fun x => hterm (x : V) x.2
    _ = ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
          * ∑' x : t, volume (Metric.closedBall (x : V) (r x)) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
          * volume (⋃ x ∈ t, Metric.closedBall x (r x)) := by
        rw [measure_biUnion htc hdisj fun b _ => measurableSet_closedBall]
    _ ≤ ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) * volume (Metric.ball (0:V) 1) := by
        gcongr
        exact Set.iUnion₂_subset hsub

variable (V) in
/-- Mathlib's top-dimensional Hausdorff measure of a finite-dimensional inner-product space is
`2^n / ω_n` times Lebesgue measure.  General form of `KLS.hausdorffNormalized_finrank_eq_volume`:
multiplying by `ENNReal.ofReal (ω_n / 2^n)` recovers `hausdorffNormalized V n = volume`. -/
theorem hausdorffMeasure_finrank_eq_smul_volume :
    (μH[(Module.finrank ℝ V : ℝ)] : Measure V) =
      ENNReal.ofReal (2 ^ Module.finrank ℝ V / KLS.unitBallVolume (Module.finrank ℝ V)) •
        (volume : Measure V) := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · have hn0 : Module.finrank ℝ V = 0 := Module.finrank_zero_of_subsingleton
    have hval : (2 : ℝ) ^ (0 : ℕ) / KLS.unitBallVolume 0 = 1 := by simp [KLS.unitBallVolume]
    rw [hn0, hval, ENNReal.ofReal_one, one_smul, Nat.cast_zero]
    have hvolU : (volume : Measure V) Set.univ = 1 := by
      have hb := (stdOrthonormalBasis ℝ V).toBasis.addHaar_self
      have hne : (parallelepiped ((stdOrthonormalBasis ℝ V).toBasis)).Nonempty :=
        ⟨0, 0, by simp, by simp⟩
      rw [Subsingleton.eq_univ_of_nonempty hne] at hb
      exact hb
    have hHU : (μH[(0 : ℝ)] : Measure V) Set.univ = 1 := by
      rw [show (Set.univ : Set V) = {(0 : V)} from
        (Subsingleton.eq_univ_of_nonempty (Set.singleton_nonempty (0 : V))).symm]
      exact Measure.hausdorffMeasure_zero_singleton 0
    refine Measure.ext fun s _ => ?_
    rcases Set.eq_empty_or_nonempty s with rfl | hne
    · simp
    · rw [Subsingleton.eq_univ_of_nonempty hne, hHU, hvolU]
  · set n := Module.finrank ℝ V with hn
    have hωpos : 0 < KLS.unitBallVolume n := by unfold KLS.unitBallVolume; positivity
    have hsmul : (μH[(n : ℝ)] : Measure V)
        = (((μH[(n : ℝ)] : Measure V).addHaarScalarFactor (volume : Measure V) : ℝ≥0) : ℝ≥0∞)
          • (volume : Measure V) :=
      Measure.isAddLeftInvariant_eq_smul _ _
    set c : ℝ≥0 := (μH[(n : ℝ)] : Measure V).addHaarScalarFactor (volume : Measure V) with hcdef
    have hball : volume (Metric.ball (0 : V) 1) = ENNReal.ofReal (KLS.unitBallVolume n) := by
      rw [InnerProductSpace.volume_ball, hn]
      simp [KLS.unitBallVolume]
    have hV0 : volume (Metric.ball (0 : V) 1) ≠ 0 := by
      rw [hball]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hωpos
    have hVtop : volume (Metric.ball (0 : V) 1) ≠ ⊤ := by rw [hball]; exact ENNReal.ofReal_ne_top
    have hcancel : ∀ a b : ℝ≥0∞, a * volume (Metric.ball (0 : V) 1)
        ≤ b * volume (Metric.ball (0 : V) 1) → a ≤ b := by
      intro a b hab
      calc a = a * volume (Metric.ball (0 : V) 1) * (volume (Metric.ball (0 : V) 1))⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel hV0 hVtop, mul_one]
        _ ≤ b * volume (Metric.ball (0 : V) 1) * (volume (Metric.ball (0 : V) 1))⁻¹ := by gcongr
        _ = b := by rw [mul_assoc, ENNReal.mul_inv_cancel hV0 hVtop, mul_one]
    have hle : (c : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) := by
      refine hcancel _ _ ?_
      have := hausdorffMeasure_ball_le (V := V)
      rwa [hsmul, Measure.smul_apply, smul_eq_mul] at this
    have hge : ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) ≤ (c : ℝ≥0∞) := by
      have hlow := volume_le_ofReal_mul_hausdorffMeasure (Metric.ball (0 : V) 1)
      rw [hsmul, Measure.smul_apply, smul_eq_mul] at hlow
      have h1 : (1 : ℝ≥0∞) * volume (Metric.ball (0 : V) 1)
          ≤ (ENNReal.ofReal (KLS.unitBallVolume n / 2 ^ n) * c)
            * volume (Metric.ball (0 : V) 1) := by
        rw [one_mul, mul_assoc]
        exact hlow
      have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (KLS.unitBallVolume n / 2 ^ n) * c := hcancel _ _ h1
      calc ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
          = ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n) * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal (2 ^ n / KLS.unitBallVolume n)
              * (ENNReal.ofReal (KLS.unitBallVolume n / 2 ^ n) * c) := by gcongr
        _ = c := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              show 2 ^ n / KLS.unitBallVolume n * (KLS.unitBallVolume n / 2 ^ n) = 1 by
                field_simp, ENNReal.ofReal_one, one_mul]
    rw [hsmul, le_antisymm hle hge]

end Isodiametric

/-! ### B. Regular level sets are locally Lipschitz graphs of finite `ℋ^{n-1}` -/

section LipschitzGraph

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Lipschitz-graph form of the implicit function theorem: near a regular point `x` of a `C¹`
function, the level set through `x` is contained in the image of a bounded subset of the tangent
hyperplane `ker (Dφ x)` under a Lipschitz map.  No finite-dimensionality is needed; completeness
is what the implicit function theorem uses. -/
theorem exists_lipschitzOnWith_levelSet_subset_image {φ : V → ℝ} (hφ : ContDiff ℝ 1 φ) {x : V}
    (hx : fderiv ℝ φ x ≠ 0) :
    ∃ (N : Set V) (K : ℝ≥0) (s : Set (LinearMap.ker (fderiv ℝ φ x).toLinearMap))
      (g : LinearMap.ker (fderiv ℝ φ x).toLinearMap → V),
      N ∈ 𝓝 x ∧ Bornology.IsBounded s ∧ LipschitzOnWith K g s ∧
        N ∩ {y | φ y = φ x} ⊆ g '' s := by
  classical
  have hne : (fderiv ℝ φ x).toLinearMap ≠ 0 := fun h =>
    hx (ContinuousLinearMap.coe_injective (h.trans ContinuousLinearMap.toLinearMap_zero.symm))
  have hrange : (fderiv ℝ φ x).range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hne
  have hstrict : HasStrictFDerivAt φ (fderiv ℝ φ x) x := hφ.hasStrictFDerivAt one_ne_zero
  have hker : (fderiv ℝ φ x).ker.ClosedComplemented :=
    (fderiv ℝ φ x).ker_closedComplemented_of_finiteDimensional_range
  set P := Classical.choose hker with hPdef
  set g := hstrict.implicitFunctionOfComplemented φ (fderiv ℝ φ x) hrange hker (φ x) with hgdef
  have hgd : HasStrictFDerivAt g (fderiv ℝ φ x).ker.subtypeL 0 :=
    hstrict.to_implicitFunctionOfComplemented hrange hker
  obtain ⟨K, t, ht, hlip⟩ := hgd.exists_lipschitzOnWith
  have hPcont : Continuous fun y : V => P (y - x) := P.continuous.comp (continuous_id.sub continuous_const)
  have hpre : (fun y : V => P (y - x)) ⁻¹' t ∈ 𝓝 x := by
    exact hPcont.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨A, hA, hAsub⟩ := Filter.eventually_iff_exists_mem.mp
    (hstrict.eq_implicitFunctionOfComplemented hrange hker)
  refine ⟨A ∩ ((fun y : V => P (y - x)) ⁻¹' t) ∩ Metric.ball x 1, K,
    (fun y : V => P (y - x)) '' ((A ∩ ((fun y : V => P (y - x)) ⁻¹' t) ∩ Metric.ball x 1)
      ∩ {y | φ y = φ x}), g, ?_, ?_, ?_, ?_⟩
  · exact Filter.inter_mem (Filter.inter_mem hA hpre) (Metric.ball_mem_nhds x one_pos)
  · refine (Metric.isBounded_closedBall (x := (0 : LinearMap.ker (fderiv ℝ φ x).toLinearMap))
      (r := ‖P‖)).subset ?_
    rintro _ ⟨y, ⟨⟨⟨-, -⟩, hy1⟩, -⟩, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine (P.le_opNorm _).trans ?_
    have : ‖y - x‖ ≤ 1 := by
      rw [← dist_eq_norm]
      exact (Metric.mem_ball.mp hy1).le
    nlinarith [norm_nonneg P, norm_nonneg (y - x)]
  · refine hlip.mono ?_
    rintro _ ⟨y, ⟨⟨⟨-, hy2⟩, -⟩, -⟩, rfl⟩
    exact hy2
  · rintro y ⟨hyN, hylev⟩
    refine ⟨(fun y : V => P (y - x)) y, ⟨y, ⟨hyN, hylev⟩, rfl⟩, ?_⟩
    have h1 := hAsub y hyN.1.1
    rw [hgdef, ← hylev]
    exact h1

end LipschitzGraph

section LevelSet

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- At a regular point of a `C¹` function the level set through that point has finite
`(n-1)`-dimensional Hausdorff measure in some neighbourhood.  General form of
`SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`. -/
theorem exists_hausdorffMeasure_levelSet_lt_top {φ : V → ℝ} (hφ : ContDiff ℝ 1 φ) {x : V}
    (hx : fderiv ℝ φ x ≠ 0) :
    ∃ N ∈ 𝓝 x, μH[(Module.finrank ℝ V : ℝ) - 1] (N ∩ {y | φ y = φ x}) < ⊤ := by
  classical
  obtain ⟨N, K, s, g, hN, hsb, hg, hsub⟩ := exists_lipschitzOnWith_levelSet_subset_image hφ hx
  refine ⟨N, hN, ?_⟩
  have hne : (fderiv ℝ φ x).toLinearMap ≠ 0 := fun h =>
    hx (ContinuousLinearMap.coe_injective (h.trans ContinuousLinearMap.toLinearMap_zero.symm))
  have hrank :
      Module.finrank ℝ (LinearMap.ker (fderiv ℝ φ x).toLinearMap) + 1 = Module.finrank ℝ V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hne
  have hd : ((Module.finrank ℝ V : ℝ) - 1)
      = (Module.finrank ℝ (LinearMap.ker (fderiv ℝ φ x).toLinearMap) : ℝ) := by
    rw [← hrank]; push_cast; ring
  rw [hd]
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  refine lt_of_le_of_lt (hg.hausdorffMeasure_image_le (Nat.cast_nonneg _)) ?_
  refine ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg _) ENNReal.coe_ne_top) ?_
  obtain ⟨r, hr⟩ := hsb.subset_closedBall 0
  exact lt_of_le_of_lt (measure_mono hr)
    ((isCompact_closedBall (0 : LinearMap.ker (fderiv ℝ φ x).toLinearMap) r).measure_lt_top)

end LevelSet

end Analysis

end FunctionalInequalities

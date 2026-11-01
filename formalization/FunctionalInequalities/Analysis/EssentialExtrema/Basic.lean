module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Bases

/-!
# Essential extrema of bounded functions

Identities between essential infima and suprema of a.e. bounded real functions, used for deficits `M
− f` (Gilbarg–Trudinger
2001, §17.4). Essential (a.e.) extrema only: no pointwise extremum or regular representative is
asserted.
-/

@[expose] public section

namespace FunctionalInequalities.Analysis

section EssentialDeficit
open MeasureTheory Filter
/-- **Essential infimum of a deficit.** For a nonzero measure and `0 ≤ f ≤ M` a.e.,
`essinf (M − f) = M − esssup f` (as `ℝ≥0∞` values); the nonzero measure excludes the value `⊤`. Used
for the
directional deficits of Gilbarg–Trudinger (2001), §17.4; no pointwise infimum or representative is
involved. -/
theorem essInf_ofReal_deficit_eq_sub_essSup {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [NeZero μ] (f : X → ℝ) (M : ℝ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hfM : ∀ᵐ x ∂μ, f x ≤ M) :
    essInf (fun x => ENNReal.ofReal (M - f x)) μ = ENNReal.ofReal (M - essSup f μ) := by
  have hfub : (ae μ).IsBoundedUnder (· ≤ ·) f := ⟨M, hfM⟩
  have hfco : (ae μ).IsCoboundedUnder (· ≤ ·) f := isCoboundedUnder_le_of_eventually_le _ hf0
  have hglo : (ae μ).IsBoundedUnder (· ≥ ·) (fun x => M - f x) := by
    refine ⟨0, ?_⟩
    change ∀ᵐ x ∂μ, 0 ≤ M - f x
    filter_upwards [hfM] with x hx
    exact sub_nonneg.mpr hx
  have hgco : (ae μ).IsCoboundedUnder (· ≥ ·) (fun x => M - f x) := by
    apply isCoboundedUnder_ge_of_eventually_le
    filter_upwards [hf0] with x hx
    exact sub_le_self M hx
  have hmap :=
    Monotone.map_liminf_of_continuousAt ENNReal.ofReal_mono (fun x => M - f x)
      ENNReal.continuous_ofReal.continuousAt hgco hglo
  change
    ENNReal.ofReal (Filter.liminf (fun x => M - f x) (ae μ)) =
      Filter.liminf (fun x => ENNReal.ofReal (M - f x)) (ae μ) at hmap
  change Filter.liminf (fun x => ENNReal.ofReal (M - f x)) (ae μ) = _
  rw [← hmap]
  rw [liminf_const_sub (ae μ) f M hfub hfco]
  rfl
end EssentialDeficit

end FunctionalInequalities.Analysis

/-! ## Real essential extrema and a common good set -/

section RealEssentialBounds

open MeasureTheory Filter Set TopologicalSpace

namespace FunctionalInequalities.Analysis

/--
Real essential extrema of an a.e. bounded function `L ≤ f ≤ U` under a nonzero measure: `L ≤ essInf
f ≤ essSup f ≤ U`,
and `essInf f ≤ f ≤ essSup f` almost everywhere. -/
theorem real_essential_bounds {X : Type*} [MeasurableSpace X] (μ : Measure X) [NeZero μ]
    (f : X → ℝ) {L U : ℝ} (hL : ∀ᵐ x ∂μ, L ≤ f x) (hU : ∀ᵐ x ∂μ, f x ≤ U) :
    L ≤ essInf f μ ∧
      essInf f μ ≤ essSup f μ ∧ essSup f μ ≤ U ∧ ∀ᵐ x ∂μ, essInf f μ ≤ f x ∧ f x ≤ essSup f μ := by
  have hlo : (ae μ).IsBoundedUnder (· ≥ ·) f := ⟨L, hL⟩
  have hhi : (ae μ).IsBoundedUnder (· ≤ ·) f := ⟨U, hU⟩
  have hclo : (ae μ).IsCoboundedUnder (· ≥ ·) f := isCoboundedUnder_ge_of_eventually_le _ hU
  have hchi : (ae μ).IsCoboundedUnder (· ≤ ·) f := isCoboundedUnder_le_of_eventually_le _ hL
  have hl : ∀ᵐ x ∂μ, essInf f μ ≤ f x := ae_essInf_le hlo
  have hu : ∀ᵐ x ∂μ, f x ≤ essSup f μ := ae_le_essSup hhi
  obtain ⟨x, hx⟩ := (hl.and hu).exists
  exact ⟨le_essInf_of_ae_le L hL hclo, hx.1.trans hx.2, essSup_le_of_ae_le U hU hchi, hl.and hu⟩

/-- For an a.e. bounded `f` under a nonzero measure, `essSup (M − f) = M − essInf f`. -/
theorem real_essSup_deficit {X : Type*} [MeasurableSpace X] (μ : Measure X) [NeZero μ]
    (f : X → ℝ) (M : ℝ) {L U : ℝ} (hL : ∀ᵐ x ∂μ, L ≤ f x) (hU : ∀ᵐ x ∂μ, f x ≤ U) :
    essSup (fun x => M - f x) μ = M - essInf f μ := by
  exact limsup_const_sub (ae μ) f M (isCoboundedUnder_ge_of_eventually_le _ hU) ⟨L, hL⟩

/--
For nonzero measures `ν ≤ μ` and `f` bounded `μ`-a.e., `essInf_μ f ≤ essInf_ν f` and `essSup_ν f ≤
essSup_μ f`. -/
theorem real_essential_bounds_mono_measure {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [NeZero μ] [NeZero ν] (hνμ : ν ≤ μ) (f : X → ℝ) {L U : ℝ} (hL : ∀ᵐ x ∂μ, L ≤ f x)
    (hU : ∀ᵐ x ∂μ, f x ≤ U) : essInf f μ ≤ essInf f ν ∧ essSup f ν ≤ essSup f μ := by
  have hLn : ∀ᵐ x ∂ν, L ≤ f x := (Measure.absolutelyContinuous_of_le hνμ).ae_le hL
  have hUn : ∀ᵐ x ∂ν, f x ≤ U := (Measure.absolutelyContinuous_of_le hνμ).ae_le hU
  exact
    ⟨essInf_antitone_measure (Measure.absolutelyContinuous_of_le hνμ) ⟨L, hL⟩
        (isCoboundedUnder_ge_of_eventually_le _ hUn),
      essSup_mono_measure' hνμ (isCoboundedUnder_le_of_eventually_le _ hLn) ⟨U, hU⟩⟩

/--
On a second-countable space with an open-positive measure, for an a.e. bounded real `f`, almost
every point `x`
satisfies `essInf_{μ|V} f ≤ f x ≤ essSup_{μ|V} f` for EVERY open `V ∋ x`. Only the countable basis
is intersected; arbitrary
open sets follow by monotonicity. -/
theorem ae_forall_open_real_essential_bounds {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X)
    [μ.IsOpenPosMeasure] (f : X → ℝ) {L U : ℝ} (hL : ∀ᵐ x ∂μ, L ≤ f x) (hU : ∀ᵐ x ∂μ, f x ≤ U) :
    ∀ᵐ x ∂μ,
      ∀ V : Set X,
        IsOpen V → x ∈ V → essInf f (μ.restrict V) ≤ f x ∧ f x ≤ essSup f (μ.restrict V) := by
  have hB (V : countableBasis X) :
    ∀ᵐ x ∂μ, x ∈ (V : Set X) → essInf f (μ.restrict V) ≤ f x ∧ f x ≤ essSup f (μ.restrict V) := by
    have hVo : IsOpen (V : Set X) := (isBasis_countableBasis X).isOpen V.property
    have hVn : (V : Set X).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr
        (by
          intro h
          exact empty_notMem_countableBasis X (h ▸ V.property))
    let : NeZero (μ.restrict (V : Set X)) :=
      ⟨by
        rw [Ne, Measure.restrict_eq_zero]
        exact hVo.measure_ne_zero μ hVn⟩
    exact
      ae_imp_of_ae_restrict
        (real_essential_bounds (μ.restrict V) f (ae_restrict_of_ae hL)
                (ae_restrict_of_ae hU)).2.2.2
  filter_upwards [ae_all_iff.mpr hB] with x hx
  intro V hVo hxV
  obtain ⟨B, hB, hxB, hBV⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hxV hVo
  have hBo := (isBasis_countableBasis X).isOpen hB
  let : NeZero (μ.restrict V) :=
    ⟨by
      rw [Ne, Measure.restrict_eq_zero]
      exact hVo.measure_ne_zero μ ⟨x, hxV⟩⟩
  let : NeZero (μ.restrict B) :=
    ⟨by
      rw [Ne, Measure.restrict_eq_zero]
      exact hBo.measure_ne_zero μ ⟨x, hxB⟩⟩
  have hm :=
    real_essential_bounds_mono_measure (μ.restrict V) (μ.restrict B)
      (Measure.restrict_mono hBV le_rfl) f (ae_restrict_of_ae hL) (ae_restrict_of_ae hU)
  have hb := hx ⟨B, hB⟩ hxB
  exact ⟨hm.1.trans hb.1, hb.2.trans hm.2⟩

end FunctionalInequalities.Analysis

end RealEssentialBounds

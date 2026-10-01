import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski
import FunctionalInequalities.KLS.Geometry.Cheeger.UpperMinkowskiContent

/-!
# Upper Minkowski recovery of the metric BV perimeter

For a finite Borel measure `ν` on a metric space (2026-09-30: generic metric and finite-measure
scope; probability laws are instances) and every target
set `B` of finite metric BV perimeter, `exists_upperMinkowskiRecovery` produces measurable (open)
sets `upperRecoverySet ν hB n` converging to `B` in indicator `L¹(ν)` whose *upper* Minkowski
contents tend to `perimeter ν B` in `ℝ≥0∞`.

Construction.  The lower recovery sets `minkowskiRecoverySet ν hB n` (measurable, indicator
errors and lower contents converging to the perimeter) have finite lower content term by term,
from their explicit quantitative bound `minkowskiContent_minkowskiRecoverySet_le`, never from the
convergence.  Stage A (`Isoperimetry.exists_upperRecovery`) gives, for each of them, thickenings
with indicator error and upper-content excess below any slack; one such thickening with slack
`1/(n+1)` is `upperRecoverySet ν hB n`.  The diagonal indicator error is bounded by the triangle
inequality, the upper bound `limsup ≤ perimeter` follows from the lower contents of the recovery
sets, and the lower bound `perimeter ≤ liminf` is the BV lower semicontinuity under indicator `L¹`
convergence (`perimeter_le_liminf_of_tendsto`) combined with `perimeter ≤ minkowskiContent ≤
upperMinkowskiContent` on measurable sets.  The lower bound holds for every measurable
`L¹`-convergent sequence and every target, so at infinite perimeter every such sequence has
`liminf` of upper contents equal to `⊤` (`liminf_upperMinkowskiContent_eq_top_of_perimeter_eq_top`):
the infinite boundary is exact: no such sequence can have a finite limiting upper content
(terms may still be finite while tending to `⊤`), and no recovery is claimed there.

The relaxed upper Minkowski content over the same measurable approximating class, and its
identification with the perimeter, are in `Perimeter/RelaxedMinkowski.lean`
(`relaxedUpperMinkowskiContent_eq_perimeter`). The additive finite-target section now proves
actual bounded open recovery at measurable finite-mass targets for Borel measures finite on
bounded Borel sets, without properness or finite total mass. The lower bound uses eventual
finite approximating-set mass; radius-local transfer first proves finite neighborhood mass
from finite target mass and finite lower content. No pointwise content/perimeter equality or
infinite-mass target endpoint is asserted.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace FunctionalInequalities.KLS.MetricBV

/-! ### Triangle bound for set indicators -/

section Triangle

variable {X : Type*} [MeasurableSpace X]

/-- Triangle bound for the indicator `L¹` distance of sets through a measurable intermediate
set (the target `B` is arbitrary). -/
theorem lintegral_enorm_indicator_sub_le_add (ν : Measure X) {U A : Set X} (hU : MeasurableSet U)
    (hA : MeasurableSet A) (B : Set X) :
    ∫⁻ x, ‖U.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν ≤
      ∫⁻ x, ‖U.indicator (1 : X → ℝ) x - A.indicator 1 x‖ₑ ∂ν +
        ∫⁻ x, ‖A.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν := by
  have hmeas : Measurable fun x => ‖U.indicator (1 : X → ℝ) x - A.indicator (1 : X → ℝ) x‖ₑ :=
    ((measurable_one.indicator hU).sub (measurable_one.indicator hA)).enorm
  calc ∫⁻ x, ‖U.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν
      ≤ ∫⁻ x, (‖U.indicator (1 : X → ℝ) x - A.indicator (1 : X → ℝ) x‖ₑ +
          ‖A.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ) ∂ν :=
        lintegral_mono fun x => by
          rw [← sub_add_sub_cancel (U.indicator (1 : X → ℝ) x) (A.indicator (1 : X → ℝ) x)]
          exact enorm_add_le _ _
    _ = _ := lintegral_add_left hmeas _

end Triangle

variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]

/-! ### Lower bound: BV lower semicontinuity below the upper content -/

/-- For every target `B` and every sequence of measurable sets converging to `B` in indicator
`L¹(ν)`, the perimeter is at most the `liminf` of the upper contents (BV lower semicontinuity,
then `perimeter ≤ minkowskiContent ≤ upperMinkowskiContent` on measurable sets). -/
theorem perimeter_le_liminf_upperMinkowskiContent (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)
    {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    perimeter (ν : Measure V) B ≤
      liminf (fun n => Isoperimetry.upperMinkowskiContent ν (A n)) atTop :=
  (perimeter_le_liminf_of_tendsto (ν : Measure V) hA hconv).trans
    (liminf_le_liminf (Eventually.of_forall fun n =>
      (perimeter_le_minkowskiContent ν (hA n)).trans
        (Isoperimetry.minkowskiContent_le_upperMinkowskiContent ν (A n))))

/-- The exact infinite boundary: at infinite perimeter, every measurable `L¹`-convergent sequence
has `liminf` of upper contents equal to `⊤`, so no such sequence can have a finite limiting
upper content (its terms may still be finite while tending to `⊤`). -/
theorem liminf_upperMinkowskiContent_eq_top_of_perimeter_eq_top (ν : Measure V) [IsFiniteMeasure ν]
    {B : Set V} (hB : perimeter (ν : Measure V) B = ⊤) {A : ℕ → Set V}
    (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    liminf (fun n => Isoperimetry.upperMinkowskiContent ν (A n)) atTop = ⊤ :=
  top_le_iff.mp (hB ▸ perimeter_le_liminf_upperMinkowskiContent ν B hA hconv)

/-! ### One Stage-A thickening with prescribed slack -/

/-- From Stage A: a measurable set of finite lower content has a positive thickening with
indicator error at most `δ` and upper content at most its lower content plus `δ`. -/
theorem exists_thickening_approx (ν : Measure V) [IsFiniteMeasure ν] {A : Set V} (hA : MeasurableSet A)
    (hfin : Isoperimetry.minkowskiContent ν A ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℝ, 0 < s ∧
      ∫⁻ x, ‖(thickening s A).indicator (1 : V → ℝ) x - A.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        ENNReal.ofReal δ ∧
      Isoperimetry.upperMinkowskiContent ν (thickening s A) ≤
        Isoperimetry.minkowskiContent ν A + ENNReal.ofReal δ := by
  obtain ⟨s, hs, -, -, hL1, hl⟩ := Isoperimetry.exists_upperRecovery ν A hA hfin
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  have h1 : ∀ᶠ n in atTop, ∫⁻ x, ‖(thickening (s n) A).indicator (1 : V → ℝ) x -
      A.indicator 1 x‖ₑ ∂(ν : Measure V) ≤ ENNReal.ofReal δ :=
    ENNReal.tendsto_nhds_zero.1 hL1 _ hδ'
  have h2 : ∀ᶠ n in atTop, Isoperimetry.upperMinkowskiContent ν (thickening (s n) A) <
      Isoperimetry.minkowskiContent ν A + ENNReal.ofReal δ :=
    eventually_lt_of_limsup_lt (hl.trans_lt (ENNReal.lt_add_right hfin hδ'.ne'))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  exact ⟨s n, hs n, hn1, hn2.le⟩

/-! ### Upper recovery sets -/

section UpperRecovery

variable (ν : Measure V) [IsFiniteMeasure ν] {B : Set V} (hB : perimeter (ν : Measure V) B < ⊤)

/-- Each lower recovery set has finite lower content, by its explicit quantitative bound (not by
the convergence of the contents). -/
theorem minkowskiContent_minkowskiRecoverySet_ne_top (n : ℕ) :
    Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n) ≠ ⊤ := by
  refine ((minkowskiContent_minkowskiRecoverySet_le ν hB n).trans_lt ?_).ne
  have hw : 0 < 1 - 2 * recoveryWidth n := by linarith [recoveryWidth_lt_half n]
  exact ENNReal.add_lt_top.2
    ⟨ENNReal.div_lt_top (ENNReal.add_lt_top.2 ⟨hB, ENNReal.ofReal_lt_top⟩).ne
      (ENNReal.ofReal_pos.2 hw).ne', ENNReal.ofReal_lt_top⟩

/-- The `n`-th step: a positive thickening radius of the `n`-th lower recovery set with indicator
error and upper-content excess at most `1/(n+1)`. -/
theorem exists_upperRecoveryStep (n : ℕ) :
    ∃ s : ℝ, 0 < s ∧
      ∫⁻ x, ‖(thickening s (minkowskiRecoverySet ν hB n)).indicator (1 : V → ℝ) x -
        (minkowskiRecoverySet ν hB n).indicator 1 x‖ₑ ∂(ν : Measure V) ≤
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
      Isoperimetry.upperMinkowskiContent ν (thickening s (minkowskiRecoverySet ν hB n)) ≤
        Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n) +
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
  exists_thickening_approx ν (measurableSet_minkowskiRecoverySet ν hB n)
    (minkowskiContent_minkowskiRecoverySet_ne_top ν hB n) (by positivity)

/-- The selected thickening radius of the `n`-th lower recovery set. -/
def upperRecoveryRadius (n : ℕ) : ℝ :=
  Classical.choose (exists_upperRecoveryStep ν hB n)

/-- The `n`-th upper recovery set: the selected open thickening of the `n`-th lower recovery
set. -/
def upperRecoverySet (n : ℕ) : Set V :=
  thickening (upperRecoveryRadius ν hB n) (minkowskiRecoverySet ν hB n)

theorem upperRecoveryRadius_pos (n : ℕ) : 0 < upperRecoveryRadius ν hB n :=
  (Classical.choose_spec (exists_upperRecoveryStep ν hB n)).1

theorem isOpen_upperRecoverySet (n : ℕ) : IsOpen (upperRecoverySet ν hB n) :=
  isOpen_thickening

theorem measurableSet_upperRecoverySet (n : ℕ) : MeasurableSet (upperRecoverySet ν hB n) :=
  (isOpen_upperRecoverySet ν hB n).measurableSet

/-- Indicator error of the `n`-th upper recovery set against the `n`-th lower recovery set. -/
theorem lintegral_enorm_upperRecoverySet_sub_minkowskiRecoverySet_le (n : ℕ) :
    ∫⁻ x, ‖(upperRecoverySet ν hB n).indicator (1 : V → ℝ) x -
      (minkowskiRecoverySet ν hB n).indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
  (Classical.choose_spec (exists_upperRecoveryStep ν hB n)).2.1

/-- Upper content of the `n`-th upper recovery set: at most the lower content of the `n`-th lower
recovery set plus `1/(n+1)`. -/
theorem upperMinkowskiContent_upperRecoverySet_le (n : ℕ) :
    Isoperimetry.upperMinkowskiContent ν (upperRecoverySet ν hB n) ≤
      Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n) +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
  (Classical.choose_spec (exists_upperRecoveryStep ν hB n)).2.2

/-- Diagonal indicator error against the target: at most `1/(n+1)` plus the error of the `n`-th
lower recovery set. -/
theorem lintegral_enorm_upperRecoverySet_sub_le (n : ℕ) :
    ∫⁻ x, ‖(upperRecoverySet ν hB n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) +
        ∫⁻ x, ‖(minkowskiRecoverySet ν hB n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
          ∂(ν : Measure V) :=
  (lintegral_enorm_indicator_sub_le_add (ν : Measure V) (measurableSet_upperRecoverySet ν hB n)
    (measurableSet_minkowskiRecoverySet ν hB n) B).trans
    (add_le_add_left (lintegral_enorm_upperRecoverySet_sub_minkowskiRecoverySet_le ν hB n) _)

/-- The upper recovery sets converge to `B` in indicator `L¹(ν)`. -/
theorem tendsto_indicator_upperRecoverySet :
    Tendsto (fun n => ∫⁻ x, ‖(upperRecoverySet ν hB n).indicator (1 : V → ℝ) x -
      B.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) := by
  have hslack : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)) +
      ∫⁻ x, ‖(minkowskiRecoverySet ν hB n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) := by
    simpa using hslack.add (tendsto_indicator_minkowskiRecoverySet ν hB)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    (lintegral_enorm_upperRecoverySet_sub_le ν hB)

/-- **Upper Minkowski recovery.**  The upper contents of the upper recovery sets converge to the
perimeter of `B`. -/
theorem tendsto_upperMinkowskiContent_upperRecoverySet :
    Tendsto (fun n => Isoperimetry.upperMinkowskiContent ν (upperRecoverySet ν hB n)) atTop
      (𝓝 (perimeter (ν : Measure V) B)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · exact perimeter_le_liminf_upperMinkowskiContent ν B (measurableSet_upperRecoverySet ν hB)
      (tendsto_indicator_upperRecoverySet ν hB)
  · have hslack : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n : ℕ =>
        Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n) +
          ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 (perimeter (ν : Measure V) B)) := by
      simpa using (tendsto_minkowskiContent_minkowskiRecoverySet ν hB).add hslack
    rw [← hlim.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall (upperMinkowskiContent_upperRecoverySet_le ν hB))

include hB in
/-- **Existence form.**  For every target `B` of finite perimeter there are measurable sets
converging to `B` in indicator `L¹(ν)` whose upper Minkowski contents tend to the perimeter. -/
theorem exists_upperMinkowskiRecovery :
    ∃ U : ℕ → Set V, (∀ n, MeasurableSet (U n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => Isoperimetry.upperMinkowskiContent ν (U n)) atTop
        (𝓝 (perimeter (ν : Measure V) B)) :=
  ⟨upperRecoverySet ν hB, measurableSet_upperRecoverySet ν hB,
    tendsto_indicator_upperRecoverySet ν hB, tendsto_upperMinkowskiContent_upperRecoverySet ν hB⟩

end UpperRecovery

/-! ### Finite-mass targets for measures finite on bounded Borel sets -/

/-- For a measurable finite-mass target, global indicator L1 convergence bounds perimeter
by the liminf of genuine upper contents under any Borel measure. -/
theorem perimeter_le_liminf_upperMinkowskiContent_of_measure_lt_top (ν : Measure V) {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤)
    {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) : perimeter ν B ≤ liminf (fun n => Isoperimetry.upperMinkowskiContent ν (A n)) atTop :=
  (perimeter_le_liminf_minkowskiContent_of_measure_lt_top ν hB hνB hA hconv).trans
    (liminf_le_liminf (Eventually.of_forall fun n =>
      (show Isoperimetry.minkowskiContent ν (A n) ≤ Isoperimetry.upperMinkowskiContent ν (A n) from liminf_le_limsup)))

/-- A finite-mass set of finite lower content admits a finite-mass positive thickening
with prescribed indicator L1 and upper-content slack. -/
theorem exists_thickening_approx_of_measure_lt_top (ν : Measure V) {A : Set V} (hA : MeasurableSet A) (hνA : ν A < ⊤)
    (hfin : Isoperimetry.minkowskiContent ν A < ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℝ, 0 < s ∧ ν (Metric.thickening s A) < ⊤ ∧
      ∫⁻ x, ‖(Metric.thickening s A).indicator (1 : V → ℝ) x - A.indicator 1 x‖ₑ ∂ν ≤
        ENNReal.ofReal δ ∧ Isoperimetry.upperMinkowskiContent ν (Metric.thickening s A) ≤
          Isoperimetry.minkowskiContent ν A + ENNReal.ofReal δ := by
  obtain ⟨s, hs, -, -, hmass, hL1, hl⟩ := Isoperimetry.exists_upperRecovery_of_measure_lt_top ν hA hνA hfin
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  have h1 : ∀ᶠ n in atTop, ∫⁻ x, ‖(Metric.thickening (s n) A).indicator (1 : V → ℝ) x -
      A.indicator 1 x‖ₑ ∂ν ≤ ENNReal.ofReal δ := ENNReal.tendsto_nhds_zero.1 hL1 _ hδ'
  have h2 : ∀ᶠ n in atTop, Isoperimetry.upperMinkowskiContent ν (Metric.thickening (s n) A) <
      Isoperimetry.minkowskiContent ν A + ENNReal.ofReal δ :=
    eventually_lt_of_limsup_lt (hl.trans_lt (ENNReal.lt_add_right hfin.ne hδ'.ne'))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  exact ⟨s n, hs n, hmass n, hn1, hn2.le⟩

/-- Actual upper-content recovery for measurable finite-mass targets under finiteness on
bounded Borel sets. The selected sets are open and bounded, have finite mass and finite
upper content term by term, and converge in global indicator L1 with upper contents
converging to the finite target perimeter. No properness or finite total mass is needed. -/
theorem exists_upperMinkowskiRecovery_of_finite_on_bounded (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) (hP : perimeter ν B < ⊤) :
    ∃ U : ℕ → Set V, (∀ n, IsOpen (U n)) ∧ (∀ n, MeasurableSet (U n)) ∧ (∀ n, Bornology.IsBounded (U n)) ∧
      (∀ n, ν (U n) < ⊤) ∧ (∀ n, Isoperimetry.upperMinkowskiContent ν (U n) < ⊤) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
        atTop (𝓝 0) ∧ Tendsto (fun n => Isoperimetry.upperMinkowskiContent ν (U n)) atTop (𝓝 (perimeter ν B)) := by
  obtain ⟨A, hA, hbndA, hmassA, hfinA, hconvA, hcostA⟩ :=
    exists_minkowskiRecovery_of_finite_on_bounded ν hν hB hνB hP
  have hs : ∀ n : ℕ, ∃ s : ℝ, 0 < s ∧ ν (Metric.thickening s (A n)) < ⊤ ∧
      ∫⁻ x, ‖(Metric.thickening s (A n)).indicator (1 : V → ℝ) x - (A n).indicator 1 x‖ₑ ∂ν ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
      Isoperimetry.upperMinkowskiContent ν (Metric.thickening s (A n)) ≤
        Isoperimetry.minkowskiContent ν (A n) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    exists_thickening_approx_of_measure_lt_top ν (hA n) (hmassA n) (hfinA n) (by positivity)
  choose s hspos hmass he hc using hs
  let U : ℕ → Set V := fun n => Metric.thickening (s n) (A n)
  have hU : ∀ n, MeasurableSet (U n) := fun _ => Metric.isOpen_thickening.measurableSet
  have hη : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have herr : ∀ n, ∫⁻ x, ‖(U n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) +
        ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν := fun n =>
    (lintegral_enorm_indicator_sub_le_add ν (hU n) (hA n) B).trans (add_le_add (he n) le_rfl)
  have hconv : Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hη.add hconvA) (fun _ => zero_le) herr
  have hcontentFin : ∀ n, Isoperimetry.upperMinkowskiContent ν (U n) < ⊤ := fun n =>
    (hc n).trans_lt (ENNReal.add_lt_top.2 ⟨hfinA n, ENNReal.ofReal_lt_top⟩)
  refine ⟨U, fun _ => Metric.isOpen_thickening, hU, fun n => (hbndA n).thickening, hmass, hcontentFin, hconv, ?_⟩
  refine tendsto_of_le_liminf_of_limsup_le (perimeter_le_liminf_upperMinkowskiContent_of_measure_lt_top ν hB hνB hU hconv) ?_
  have hup : Tendsto (fun n => Isoperimetry.minkowskiContent ν (A n) + ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (perimeter ν B)) := by simpa using hcostA.add hη
  exact (limsup_le_limsup (Eventually.of_forall hc)).trans_eq hup.limsup_eq

end FunctionalInequalities.KLS.MetricBV

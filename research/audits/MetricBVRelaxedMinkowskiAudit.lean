import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent full-signature clients for the relaxed lower Minkowski content as a set infimum:
the class carries only measurability and indicator `L¹` convergence; the infimum of liminf outer
Minkowski contents equals the metric BV perimeter for every set (in particular every measurable
set) and every probability law on a normed additive group with Borel structure. Both directions
are used with actual sequences: the constant sequence bounds the relaxed content by the content,
and the phase-10 recovery sets bound it by the perimeter. Edge cases: zero perimeter
(`Iic (1/2)` under the two-atom law), the zero-dimensional space, infinite perimeter and an empty
class (conditional), and the strict pointwise gap: the rationals under the standard Gaussian law
have relaxed content `0` and outer Minkowski content `⊤`, so no pointwise equality is asserted.
Neither Lemma 2.1 nor Theorem 3.6 of Ambrosio--Di Marino--Gigli in general metric measure
spaces is claimed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVRelaxedMinkowskiAudit

open FunctionalInequalities
open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem identity (ν : ProbabilityMeasure V) (B : Set V) :
    relaxedMinkowskiContent (ν : Measure V) B = perimeter (ν : Measure V) B := by
  exact relaxedMinkowskiContent_eq_perimeter (ν : Measure V) B

/-- The requested form, with `B` measurable. -/
theorem identityMeasurable (ν : ProbabilityMeasure V) {B : Set V} (_hB : MeasurableSet B) :
    relaxedMinkowskiContent (ν : Measure V) B = perimeter (ν : Measure V) B := by
  exact relaxedMinkowskiContent_eq_perimeter (ν : Measure V) B

theorem bothInequalities (ν : ProbabilityMeasure V) (B : Set V) :
    perimeter (ν : Measure V) B ≤ relaxedMinkowskiContent (ν : Measure V) B ∧
      relaxedMinkowskiContent (ν : Measure V) B ≤ perimeter (ν : Measure V) B :=
  ⟨perimeter_le_relaxedMinkowskiContent (ν : Measure V) B, relaxedMinkowskiContent_le_perimeter (ν : Measure V) B⟩

/-- Direction one with an actual sequence: the constant sequence of a measurable set. -/
theorem constantSequence (ν : ProbabilityMeasure V) {B : Set V} (hB : MeasurableSet B) :
    ((MinkowskiApproximatingSequence.const (ν : Measure V) hB).1 = fun _ => B) ∧
      relaxedMinkowskiContent (ν : Measure V) B ≤ Isoperimetry.minkowskiContent (ν : Measure V) B ∧
      perimeter (ν : Measure V) B ≤ Isoperimetry.minkowskiContent (ν : Measure V) B :=
  ⟨rfl, relaxedMinkowskiContent_le_minkowskiContent (ν : Measure V) hB,
    (perimeter_le_relaxedMinkowskiContent (ν : Measure V) B).trans
      (relaxedMinkowskiContent_le_minkowskiContent (ν : Measure V) hB)⟩

/-- Direction two with an actual sequence: the Minkowski recovery sets of a set of finite
perimeter form a member of the class, and bound the relaxed content by the perimeter. -/
theorem recoverySequence (ν : ProbabilityMeasure V) {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) :
    relaxedMinkowskiContent (ν : Measure V) B ≤
      liminf (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n)) atTop ∧
      liminf (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n)) atTop =
        perimeter (ν : Measure V) B :=
  ⟨relaxedMinkowskiContent_le_liminf (ν : Measure V) B
      ⟨minkowskiRecoverySet (ν : Measure V) hB, measurableSet_minkowskiRecoverySet (ν : Measure V) hB,
        tendsto_indicator_minkowskiRecoverySet (ν : Measure V) hB⟩,
    (tendsto_minkowskiContent_minkowskiRecoverySet (ν : Measure V) hB).liminf_eq⟩

/-- Sequential lower semicontinuity of the relaxed content. -/
theorem lowerSemicontinuity (ν : ProbabilityMeasure V) {B : Set V} {A : ℕ → Set V}
    (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    relaxedMinkowskiContent (ν : Measure V) B ≤ liminf (fun n => relaxedMinkowskiContent (ν : Measure V) (A n)) atTop := by
  exact relaxedMinkowskiContent_le_liminf_of_tendsto (ν : Measure V) hA hconv

/-- Infinite perimeter transfers; an empty class forces infinite perimeter. -/
theorem topCases (ν : ProbabilityMeasure V) (B : Set V) :
    (perimeter (ν : Measure V) B = ⊤ → relaxedMinkowskiContent (ν : Measure V) B = ⊤) ∧
      (IsEmpty (MinkowskiApproximatingSequence (ν : Measure V) B) → perimeter (ν : Measure V) B = ⊤) := by
  refine ⟨fun h => (relaxedMinkowskiContent_eq_perimeter (ν : Measure V) B).trans h, fun h => ?_⟩
  have := h
  exact (relaxedMinkowskiContent_eq_perimeter (ν : Measure V) B).symm.trans
    (relaxedMinkowskiContent_eq_top_of_isEmpty (ν : Measure V) B)

/-- The zero-dimensional space: every relaxed content is `0`. -/
theorem zeroDimensional (ν : ProbabilityMeasure (Fin 0 → ℝ)) (B : Set (Fin 0 → ℝ)) :
    relaxedMinkowskiContent (ν : Measure (Fin 0 → ℝ)) B = 0 :=
  (relaxedMinkowskiContent_eq_perimeter (ν : Measure (Fin 0 → ℝ)) B).trans (perimeter_eq_zero_of_subsingleton _ _)

/-- The two-atom law `(δ₀ + δ₁)/2` on `ℝ`. -/
def twoAtom : ProbabilityMeasure ℝ :=
  ⟨(2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1), ⟨by
    simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩⟩

theorem twoAtom_apply {S : Set ℝ} (hS : MeasurableSet S) (h0 : (0 : ℝ) ∈ S) (h1 : (1 : ℝ) ∉ S) :
    (twoAtom : Measure ℝ) S = 2⁻¹ := by
  change (((2 : ℝ≥0∞)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac 1) : Measure ℝ) S) =
    (2 : ℝ≥0∞)⁻¹
  simp [Measure.dirac_apply' _ hS, h0, h1]

/-- Zero perimeter: `Iic (1/2)` under the two-atom law has zero outer content, hence zero relaxed
content and zero perimeter, through the constant sequence. -/
theorem zeroPerimeter :
    relaxedMinkowskiContent (twoAtom : Measure ℝ) (Set.Iic (1 / 2 : ℝ)) = 0 ∧
      perimeter (twoAtom : Measure ℝ) (Set.Iic (1 / 2 : ℝ)) = 0 := by
  set B : Set ℝ := Set.Iic (1 / 2) with hBdef
  have hBm : MeasurableSet B := measurableSet_Iic
  have hmass : (twoAtom : Measure ℝ) B = 2⁻¹ :=
    twoAtom_apply hBm (by norm_num [hBdef]) (by norm_num [hBdef])
  have hc : Isoperimetry.minkowskiContent (twoAtom : Measure ℝ) B = 0 := by
    refine le_antisymm ?_ bot_le
    refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with r hr
    have hsub : Metric.thickening r B ⊆ Set.Iio (1 / 2 + r) := fun x hx => by
      obtain ⟨z, hz, hdz⟩ := Metric.mem_thickening_iff.mp hx
      have hz' : z ≤ 1 / 2 := hz
      have := (abs_lt.mp (by simpa [Real.dist_eq] using hdz)).2
      show x < 1 / 2 + r
      linarith
    have hthick : (twoAtom : Measure ℝ) (Metric.thickening r B) ≤ 2⁻¹ :=
      (measure_mono hsub).trans (twoAtom_apply measurableSet_Iio
        (by simp only [Set.mem_Iio]; linarith [hr.1])
        (by simp only [Set.mem_Iio, not_lt]; linarith [hr.2])).le
    rw [hmass, tsub_eq_zero_of_le hthick, ENNReal.zero_div]
  have hr : relaxedMinkowskiContent (twoAtom : Measure ℝ) B = 0 :=
    le_antisymm ((relaxedMinkowskiContent_le_minkowskiContent (twoAtom : Measure ℝ) hBm).trans_eq hc) bot_le
  exact ⟨hr, (relaxedMinkowskiContent_eq_perimeter (twoAtom : Measure ℝ) B).symm.trans hr⟩

/-- The pointwise inequality is strict in general: the rationals under the standard Gaussian law
are null, so their relaxed content and perimeter vanish, while their closure is the whole line,
so their outer Minkowski content is infinite. -/
theorem strictGap :
    ∃ (ν : ProbabilityMeasure ℝ) (B : Set ℝ), MeasurableSet B ∧
      relaxedMinkowskiContent (ν : Measure ℝ) B = 0 ∧ Isoperimetry.minkowskiContent (ν : Measure ℝ) B = ⊤ := by
  let ν : ProbabilityMeasure ℝ := ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
  set B : Set ℝ := Set.range ((↑) : ℚ → ℝ) with hBdef
  have hBc : B.Countable := Set.countable_range _
  have hBm : MeasurableSet B := hBc.measurableSet
  have h0 : (ν : Measure ℝ) B = 0 :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero (hBc.measure_zero _)
  refine ⟨ν, B, hBm, ?_, ?_⟩
  · rw [relaxedMinkowskiContent_eq_perimeter]
    have hdist : ∫⁻ x, ‖(∅ : Set ℝ).indicator (1 : ℝ → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure ℝ) = 0 := by
      have hfun : (fun x => ‖(∅ : Set ℝ).indicator (1 : ℝ → ℝ) x - B.indicator 1 x‖ₑ) =
          B.indicator 1 := by
        funext x
        by_cases hx : x ∈ B <;> simp [hx]
      rw [hfun, lintegral_indicator_one hBm, h0]
    have h := perimeter_le_liminf_of_tendsto (ν : Measure ℝ) (Bn := fun _ => (∅ : Set ℝ))
      (B := B) (fun _ => MeasurableSet.empty) (by simp only [hdist]; exact tendsto_const_nhds)
    simp only [perimeter_empty, liminf_const] at h
    exact le_antisymm h bot_le
  · by_contra hne
    have hcl := Isoperimetry.measure_closure_eq_of_minkowskiContent_ne_top (ν : Measure ℝ) hne
    rw [hBdef, Rat.denseRange_cast.closure_range, ← hBdef, h0, measure_univ] at hcl
    exact one_ne_zero hcl

#print axioms identity
#print axioms identityMeasurable
#print axioms bothInequalities
#print axioms constantSequence
#print axioms recoverySequence
#print axioms lowerSemicontinuity
#print axioms topCases
#print axioms zeroDimensional
#print axioms zeroPerimeter
#print axioms strictGap

end MetricBVRelaxedMinkowskiAudit

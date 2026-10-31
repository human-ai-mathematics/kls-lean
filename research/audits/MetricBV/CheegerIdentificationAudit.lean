module

public import FunctionalInequalities.KLS.Geometry.Cheeger.BVIdentification

/-! Independent full-signature clients for the identification of the metric BV Cheeger constants
with the Minkowski Cheeger constant on probability laws on normed groups, and of the BV constants
of the intrinsic coordinate law with `Isoperimetry.constant`. Checks: both inequalities
separately, the empty admissible family (dimension zero, both constants `⊤`), a realized
intermediate-mass case (the two-atom law `(δ₀ + δ₁)/2` on `ℝ` with `B = Iic (1/2)`, both
constants `0`), and the half-mass form. The closed-support constant `intrinsicHalfConstant`, the
literature test-class equivalence and general metric-measure comparisons are not claimed. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVCheegerIdentificationAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem lowerInequality (ν : ProbabilityMeasure V) :
    symmetricConstant ν ≤ Isoperimetry.minkowskiConstant ν := by
  exact symmetricConstant_le_minkowskiConstant ν

theorem upperInequality (ν : ProbabilityMeasure V) :
    Isoperimetry.minkowskiConstant ν ≤ symmetricConstant ν := by
  exact minkowskiConstant_le_symmetricConstant ν

theorem identification (ν : ProbabilityMeasure V) :
    symmetricConstant ν = Isoperimetry.minkowskiConstant ν := by
  exact symmetricConstant_eq_minkowskiConstant ν

theorem halfIdentification (ν : ProbabilityMeasure V) :
    halfConstant ν = Isoperimetry.minkowskiConstant ν := by
  exact halfConstant_eq_minkowskiConstant ν

/-- All three constants coincide. -/
theorem threeConstants (ν : ProbabilityMeasure V) :
    halfConstant ν = symmetricConstant ν ∧
      symmetricConstant ν = Isoperimetry.minkowskiConstant ν :=
  ⟨halfConstant_eq_symmetricConstant ν, symmetricConstant_eq_minkowskiConstant ν⟩

section FiniteDimensional

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

theorem frontendSymmetric (μ : ProbabilityMeasure E) :
    symmetricConstant (FunctionalInequalities.Probability.intrinsicMeasure μ) =
      Isoperimetry.constant μ := by
  exact symmetricConstant_intrinsicMeasure_eq_constant μ

theorem frontendHalf (μ : ProbabilityMeasure E) :
    halfConstant (FunctionalInequalities.Probability.intrinsicMeasure μ) =
      Isoperimetry.constant μ := by
  exact halfConstant_intrinsicMeasure_eq_constant μ

end FiniteDimensional

/-- Empty admissible family: in dimension zero both constants are `⊤`, consistently. -/
theorem emptyFamilyTop (ν : ProbabilityMeasure (Fin 0 → ℝ)) :
    symmetricConstant ν = ⊤ ∧ Isoperimetry.minkowskiConstant ν = ⊤ ∧ halfConstant ν = ⊤ := by
  have h := symmetricConstant_eq_top_of_subsingleton ν
  exact ⟨h, (symmetricConstant_eq_minkowskiConstant ν).symm.trans h,
    (halfConstant_eq_symmetricConstant ν).trans h⟩

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

/-- A realized intermediate-mass case: `B = Iic (1/2)` is admissible with mass `1/2` and zero
Minkowski content, so all three constants of the two-atom law vanish. -/
theorem twoAtomConstants :
    Isoperimetry.minkowskiConstant twoAtom = 0 ∧ symmetricConstant twoAtom = 0 ∧
      halfConstant twoAtom = 0 := by
  set B : Set ℝ := Set.Iic (1 / 2) with hBdef
  have hBm : MeasurableSet B := measurableSet_Iic
  have hmass : (twoAtom : Measure ℝ) B = 2⁻¹ :=
    twoAtom_apply hBm (by norm_num [hBdef]) (by norm_num [hBdef])
  have hc : Isoperimetry.minkowskiContent twoAtom B = 0 := by
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
  have hM : Isoperimetry.minkowskiConstant twoAtom = 0 := by
    refine le_antisymm ((minkowskiConstant_le_div twoAtom hBm
      (by rw [hmass]; exact ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
      (by rw [hmass]; exact ENNReal.inv_lt_one.2 ENNReal.one_lt_two)).trans_eq ?_) bot_le
    rw [hc, ENNReal.zero_div]
  have hS : symmetricConstant twoAtom = 0 := (symmetricConstant_eq_minkowskiConstant _).trans hM
  exact ⟨hM, hS, (halfConstant_eq_symmetricConstant _).trans hS⟩

#print axioms lowerInequality
#print axioms upperInequality
#print axioms identification
#print axioms halfIdentification
#print axioms threeConstants
#print axioms frontendSymmetric
#print axioms frontendHalf
#print axioms emptyFamilyTop
#print axioms twoAtomConstants

end MetricBVCheegerIdentificationAudit

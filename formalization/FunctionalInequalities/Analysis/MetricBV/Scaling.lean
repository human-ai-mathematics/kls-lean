module

public import FunctionalInequalities.Analysis.MetricBV.Basic

/-!
# Metric BV measure scaling and probability normalization
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-! ### Scaling by a nonnegative real scalar, the zero measure and normalization

Costs and indicator distances are linear in the measure; the approximating class of `c • ν` is
the class of `ν` for `c ≠ 0`; hence `perimeter (c • ν) B = c * perimeter ν B` for every nonzero
`c : ℝ≥0`, including the empty class (`⊤`).  The zero measure has zero perimeter for every set.
A finite nonzero measure is `c • ν` with `c : ℝ≥0` nonzero and `ν` a probability measure
(`exists_probability_smul`); scalars are always finite reals, so `⊤ - ⊤` never enters.
-/

section Scaling

theorem cost_smul (c : ℝ≥0) (ν : Measure X) (f : Test X) : cost (c • ν) f = c * cost ν f := by
  simp only [cost, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

theorem indicatorDistance_smul (c : ℝ≥0) (ν : Measure X) (f : Test X) (B : Set X) :
    indicatorDistance (c • ν) f B = c * indicatorDistance ν f B := by
  simp only [indicatorDistance, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

@[simp] theorem cost_zero_measure (f : Test X) : cost (0 : Measure X) f = 0 := by
  simp [cost]

@[simp] theorem indicatorDistance_zero_measure (f : Test X) (B : Set X) :
    indicatorDistance (0 : Measure X) f B = 0 := by
  simp [indicatorDistance]

/-- An approximating sequence for `ν` approximates for `c • ν` (any `c : ℝ≥0`). -/
def ApproximatingSequence.smul (c : ℝ≥0) {ν : Measure X} {B : Set X}
    (f : ApproximatingSequence ν B) : ApproximatingSequence (c • ν) B :=
  ⟨f.1, by
    have h := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) f.2 (Or.inr ENNReal.coe_ne_top)
    simpa [indicatorDistance_smul] using h⟩

/-- An approximating sequence for `c • ν` with `c ≠ 0` approximates for `ν`. -/
def ApproximatingSequence.smulInv {c : ℝ≥0} (hc : c ≠ 0) {ν : Measure X} {B : Set X}
    (f : ApproximatingSequence (c • ν) B) : ApproximatingSequence ν B :=
  ⟨f.1, by
    have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
    have h := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)⁻¹) f.2
      (Or.inr (ENNReal.inv_ne_top.2 hc'))
    simp only [indicatorDistance_smul, ← mul_assoc, ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top,
      one_mul, mul_zero] at h
    exact h⟩

theorem perimeter_smul_le (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure X) (B : Set X) :
    perimeter (c • ν) B ≤ c * perimeter ν B := by
  unfold perimeter
  rw [ENNReal.mul_iInf' (fun h => absurd h ENNReal.coe_ne_top)
    (fun h => absurd (ENNReal.coe_eq_zero.1 h) hc)]
  refine le_iInf fun f => (iInf_le _ (f.smul c)).trans (le_of_eq ?_)
  simp only [ApproximatingSequence.smul, cost_smul]
  exact ENNReal.liminf_const_mul_of_ne_top (a := (c : ℝ≥0∞)) ENNReal.coe_ne_top

/-- **Perimeter scaling**: `perimeter (c • ν) B = c * perimeter ν B` for every nonzero `c : ℝ≥0`
and every set `B` (also when the class is empty and both sides are `⊤`). -/
theorem perimeter_smul (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure X) (B : Set X) :
    perimeter (c • ν) B = c * perimeter ν B := by
  refine le_antisymm (perimeter_smul_le c hc ν B) ?_
  have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  have h := perimeter_smul_le c⁻¹ (inv_ne_zero hc) (c • ν) B
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  calc (c : ℝ≥0∞) * perimeter ν B ≤ c * ((c⁻¹ : ℝ≥0) * perimeter (c • ν) B) :=
        mul_le_mul' le_rfl h
    _ = perimeter (c • ν) B := by
        rw [← mul_assoc, ENNReal.coe_inv hc, ENNReal.mul_inv_cancel hc' ENNReal.coe_ne_top, one_mul]

/-- The zero measure has zero perimeter for every set: the zero test approximates at zero cost. -/
theorem perimeter_zero_measure (B : Set X) : perimeter (0 : Measure X) B = 0 := by
  refine le_antisymm ?_ bot_le
  have h := perimeter_le_sequence (0 : Measure X) B ⟨fun _ => Test.zero, by simp⟩
  simpa using h

omit [MetricSpace X] [BorelSpace X] in
/-- **Normalization**: a finite nonzero measure is a nonzero nonnegative real multiple of a
probability measure. -/
theorem exists_probability_smul (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    ∃ (c : ℝ≥0) (ν : ProbabilityMeasure X), c ≠ 0 ∧ μ = c • (ν : Measure X) := by
  have : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hμ (Measure.eq_zero_of_isEmpty μ)
  set μ' : FiniteMeasure X := ⟨μ, inferInstance⟩ with hμ'
  have hne : μ' ≠ 0 := by
    intro h
    apply hμ
    have := congrArg FiniteMeasure.toMeasure h
    simpa [hμ'] using this
  refine ⟨μ'.mass, μ'.normalize, (FiniteMeasure.mass_nonzero_iff μ').2 hne, ?_⟩
  have h := congrArg FiniteMeasure.toMeasure (FiniteMeasure.self_eq_mass_smul_normalize μ')
  rw [FiniteMeasure.toMeasure_smul] at h
  exact h

end Scaling

end FunctionalInequalities.KLS.MetricBV

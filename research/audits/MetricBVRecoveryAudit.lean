import FunctionalInequalities.Analysis.MetricBV.Basic
import FunctionalInequalities.Analysis.MetricBV.Finite
import FunctionalInequalities.Analysis.MetricBV.Approximation
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent full-signature clients for the epsilon recovery test of the metric BV perimeter:
the general statement for every Borel measure, a finite threshold and the top threshold. The
concrete instances use the empty set for an arbitrary measure, including Lebesgue measure on
`ℝ`, and the whole line for the standard Gaussian law. This is a prerequisite for diagonal
recovery, not a Minkowski recovery statement. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace MetricBVRecoveryAudit

open FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem recoveryTest (ν : Measure X) (B : Set X) {a : ENNReal} (ha : perimeter ν B < a)
    {ε : ENNReal} (hε : 0 < ε) :
    ∃ g : Test X, indicatorDistance ν g B < ε ∧ cost ν g < a := by
  exact exists_test_lt_of_perimeter_lt ν B ha hε

/-- Top threshold: finite perimeter yields finite-cost tests arbitrarily close in `L¹`. -/
theorem topThreshold (ν : Measure X) (B : Set X) (hB : perimeter ν B < ⊤) {ε : ENNReal}
    (hε : 0 < ε) : ∃ g : Test X, indicatorDistance ν g B < ε ∧ cost ν g < ⊤ := by
  exact exists_test_lt_of_perimeter_lt ν B hB hε

/-- Finite threshold for an arbitrary (possibly infinite) measure: the empty set. -/
theorem finiteThresholdEmpty (ν : Measure X) {ε : ENNReal} (hε : 0 < ε) :
    ∃ g : Test X, indicatorDistance ν g ∅ < ε ∧ cost ν g < 1 / 2 := by
  refine exists_test_lt_of_perimeter_lt ν ∅ ?_ hε
  rw [perimeter_empty]
  simp

/-- The same for Lebesgue measure on `ℝ`, an infinite measure. -/
theorem lebesgueEmpty {ε : ENNReal} (hε : 0 < ε) :
    ∃ g : Test ℝ, indicatorDistance (volume : Measure ℝ) g ∅ < ε ∧
      cost (volume : Measure ℝ) g < 1 := by
  refine exists_test_lt_of_perimeter_lt (volume : Measure ℝ) ∅ ?_ hε
  rw [perimeter_empty]
  exact zero_lt_one

/-- A finite threshold on the whole line for the standard Gaussian law, whose perimeter is zero
by the globally Lipschitz bridge applied to the constant one. -/
theorem gaussianWholeLine {ε : ENNReal} (hε : 0 < ε) {a : ENNReal} (ha : 0 < a) :
    ∃ g : Test ℝ, indicatorDistance (ProbabilityTheory.gaussianReal 0 1) g Set.univ < ε ∧
      cost (ProbabilityTheory.gaussianReal 0 1) g < a := by
  refine exists_test_lt_of_perimeter_lt _ _ ?_ hε
  have h := perimeter_le_liminf_of_lipschitz (ProbabilityTheory.gaussianReal 0 1)
    (B := Set.univ) (f := fun _ _ => (1 : ℝ)) (fun _ => ⟨0, LipschitzWith.const 1⟩)
    (by simp)
  simp only [FunctionalInequalities.Energy.LocalSlope.apply_const, lintegral_zero,
    Filter.liminf_const] at h
  exact (le_antisymm h bot_le).symm ▸ ha

#print axioms recoveryTest
#print axioms topThreshold
#print axioms finiteThresholdEmpty
#print axioms lebesgueEmpty
#print axioms gaussianWholeLine

end MetricBVRecoveryAudit

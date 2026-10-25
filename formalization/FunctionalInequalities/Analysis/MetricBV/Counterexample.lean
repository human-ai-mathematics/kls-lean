import FunctionalInequalities.Analysis.MetricBV.Basic

/-!
# Infinite-volume counterexample to metric BV complement symmetry
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [BorelSpace X]
/-- Complement symmetry fails for Lebesgue measure on the real line: the empty set has perimeter
zero while the whole line has infinite perimeter. -/
theorem perimeter_compl_ne_real_volume :
    perimeter (volume : Measure ℝ) (∅ : Set ℝ)ᶜ ≠ perimeter (volume : Measure ℝ) ∅ := by
  rw [Set.compl_empty, perimeter_empty,
    perimeter_univ_eq_top_of_forall_isBounded (volume : Measure ℝ) fun S hS => ?_]
  · exact ENNReal.top_ne_zero
  obtain ⟨b, hb⟩ := hS.bddAbove
  refine top_le_iff.mp ((Real.volume_Ioi (a := b)).symm.le.trans (measure_mono fun x hx => ?_))
  exact fun hxS => not_le.mpr (Set.mem_Ioi.mp hx) (hb hxS)


end FunctionalInequalities.KLS.MetricBV

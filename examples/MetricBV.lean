module

public import FunctionalInequalities.Analysis.MetricBV.Complement
public import FunctionalInequalities.Analysis.MetricBV.Scaling

/-!
# Metric perimeter under finite-mass rescaling

A client of the generic metric BV owners on an arbitrary metric space. The measure is finite,
without a probability, properness, finite-dimensional or log-concavity assumption. Nonzero
rescaling and finite-measure complement symmetry compose without importing a KLS application.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities.KLS.MetricBV
open scoped NNReal ENNReal

assert_not_exists FunctionalInequalities.KLS.Conjecture
assert_not_exists FunctionalInequalities.Poincare.SmoothTest.Holds

namespace Examples.MetricBV

/-- Rescale the perimeter of the complementary set, allowing infinite perimeter. -/
theorem scaled_complement_perimeter {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (c : ℝ≥0) (hc : c ≠ 0) (B : Set X) :
    perimeter (c • ν) Bᶜ = c * perimeter ν B := by
  rw [perimeter_smul c hc, perimeter_compl_of_isFiniteMeasure ν B]

end Examples.MetricBV

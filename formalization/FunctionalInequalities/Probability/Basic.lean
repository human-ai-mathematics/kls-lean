import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Probability-measure boundary

Public measure-dependent definitions in the new foundation take a bundled
`ProbabilityMeasure`. Low-level lemmas that already carry a `Measure` together with an
`IsProbabilityMeasure` instance can cross that boundary through the single constructor here.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Probability

variable {α : Type*} [MeasurableSpace α]

/-- Bundle a measure whose probability normalization is already available as an instance. -/
def ofMeasure (μ : Measure α) [IsProbabilityMeasure μ] : ProbabilityMeasure α :=
  ⟨μ, inferInstance⟩

/-- Unbundling `ofMeasure` recovers the original measure definitionally. -/
@[simp]
theorem coe_ofMeasure (μ : Measure α) [IsProbabilityMeasure μ] :
    (ofMeasure μ : Measure α) = μ :=
  rfl

end FunctionalInequalities.Probability

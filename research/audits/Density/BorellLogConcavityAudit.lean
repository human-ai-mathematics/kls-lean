module

public import FunctionalInequalities.KLS.LogConcave.Density.FromBorell

/-! Independent full-signature client for the finite-dimensional Borell-density converse. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace BorellDensityLogConcavityAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem compact_logConcave {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity
      (ν : Measure V) volume ρ) :
    FunctionalInequalities.KLS.LogConcave ν :=
  hρ.compactLogConcave

end BorellDensityLogConcavityAudit

#print axioms BorellDensityLogConcavityAudit.compact_logConcave

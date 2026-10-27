import FunctionalInequalities.Analysis.Sard.Sharp
import Lean

open FunctionalInequalities.Analysis MeasureTheory
open scoped ContDiff

namespace SardSharpImportAudit

theorem finite_regularity {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {u : V → ℝ}
    (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 :=
  sard hu

run_cmd do
  let env ← Lean.getEnv
  if env.header.moduleNames.contains `FunctionalInequalities.Analysis.Sard.Smooth then
    throwError "The sharp finite-regularity theorem loads the separate smooth route"
  if env.contains `FunctionalInequalities.Analysis.sard_smooth then
    throwError "The smooth Sard theorem leaked into the finite-regularity client"

#print axioms finite_regularity
end SardSharpImportAudit

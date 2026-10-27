import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation
import Lean

open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery

namespace TruncationNamesAudit

theorem eventual_mass (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∀ᶠ R : ℕ in atTop, ν (Metric.closedBall 0 R) ≠ 0 :=
  eventually_measure_closedBall_ne_zero ν

run_cmd do
  let env ← Lean.getEnv
  for name in #[`FunctionalInequalities.Analysis.BakryEmery.eventually_measure_closedBall_ne_zero_cond,
      `FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond] do
    if (env.find? name).isSome then
      throwError "An old conditional suffix remains as an alias: {name}"

#print axioms eventual_mass
end TruncationNamesAudit

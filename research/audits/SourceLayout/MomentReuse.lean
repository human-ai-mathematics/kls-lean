import FunctionalInequalities.Probability.ExponentialMoments.Norm
import Lean

open MeasureTheory FunctionalInequalities

/-- The deleted probability-only theorem's original hypotheses and conclusion. -/
example {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    {ν : Measure V} [IsProbabilityMeasure ν] {t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun v => Real.exp (t * ‖v‖)) ν) (p : ℕ) :
    Integrable (fun v => ‖v‖ ^ p) ν :=
  Probability.integrable_norm_pow_of_exp ν ht hint p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `FunctionalInequalities.Probability.integrable_norm_pow_of_integrable_exp_norm then
    throwError "The duplicate probability-only moment theorem remains"
  if env.header.moduleNames.any (fun n => n.toString.startsWith "FunctionalInequalities.KLS") then
    throwError "Generic norm moments import KLS"

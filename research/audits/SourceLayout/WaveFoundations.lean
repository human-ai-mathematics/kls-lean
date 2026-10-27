import FunctionalInequalities.Analysis.WaveSplitting.Stability
import FunctionalInequalities.Analysis.WaveSplitting.FlowDerivative
import Lean

open MeasureTheory FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff

example {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) : ContDiff ℝ ∞ (coupling b Y) :=
  State.Smooth.coupling hb hY

example {E ι : Type*} [NormedAddCommGroup E] [Fintype ι]
    (b : ι → E → ℝ) (Y : State E ι) (hp : ∀ j, HasCompactSupport (Y.p j)) :
    HasCompactSupport (coupling b Y) := hasCompactSupport_coupling b Y hp

run_cmd do
  let env ← Lean.getEnv
  for n in [`FunctionalInequalities.Analysis.WaveSplitting.timeAverage,
      `FunctionalInequalities.Analysis.WaveSplitting.weightedEnergy] do
    if env.contains n then throwError "Higher-layer declaration in the foundation client: {n}"

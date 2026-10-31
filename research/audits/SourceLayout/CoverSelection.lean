module

public import FunctionalInequalities.Analysis.Hausdorff.Content
public import Lean
meta import Lean

@[expose] public section

open MeasureTheory FunctionalInequalities.Analysis
open scoped ENNReal

/-- The scalar/vector copies have this same contract, with an arbitrary real gauge. -/
example {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} {S : Set X} {r c : ENNReal} (hr : 0 < r) (hc : μH[d] S < c) :
    ∃ T : ℕ → Set X, S ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧
      ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d < c :=
  exists_cover_familyCost_lt (A := S) hr hc

run_cmd do
  let env ← Lean.getEnv
  for n in [`FunctionalInequalities.Analysis.exists_cover_cost_lt,
      `FunctionalInequalities.Analysis.exists_cover_cost_lt_vector,
      `FunctionalInequalities.Analysis.exists_measurable_majorant,
      `FunctionalInequalities.Analysis.exists_levelBall] do
    if env.contains n then throwError "Application/copy leaked into the cover foundation: {n}"

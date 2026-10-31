module

public import FunctionalInequalities.Probability.Moments
public import Lean
meta import Lean

@[expose] public section

open FunctionalInequalities MeasureTheory

/-- The exact original finite-dimensional inner-product interface is retained. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (S : E →L[ℝ] E) (hμ4 : MemLp id 4 μ) : MemLp id 4 (μ.map S) :=
  Probability.memLp_four_map_linear μ S hμ4

run_cmd do
  let env ← Lean.getEnv
  if env.header.moduleNames.any (fun n => n.toString.startsWith "FunctionalInequalities.KLS") then
    throwError "Linear-image moments import KLS"

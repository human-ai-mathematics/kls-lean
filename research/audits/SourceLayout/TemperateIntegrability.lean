module

public import Lean
public import FunctionalInequalities.Probability.ExponentialMoments.Temperate
public import Mathlib.Analysis.Normed.Module.FiniteDimension
meta import Lean

/-! Legacy scalar/vector integrability contracts and the lower normed-space producer.
The scalar contract has no second-countability or finite-dimensional source premise.
Neither target completeness nor a probability/finite-measure instance is introduced.
-/

@[expose] public section
set_option autoImplicit false
open FunctionalInequalities MeasureTheory
namespace SourceLayout

theorem temperate_scalar_l1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → ℝ} (hg : g.HasTemperateGrowth) : Integrable g μ :=
  Probability.integrable_of_hasTemperateGrowth (μ := μ) (hexp := hexp) (g := g) hg

theorem temperate_vector_l1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → F} (hg : g.HasTemperateGrowth) : Integrable g μ :=
  Probability.integrable_of_hasTemperateGrowth μ hexp hg

theorem temperate_normed_l1 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → F} (hg : g.HasTemperateGrowth) : Integrable g μ :=
  Probability.integrable_of_hasTemperateGrowth μ hexp hg

run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    if name.toString.startsWith "FunctionalInequalities.KLS." ||
        name.toString.startsWith "FunctionalInequalities.Energy." ||
        name.toString.startsWith "FunctionalInequalities.Analysis.BakryEmery." then
      throwError "The temperate integrability producer must stay below its analytic applications"

#print axioms Probability.integrable_of_hasTemperateGrowth
#print axioms temperate_scalar_l1
#print axioms temperate_vector_l1
#print axioms temperate_normed_l1
end SourceLayout

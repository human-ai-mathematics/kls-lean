module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.Measure
public import Lean
meta import Lean

/-! Actual domain measures with no supplied measure, density or positive dimension. -/

@[expose] public section
set_option autoImplicit false
open FunctionalInequalities MeasureTheory
namespace SourceLayout

theorem domain_measure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hv : ConvexOn ℝ Ω v) (hc : ContinuousOn v Ω) :
    ∃ μ : Measure E,
      (∀ G : Set E, MeasurableSet G →
        μ G = (volume : Measure E) (Analysis.subgradientImageOn v Ω (G ∩ Ω))) ∧
      (∀ K : Set E, IsCompact K → K ⊆ Ω → μ K < ⊤) :=
  Analysis.exists_domain_mongeAmpere_measure hΩ hv hc

#print axioms SourceLayout.domain_measure
open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `FunctionalInequalities.Analysis.exists_domain_mongeAmpere_measures_local_limits then
    throwError "Domain measure construction must not import its stability consumer"
end SourceLayout

module

public import FunctionalInequalities.Probability.MomentMeasure.Maximality.BallTruncation
public import Lean
meta import Lean
import all FunctionalInequalities.Analysis.Convex.Coercivity
import all FunctionalInequalities.Analysis.Convex.Legendre.AffineMaximum
import all FunctionalInequalities.Analysis.Convex.Legendre.Basic
import all FunctionalInequalities.Analysis.Convex.Legendre.Biconjugate
import all FunctionalInequalities.Analysis.Convex.Legendre.SupportingPlane
import all FunctionalInequalities.Analysis.Convex.Legendre.Variation.Attainment
import all FunctionalInequalities.Analysis.Convex.Legendre.Variation.Derivative
import all FunctionalInequalities.Analysis.Convex.Legendre.Variation.Perturbation
import all FunctionalInequalities.Analysis.Convex.Subgradient.Basic
import all FunctionalInequalities.Analysis.Convex.Subgradient.Measure
import all FunctionalInequalities.Analysis.Extremum
import all FunctionalInequalities.Probability.MomentMeasure.Basic
import all FunctionalInequalities.Probability.MomentMeasure.FirstVariation
import all FunctionalInequalities.Probability.MomentMeasure.Maximality.BallTruncation

/-! Narrow client of the existing CEK (7) growth contract and its shared boundedness producer.
Only proof organization changes; normalization, finite nonzero mass and dimensional scope stay
with the moment-potential consumer.
-/

@[expose] public section

set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure

namespace SourceLayout.MomentGrowth

theorem mass_growth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ψ : E → EReal} (hψ : ConvexPotential ψ) (hlsc : LowerSemicontinuous ψ)
    (h0 : mass volume ψ ≠ 0) (htop : mass volume ψ ≠ ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∃ b : ℝ, ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x :=
  exists_linear_lower_bound_of_mass (hψ := hψ) (hlsc := hlsc) (h0 := h0) (htop := htop)

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some info := env.find?
      `FunctionalInequalities.Probability.MomentMeasure.exists_linear_lower_bound_of_mass
    | throwError "Missing CEK growth consumer"
  let some proof := info.value? (allowOpaque := true)
    | throwError "Missing CEK growth proof"
  unless proof.getUsedConstants.contains
      `FunctionalInequalities.Analysis.isBounded_of_convex_of_measure_lt_top do
    throwError "The CEK growth consumer must call the shared boundedness producer"
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "_private." &&
        name.toString.endsWith ".isBounded_of_convex_of_measure_lt_top" then
      throwError "The private duplicate boundedness producer must be removed: {name}"

#print axioms exists_linear_lower_bound_of_mass
#print axioms mass_growth

end SourceLayout.MomentGrowth

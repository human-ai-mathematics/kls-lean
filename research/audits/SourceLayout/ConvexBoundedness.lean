module

public import FunctionalInequalities.Analysis.Convex.Coercivity
public import Lean
meta import Lean
import all FunctionalInequalities.Analysis.Convex.Coercivity

/-! The shared finite-Haar-measure boundedness step, below its moment-measure consumers.
The generic client has no inner product, finite dimension, completeness or nontriviality premise.
The single-point client derives its finite-measure and ball-containment inputs.
-/

@[expose] public section

set_option autoImplicit false
open MeasureTheory Set FunctionalInequalities.Analysis

namespace SourceLayout.ConvexBoundedness

theorem normed_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]
    (s : Set E) (hcs : Convex ℝ s) (hms : m s < (⊤ : ENNReal))
    (hrball : ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : E) r ⊆ s) : Bornology.IsBounded s :=
  isBounded_of_convex_of_measure_lt_top (E := E) (m := m) (s := s)
    (hcs := hcs) (hms := hms) (hrball := hrball)

theorem single_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Subsingleton E]
    (m : Measure E) [m.IsAddHaarMeasure] : Bornology.IsBounded (univ : Set E) := by
  have huniv : (univ : Set E) = {0} := by
    ext x
    simp [Subsingleton.elim x 0]
  apply isBounded_of_convex_of_measure_lt_top m univ convex_univ
  · rw [huniv]
    exact isCompact_singleton.measure_lt_top
  · exact ⟨1, zero_lt_one, subset_univ _⟩

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if name.toString.startsWith "FunctionalInequalities.Probability." ||
        name.toString.startsWith "FunctionalInequalities.KLS." then
      throwError "Convex boundedness must remain below probability and paper consumers: {name}"
  let some info := env.find?
      `FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
    | throwError "Missing compact-sublevel consumer"
  let some proof := info.value? (allowOpaque := true)
    | throwError "Missing compact-sublevel proof"
  unless proof.getUsedConstants.contains
      `FunctionalInequalities.Analysis.isBounded_of_convex_of_measure_lt_top do
    throwError "The compact-sublevel consumer must call the shared boundedness producer"

#print axioms isBounded_of_convex_of_measure_lt_top
#print axioms normed_space
#print axioms single_point

end SourceLayout.ConvexBoundedness

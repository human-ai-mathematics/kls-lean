module

public import FunctionalInequalities.Analysis.Graph.Area
public import Lean
meta import Lean

/-! The former graph gradient-continuity contract uses the common calculus theorem. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FunctionalInequalities

namespace SourceLayout

theorem graph_gradient_continuity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {g : H → ℝ}
    (hg : ContDiff ℝ 1 g) : Continuous (gradient g) :=
  Analysis.BakryEmery.continuous_gradient hg

#print axioms SourceLayout.graph_gradient_continuity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if env.contains `FunctionalInequalities.Analysis.continuous_gradient then
    throwError "The duplicate graph gradient-continuity declaration must not survive"

end SourceLayout

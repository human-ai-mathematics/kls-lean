module

public import FunctionalInequalities.Analysis.Convex.Boundary
public import Lean
meta import Lean

/-! The interior-ball step has no finite-dimensional, inner-product or completeness premise.
The single-point client also checks that nontriviality is not added.
-/

@[expose] public section

set_option autoImplicit false
open Set Metric FunctionalInequalities.Analysis

namespace SourceLayout.ConvexInterior

theorem normed_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty)
    {x : E} {r R : ℝ} (hrR : r < R) (hball : ball x R ⊆ closure s) :
    closedBall x r ⊆ s :=
  closedBall_subset_of_ball_subset_closure hs hc hne hrR hball

theorem single_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Subsingleton E] {x : E} : closedBall x 0 ⊆ (univ : Set E) :=
  closedBall_subset_of_ball_subset_closure isOpen_univ convex_univ ⟨x, mem_univ x⟩ zero_lt_one
    (by simp)

open Lean Elab Command in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if name.toString.startsWith "FunctionalInequalities.KLS." ||
        name.toString.startsWith "FunctionalInequalities.Probability." then
      throwError "Convex interior geometry must stay below its application consumers: {name}"

#print axioms normed_space
#print axioms single_point

end SourceLayout.ConvexInterior

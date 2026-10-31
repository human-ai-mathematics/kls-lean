module

public import FunctionalInequalities.Analysis.Convex.Section.Affine
public import Lean
meta import Lean

/-! Section algebra below finite-dimensional estimates and covering. -/

@[expose] public section
set_option autoImplicit false
open FunctionalInequalities
open scoped RealInnerProductSpace
namespace SourceLayout

theorem section_affine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E → ℝ) (x p : E) (h : ℝ) :
    {y | u y < u x + ⟪p, y - x⟫ + h} =
      {y | u y - (⟪p, y⟫ + (u x - ⟪p, x⟫ + h)) < 0} :=
  Analysis.section_eq_sublevel u x p h

#print axioms SourceLayout.section_affine
open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `FunctionalInequalities.Analysis.SoftEngulfing.exists_bregman_comparison_core then
    throwError "Affine section algebra must not import engulfing geometry"
end SourceLayout

module

public import FunctionalInequalities.Analysis.Divergence
public import FunctionalInequalities.Analysis.BakryEmery.Calculus
public import Lean
meta import Lean

/-! Clients for Mathlib derivative reuse and the shared gradient consequence. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FunctionalInequalities

namespace SourceLayout

/-- The shared gradient support property does not require finite dimension. -/
theorem gradient_support {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) :
    gradient f x = 0 :=
  Analysis.BakryEmery.gradient_eq_zero_of_notMem_tsupport hx

#print axioms SourceLayout.gradient_support

/-- Nonzero regularity order, with no finite-dimensional hypothesis. -/
theorem gradient_continuity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hn : n ≠ 0) :
    Continuous (gradient f) :=
  Analysis.BakryEmery.continuous_gradient_of_contDiff hf hn

#print axioms SourceLayout.gradient_continuity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if env.contains `FunctionalInequalities.Analysis.fderiv_eq_zero_of_notMem_tsupport then
    throwError "The removed derivative wrapper must not survive in its original owner"

end SourceLayout

module

public import Lean
public import Mathlib.Order.Filter.ENNReal
public import FunctionalInequalities.Analysis.BakryEmery.Calculus
meta import Lean

/-! Original finite-constant `liminf` scaling and affine-line derivative contracts.
The `liminf` identity holds for every nontrivial filter on `ℝ≥0∞` (pinned Mathlib);
the line derivative needs only a real inner-product space, without completeness,
finite dimension or measurable structure.
-/

@[expose] public section
set_option autoImplicit false
open FunctionalInequalities Filter
open scoped NNReal ENNReal

namespace SourceLayout

theorem liminf_coe_mul_contract {ι : Type*} {l : Filter ι} [l.NeBot] (c : ℝ≥0)
    (u : ι → ℝ≥0∞) :
    liminf (fun i => (c : ℝ≥0∞) * u i) l = c * liminf u l :=
  ENNReal.liminf_const_mul_of_ne_top (a := (c : ℝ≥0∞)) ENNReal.coe_ne_top

theorem line_hasDerivAt_zero_contract {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c h : E) :
    HasDerivAt (fun t : ℝ => c + t • h) h 0 :=
  Analysis.BakryEmery.hasDerivAt_line c h 0

theorem line_deriv_contract {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x v : E) (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v t :=
  Analysis.BakryEmery.hasDerivAt_line x v t

run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    if name.toString.startsWith "FunctionalInequalities.Probability.Posterior." ||
        name.toString.startsWith "FunctionalInequalities.KLS." ||
        name == `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic then
      throwError "Shared line derivative must stay below its consumers: {name}"

#print axioms liminf_coe_mul_contract
#print axioms line_hasDerivAt_zero_contract
#print axioms line_deriv_contract

end SourceLayout

import FunctionalInequalities.Analysis.WeakDerivative.Products
import Lean

/-! The product rule on arbitrary finite real Hilbert spaces, without testing imports. -/
set_option autoImplicit false
open FunctionalInequalities MeasureTheory
namespace SourceLayout

theorem weak_product {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f df g dg : E → ℝ} {v : E}
    (hf : Analysis.HasWeakDerivAlong f df v) (hg : Analysis.HasWeakDerivAlong g dg v)
    (hf2 : MemLp f 2 (volume : Measure E)) (hdf2 : MemLp df 2 (volume : Measure E))
    (hg2 : MemLp g 2 (volume : Measure E)) (hdg2 : MemLp dg 2 (volume : Measure E)) :
    Analysis.HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v :=
  hf.mul_of_memLp_two hg hf2 hdf2 hg2 hdg2

#print axioms SourceLayout.weak_product
open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test then
    throwError "Product clients must not import the rough-testing layer"
end SourceLayout

import Lean
import FunctionalInequalities.Analysis.Convex.Subgradient.Basic
import FunctionalInequalities.Probability.Transport
import FunctionalInequalities.L2.Pairing

/-! Original supporting-plane, translated-moment and L² energy contracts.
The translation uses only a normed additive group; the energy identity uses
an arbitrary measurable source and real inner-product target, without completeness.
-/
set_option autoImplicit false
open FunctionalInequalities MeasureTheory Set
open scoped RealInnerProductSpace

namespace SourceLayout

theorem gradient_support {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {u : E → ℝ} (hc : ConvexOn ℝ univ u)
    (a v : E) (ha : DifferentiableAt ℝ u a) :
    ⟪gradient u a, v⟫ ≤ u (a + v) - u a :=
  Analysis.gradient_le_increment (hc := hc) (z := a) (v := v) (hz := ha)

theorem translate_memLp_two {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : ProbabilityMeasure E) (c : E)
    (h2 : MemLp id 2 (μ : Measure E)) :
    MemLp id 2 (Probability.translateLaw μ c : Measure E) :=
  Probability.memLp_id_two_translateLaw (ν := μ) (c := c) (h := h2)

theorem l2_norm_sq {α : Type*} [MeasurableSpace α]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure α} (f : Lp F 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ :=
  L2.norm_sq_eq_integral_norm_sq (α := α) (F := F) (μ := μ) (f := f)

run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    if name.toString.startsWith "FunctionalInequalities.KLS." ||
        name.toString.startsWith "FunctionalInequalities.Energy." ||
        name == `FunctionalInequalities.Analysis.Convex.Gradient.Image ||
        name == `FunctionalInequalities.L2.Components then
      throwError "Shared producers must stay below their concrete consumers: {name}"

#print axioms gradient_support
#print axioms translate_memLp_two
#print axioms l2_norm_sq

end SourceLayout

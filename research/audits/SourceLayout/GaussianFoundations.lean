import FunctionalInequalities.Probability.Gaussian.Moments
import Lean

/-! Generic Gaussian clients: no KLS, no positive-dimension premise, exact variance. -/
open MeasureTheory FunctionalInequalities.Probability
open scoped RealInnerProductSpace
namespace GaussianFoundationsAudit

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : ℝ} (hs : 0 < s) (v : E) :
    (∫ x, ⟪v, x⟫ ^ 2 ∂Gaussian.law s) = ‖v‖ ^ 2 / (2 * s) :=
  Gaussian.integral_inner_sq hs v

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : ℝ} (hs : 0 < s) : MemLp id 4 (Gaussian.law (V := E) s) :=
  Gaussian.memLp_four hs

example : IsProbabilityMeasure (Gaussian.law (V := EuclideanSpace ℝ (Fin 0)) (1 / 2)) :=
  Gaussian.law_probability (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.header.moduleNames.any (fun n => n.toString.startsWith "FunctionalInequalities.KLS") then
    throwError "Gaussian foundation imports KLS"
end GaussianFoundationsAudit

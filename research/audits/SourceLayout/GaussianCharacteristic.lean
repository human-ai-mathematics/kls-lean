module

public import FunctionalInequalities.Probability.Gaussian.CharacteristicFunction
public import Lean
meta import Lean

@[expose] public section

open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability

example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {s : ℝ} (hs : 0 < s) : Gaussian.law (V := V) s =
      (stdGaussian V).map (fun x : V => (Real.sqrt (2 * s))⁻¹ • x) :=
  Gaussian.law_eq_scaled_stdGaussian hs

example {s : ℝ} (hs : 0 < s) : Gaussian.law (V := EuclideanSpace ℝ (Fin 0)) s =
      (stdGaussian (EuclideanSpace ℝ (Fin 0))).map (fun x => (Real.sqrt (2 * s))⁻¹ • x) :=
  Gaussian.law_eq_scaled_stdGaussian hs

run_cmd do
  let env ← Lean.getEnv
  if env.header.moduleNames.any (fun n =>
      n.toString.startsWith "FunctionalInequalities.KLS" ||
      n.toString.startsWith "FunctionalInequalities.Poincare") then
    throwError "The Gaussian object identification imports an application bound"

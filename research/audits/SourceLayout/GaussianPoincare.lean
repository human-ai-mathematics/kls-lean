module

public import FunctionalInequalities.Poincare.Gaussian.Multivariate
public import Lean
meta import Lean

@[expose] public section

open FunctionalInequalities MeasureTheory

example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {s : ℝ} (hs : 0 < s) :
    Poincare.SmoothTest.Holds (Probability.Gaussian.law (V := V) s) (1 / (2 * s)) :=
  Poincare.SmoothTest.holds_gaussianLaw hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw then
    throwError "The Gaussian Poincare bound imports smoothing"

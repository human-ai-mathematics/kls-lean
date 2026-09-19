import FunctionalInequalities.Probability.Covariance.Basic
import FunctionalInequalities.Probability.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Isotropic probability laws

Source: Blueprint `def:isotropic-law`. The three fields state finite second moment,
zero barycenter, and identity centered covariance. This is a definition, with no whitening
or equivalence theorem. On a zero-dimensional space the identity operator is itself zero.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- A probability law with finite second moment, mean zero, and identity centered covariance.
The moment field prevents the totalized integral/covariance from encoding integrability. -/
structure Isotropic (μ : ProbabilityMeasure E) : Prop where
  memLp_two : MemLp id 2 (μ : Measure E)
  mean_zero : ∫ x, x ∂(μ : Measure E) = 0
  covariance_identity : Covariance.operator (μ : Measure E) = ContinuousLinearMap.id ℝ E

end FunctionalInequalities.KLS

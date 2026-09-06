import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Covariance operator definition

The centered covariance bilinear form is represented by its Riesz operator. This definition
is shared by the literal KLS statement and the linear-test implementation, without importing
that implementation into the statement. Moment assumptions belong to the consuming results.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Covariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Source: local encoding of the source's centered covariance, using Mathlib's
`covarianceBilin` and `InnerProductSpace.continuousLinearMapOfBilin`.
The variance identification below retains its explicit second-moment hypothesis. -/
def operator (μ : Measure E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (covarianceBilin μ)

/-- Source: local Riesz-representation identity from
`InnerProductSpace.continuousLinearMapOfBilin_apply`. -/
@[simp]
theorem operator_inner (μ : Measure E) (x y : E) :
    inner ℝ (operator μ x) y = covarianceBilin μ x y := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply (covarianceBilin μ) x y

end FunctionalInequalities.Covariance

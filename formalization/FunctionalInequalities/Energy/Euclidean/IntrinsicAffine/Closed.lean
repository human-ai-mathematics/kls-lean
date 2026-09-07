import FunctionalInequalities.Energy.Euclidean.IntrinsicAffine.Basic
import FunctionalInequalities.Energy.Euclidean.SmoothGradient.Closed

/-!
# Closed quadratic energy in intrinsic affine coordinates

The intrinsic-coordinate map identifies the original real `L²` space linearly and isometrically
with real `L²` of the probability law on the direction of its affine support. Pulling the
closed smooth-gradient relaxation back along this equivalence preserves the complete
closed-quadratic structure.

This is an intrinsic-affine smooth-relaxation theorem. It is not an identification with Cheeger
energy, a Markov theorem, or an agreement statement for raw ambient gradients.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Energy.Canonical

open Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The intrinsic-affine smooth-gradient relaxation is a densely defined closed quadratic
functional on the original real `L²(μ)` space. -/
theorem closedQuadratic
    (μ : ProbabilityMeasure E) :
    ClosedQuadratic (energy μ) :=
  (smoothGradientRelaxation_closedQuadratic
    (Probability.intrinsicMeasure μ)).comap_linearIsometryEquiv (intrinsicL2Equiv μ)

end FunctionalInequalities.Energy.Canonical

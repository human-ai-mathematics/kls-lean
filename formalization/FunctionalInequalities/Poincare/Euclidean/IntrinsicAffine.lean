import FunctionalInequalities.Energy.Euclidean.IntrinsicAffine.Closed
import FunctionalInequalities.Poincare.L2Energy

/-!
# Poincaré optimization in intrinsic affine coordinates

This module attaches the generic real-`L²` Poincaré optimizer to the closed quadratic
smooth-gradient relaxation on the direction of the affine support. The variance is still the
intrinsic `L²(μ)` variance of the original probability law; only the energy is evaluated through
the linearly isometric intrinsic-coordinate presentation.

The `Poincare.Canonical` namespace names the frontend selected by the repository: the
intrinsic-affine smooth-gradient relaxation. Its construction remains explicit in
`Energy.Canonical.energy`; the name itself asserts no Cheeger or spectral identification.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.Canonical

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The optimal Poincaré constant of the intrinsic-affine smooth-gradient relaxation. -/
def constant (μ : ProbabilityMeasure E) : ENNReal :=
  L2Energy.constant μ
    (Energy.Canonical.energy μ)

/-- Validity of a finite Poincaré constant on the finite domain of the intrinsic-affine
smooth-gradient relaxation. -/
def Holds
    (μ : ProbabilityMeasure E) (C : NNReal) : Prop :=
  L2Energy.Holds μ (Energy.Canonical.energy μ) C

/-- A finite constant is valid for the intrinsic-affine relaxation exactly when it bounds the
optimal extended constant. -/
theorem holds_iff_constant_le
    (μ : ProbabilityMeasure E) (C : NNReal) :
    Holds μ C ↔
      constant μ ≤ (C : ENNReal) := by
  exact L2Energy.holds_iff_constant_le μ
    (Energy.Canonical.energy μ) C

end FunctionalInequalities.Poincare.Canonical

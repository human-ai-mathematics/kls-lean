import FunctionalInequalities.Energy.Euclidean.AffineComparison
import FunctionalInequalities.Poincare.Euclidean.IntrinsicAffine
import FunctionalInequalities.Poincare.Euclidean.SmoothGradient

/-!
# Ambient and intrinsic-affine Poincaré comparisons

Proved optimizer consequences for `lem:ambient-intrinsic-poincare-comparison`.
The two functionals are represented on the same original `L²(μ)` space, so the variance is
identical and energy equality identifies both their finite domains and their optimal constants.

Source: Blueprint `cor:ambient-intrinsic-constant-equality` and its energy-level predecessor.
Neither raw/core agreement nor a literature or Cheeger-energy identification is a premise.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.Ambient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)

/-- Ambient and intrinsic-affine inequalities have the same valid finite constants.
Source: exact equality of the relaxed energies on their common ambient carrier. -/
theorem holds_iff_canonical (C : NNReal) :
    Holds μ C ↔ Canonical.Holds μ C := by
  unfold Holds Canonical.Holds
  rw [Energy.Euclidean.smoothGradientRelaxation_eq_canonical]

/-- The ambient and selected optima agree in `ENNReal`, with no finiteness assumption.
Source: Blueprint `cor:ambient-intrinsic-constant-equality`. -/
theorem constant_eq_canonical :
    constant μ = Canonical.constant μ := by
  unfold constant Canonical.constant
  rw [Energy.Euclidean.smoothGradientRelaxation_eq_canonical]

end FunctionalInequalities.Poincare.Ambient

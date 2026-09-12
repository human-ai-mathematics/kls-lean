import FunctionalInequalities.Energy.Cheeger

/-!
# The singular-measure Cheeger comparisons (work in progress)

Work-in-progress module for Blueprint `thm:smooth-gradient-relaxation-two-cheeger`, the
unconditional identity `𝓔^can_μ = 2 Ch_μ`.  Everything provable from certified repository input
now lives in `Energy/LocalSlope/Relaxation.lean` and `Energy/Cheeger.lean`, which are registered
and `sorry`-free; in particular the absolutely continuous and log-concave scope is proved and
certified as `cor:absolutely-continuous-relaxation-two-cheeger`.

What remains here are the five open obligations of the singular case.  Two are genuine:

* `LocalSlope.relaxation_eq_asymptoticLipschitz` — the two Cheeger conventions relax to the same
  functional (Ambrosio--Gigli--Savaré 2013; the Blueprint records no source for singular laws);
* `SmoothGradient.relaxation_eq_localSlope` — the smooth-gradient relaxation is the relaxed
  squared local slope without an absolute-continuity hypothesis.

The other three are three-line consequences of those two, kept here so that the Blueprint
statement itself has a Lean home:

* `Cheeger.energy_eq_ofAsymptoticLipschitz` (from the first),
* `SmoothGradient.relaxation_eq_two_mul_cheeger` and
  `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger` (from the second, through
  `Cheeger.two_mul_energy` and `SmoothGradient.Intrinsic.energy_apply`).

This module is not imported by the library root, not registered in the ledger, and not anchored
from the Blueprint.  Nothing here may be used by a registered module.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Energy

universe u

namespace LocalSlope

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The two Cheeger conventions relax to the same `L²(ν)` functional, for every Borel
probability law on a finite-dimensional inner-product space.  Source: Ambrosio–Gigli–Savaré
2013 (density of Lipschitz functions and equivalence of weak gradients), specialized to the
Euclidean carrier; the Blueprint records no source for singular laws, so this equality is an
explicit obligation and is never used definitionally. -/
theorem relaxation_eq_asymptoticLipschitz (ν : ProbabilityMeasure V) :
    relaxation ν = AsymptoticLipschitz.relaxation ν := by
  sorry

end LocalSlope

namespace Cheeger

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The two conventions give the same Cheeger energy; consequence of
`LocalSlope.relaxation_eq_asymptoticLipschitz`. -/
theorem energy_eq_ofAsymptoticLipschitz (ν : ProbabilityMeasure V) :
    energy ν = ofAsymptoticLipschitz ν := by
  sorry

end Cheeger

namespace SmoothGradient

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The smooth-gradient relaxation is the relaxed squared local slope, for every Borel
probability law on a finite-dimensional inner-product space.  The singular case is the open
comparison the Blueprint flags; no source is recorded for it. -/
theorem relaxation_eq_localSlope (ν : ProbabilityMeasure V) :
    relaxation ν = LocalSlope.relaxation ν := by
  sorry

/-- Coordinate form of the Blueprint identity: the smooth-gradient relaxation is twice the
selected Cheeger energy. -/
theorem relaxation_eq_two_mul_cheeger (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f = 2 * Cheeger.energy ν f := by
  sorry

namespace Intrinsic

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- Blueprint `thm:smooth-gradient-relaxation-two-cheeger`: on ambient real `L²(μ)`, the selected
canonical energy `𝓔^can_μ = SmoothGradient.Intrinsic.energy μ` equals twice the metric Cheeger
energy of the intrinsic law on the affine support, transported along the intrinsic `L²`
isometry.  Every finite-dimensional Borel probability law is included, with the value `⊤`
allowed on both sides and a one-point affine support giving `0 = 2 * 0`. -/
theorem energy_eq_two_mul_cheeger (μ : ProbabilityMeasure E) (f : Lp ℝ 2 (μ : Measure E)) :
    energy μ f = 2 * Cheeger.Intrinsic.energy μ f := by
  sorry

end Intrinsic

end SmoothGradient

end FunctionalInequalities.Energy

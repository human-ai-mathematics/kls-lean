import FunctionalInequalities.Energy.Cheeger.Basic
import FunctionalInequalities.Energy.Euclidean.Slope.Comparison
import FunctionalInequalities.Energy.Euclidean.Slope.Density

/-!
# The Cheeger identification for every Borel probability law

Hole-free module for Blueprint `thm:smooth-gradient-relaxation-two-cheeger`, the unconditional
identity `𝓔^can_μ = 2 Ch_μ`.  It replaces the former work-in-progress module
`Energy/WIP/Cheeger.lean`; its five declarations are moved here with byte-identical `pp.all`
signatures (`build/audit/energy-slope-proofs/ppall-before.txt` and `ppall-after.txt`).

* `SmoothGradient.relaxation_eq_localSlope`: the smooth-gradient relaxation is the relaxed squared
  local slope, for every Borel probability law on a finite-dimensional inner-product space — the
  inequality `≤` is the density theorem of `Energy/Euclidean/Slope/Density.lean` (McShane patches on
  a slope-adapted Borel partition, smooth recovery of globally Lipschitz tests, a cutoff for general
  admissible tests), the inequality `≥` the unconditional `SmoothGradient.localSlope_relaxation_le`.
* `LocalSlope.relaxation_eq_asymptoticLipschitz`, `Cheeger.energy_eq_ofAsymptoticLipschitz`: the two
  Cheeger conventions agree, by collapsing the unconditional sandwich of
  `Energy/Euclidean/Slope/Comparison.lean`; this is a consequence of the identification, not a
  second obligation, and the citation of Ambrosio–Gigli–Savaré recorded for it in the former WIP
  module is no longer load-bearing.
* `SmoothGradient.relaxation_eq_two_mul_cheeger`, `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger`:
  the coordinate and the affine-support forms of `𝓔^can = 2 Ch`, the latter being the Blueprint
  statement, with the value `⊤` allowed on both sides and a one-point affine support giving
  `0 = 2 · 0`.

Closest literature: S. Eriksson-Bique, *Density of Lipschitz functions in energy*, Calc. Var. PDE
62 (2023), Art. 60, Thm 1.1 (general metric measure spaces); Ambrosio–Gigli–Savaré, Rev. Mat.
Iberoam. 29 (2013), §8.3 (the same conclusion via Hopf–Lax).  Nothing here is a Poincaré
inequality, a finiteness statement or a Cheeger–Buser comparison.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Energy

universe u

namespace SmoothGradient

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The smooth-gradient relaxation is the relaxed squared local slope, for every Borel
probability law on a finite-dimensional inner-product space: `≤` is the density of smooth tests in
the local-slope energy (`SlopeDensity`), `≥` is `localSlope_relaxation_le`. -/
theorem relaxation_eq_localSlope (ν : ProbabilityMeasure V) :
    relaxation ν = LocalSlope.relaxation ν :=
  Functional.ext fun f => le_antisymm (relaxation_le_localSlope ν f) (localSlope_relaxation_le ν f)

/-- Coordinate form of the Blueprint identity: the smooth-gradient relaxation is twice the
selected Cheeger energy. -/
theorem relaxation_eq_two_mul_cheeger (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f = 2 * Cheeger.energy ν f := by
  rw [Cheeger.two_mul_energy, relaxation_eq_localSlope ν]

end SmoothGradient

namespace LocalSlope

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The two Cheeger conventions relax to the same `L²(ν)` functional, for every Borel
probability law on a finite-dimensional inner-product space: the sandwich
`LocalSlope.relaxation ≤ AsymptoticLipschitz.relaxation ≤ SmoothGradient.relaxation` collapses once
the smooth-gradient relaxation is identified with the local-slope one. -/
theorem relaxation_eq_asymptoticLipschitz (ν : ProbabilityMeasure V) :
    relaxation ν = AsymptoticLipschitz.relaxation ν :=
  relaxation_eq_asymptoticLipschitz_of_smoothGradient ν (SmoothGradient.relaxation_eq_localSlope ν)

end LocalSlope

namespace Cheeger

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The two conventions give the same Cheeger energy; consequence of
`LocalSlope.relaxation_eq_asymptoticLipschitz`. -/
theorem energy_eq_ofAsymptoticLipschitz (ν : ProbabilityMeasure V) :
    energy ν = ofAsymptoticLipschitz ν := by
  refine Functional.ext fun f => ?_
  rw [energy_apply]
  show LocalSlope.relaxation ν f / 2 = AsymptoticLipschitz.relaxation ν f / 2
  rw [LocalSlope.relaxation_eq_asymptoticLipschitz ν]

end Cheeger

namespace SmoothGradient

namespace Intrinsic

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

-- The type is the one fixed by the statement round; `CompleteSpace E` is part of the frozen
-- signature, so the linter is silenced instead of the signature changed.
set_option linter.unusedSectionVars false in
/-- Blueprint `thm:smooth-gradient-relaxation-two-cheeger`: on ambient real `L²(μ)`, the selected
canonical energy `𝓔^can_μ = SmoothGradient.Intrinsic.energy μ` equals twice the metric Cheeger
energy of the intrinsic law on the affine support, transported along the intrinsic `L²`
isometry.  Every finite-dimensional Borel probability law is included, with the value `⊤`
allowed on both sides and a one-point affine support giving `0 = 2 * 0`. -/
theorem energy_eq_two_mul_cheeger (μ : ProbabilityMeasure E) (f : Lp ℝ 2 (μ : Measure E)) :
    energy μ f = 2 * Cheeger.Intrinsic.energy μ f := by
  rw [SmoothGradient.Intrinsic.energy_apply, Cheeger.Intrinsic.energy_apply,
    relaxation_eq_localSlope (Probability.intrinsicMeasure μ)]
  exact (Cheeger.two_mul_energy (Probability.intrinsicMeasure μ)
    (Energy.Euclidean.toIntrinsicL2 μ f)).symm

end Intrinsic

end SmoothGradient

end FunctionalInequalities.Energy

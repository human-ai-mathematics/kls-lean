import FunctionalInequalities.Poincare.LocalSlope.Basic
import FunctionalInequalities.Probability.AffineSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Definitions of the literature-facing KLS target

Source: Blueprint `def:log-concave-law` and `def:literature-poincare-constant`.
Read `LogConcave`, `Energy.LocalSlope.apply`, `Energy.LocalSlope.Admissible`, then `Poincare.LocalSlope.Intrinsic.constant`.
Log-concavity is tested on compact sets. The energy uses the pointwise local metric slope,
on intrinsic affine coordinates, with no factor of one half. Finite-energy L² tests include
zero-energy functions. Constants are finite `NNReal`; the infimum may be infinite.

These are definitions, not a proof of their equivalence with a different log-concavity,
smooth-gradient, asymptotic-Lipschitz, or Cheeger frontend. In particular, no approximation
theorem is hidden in an admissibility predicate. Interfaces may evolve under the current policy.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.KLS

section LogConcavity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Compact-set log-concavity, including measures on proper affine supports.
The displayed combination of compact sets is compact in finite dimension. -/
def LogConcave (μ : ProbabilityMeasure E) : Prop :=
  ∀ (K₀ K₁ : Set E), IsCompact K₀ → IsCompact K₁ →
    ∀ t : ℝ, 0 < t → t < 1 →
      (μ : Measure E) K₀ ^ t * (μ : Measure E) K₁ ^ (1 - t) ≤
        (μ : Measure E) {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y}

end LogConcavity

end FunctionalInequalities.KLS

import FunctionalInequalities.Probability.AffineSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Definitions of the literature-facing KLS target

Source: Blueprint `def:log-concave-law` and `def:literature-poincare-constant`.
Read `LogConcave`, `localSlope`, `LiteratureAdmissible`, then `literatureConstant`.
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

section Metric

variable {X : Type*} [MetricSpace X]

/-- Pointwise local metric slope as the infimum of punctured-ball secant suprema.
The real quotient at `y = x` is zero, so including the center does not change the supremum.
At an isolated point the slope is zero. This is not the two-moving-point Lipschitz constant. -/
def localSlope (f : X → ℝ) (x : X) : ENNReal :=
  ⨅ (r : ℝ) (_ : 0 < r), ⨆ (y : X) (_ : dist y x < r),
    ENNReal.ofReal (dist (f y) (f x) / dist y x)

@[simp] theorem localSlope_const (c : ℝ) (x : X) :
    localSlope (fun _ : X ↦ c) x = 0 := by
  unfold localSlope
  apply le_antisymm ?_ bot_le
  exact iInf_le_of_le (1 : ℝ) (iInf_le_of_le zero_lt_one (by simp))

/-- The local-slope definition handles a one-point carrier without a nontriviality premise. -/
theorem localSlope_eq_zero_of_subsingleton [Subsingleton X] (f : X → ℝ) (x : X) :
    localSlope f x = 0 := by
  have hf : f = fun _ ↦ f x := funext fun y ↦ congrArg f (Subsingleton.elim y x)
  rw [hf, localSlope_const]

end Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The unnormalized squared local-slope integral in an intrinsic coordinate space. -/
def literatureEnergy (ν : ProbabilityMeasure E) (f : E → ℝ) : ENNReal :=
  ∫⁻ x, localSlope f x ^ 2 ∂(ν : Measure E)

/-- The literature test domain, independent of the candidate Poincaré constant. -/
structure LiteratureAdmissible (ν : ProbabilityMeasure E) (f : E → ℝ) : Prop where
  locallyLipschitz : LocallyLipschitz f
  memLp_two : MemLp f 2 (ν : Measure E)
  finite_energy : literatureEnergy ν f ≠ ⊤

/-- A finite bound on all literature tests in the displayed coordinate space.
The extended variance is finite by `memLp_two`; no real-valued infinite integral is used. -/
def LiteratureHolds (ν : ProbabilityMeasure E) (C : NNReal) : Prop :=
  ∀ f : E → ℝ, LiteratureAdmissible ν f →
    evariance f (ν : Measure E) ≤ (C : ENNReal) * literatureEnergy ν f

/-- The literature optimum of the intrinsic law. Empty sets of finite constants give infinity. -/
def literatureConstant (μ : ProbabilityMeasure E) : ENNReal :=
  ⨅ C : {C : NNReal // LiteratureHolds (Probability.intrinsicMeasure μ) C},
    (C.1 : ENNReal)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- All tests on a zero-dimensional coordinate space have zero variance. -/
theorem literatureHolds_zero_of_subsingleton [Subsingleton E] (ν : ProbabilityMeasure E) :
    LiteratureHolds ν 0 := by
  intro f _
  have hf : f = fun _ ↦ f 0 := funext fun y ↦ congrArg f (Subsingleton.elim y 0)
  rw [hf]
  simp [evariance]

/-- The literature optimum includes the zero-dimensional case with value zero. -/
theorem literatureConstant_eq_zero_of_subsingleton [Subsingleton E] (μ : ProbabilityMeasure E) :
    literatureConstant μ = 0 := by
  apply le_antisymm ?_ bot_le
  exact iInf_le_of_le ⟨0, literatureHolds_zero_of_subsingleton (Probability.intrinsicMeasure μ)⟩
    (by simp)

end FunctionalInequalities.KLS

import FunctionalInequalities.Energy.SmoothGradient.Dirichlet
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `thm:smooth-gradient-relaxation-dirichlet`

For every Borel probability law `μ` on a finite-dimensional real Hilbert space, the ambient
smooth-gradient relaxation `Energy.SmoothGradient.relaxation μ` is Markovian (every normal
contraction of an `L²(μ)` class does not increase its relaxed energy) and, with its closed
quadratic structure, is a Dirichlet energy. The intrinsic-affine relaxation
`Energy.SmoothGradient.Intrinsic.energy μ` on the ambient `L²(μ)` is a Dirichlet energy as well.
No absolute continuity, density or log-concavity is assumed and dimension zero is included.
Nothing here identifies the relaxation with a Cheeger energy, asserts a Poincaré inequality, or
transfers the Markov property to the covariance-weighted relaxations.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.ThmSmoothGradientRelaxationDirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The complete Dirichlet statement of the Blueprint for the smooth-gradient relaxation, together
with its intrinsic-affine counterpart. -/
theorem certificate (μ : ProbabilityMeasure E) :
    Energy.Markovian (μ : Measure E) (Energy.SmoothGradient.relaxation μ) ∧
    Energy.Dirichlet (μ : Measure E) (Energy.SmoothGradient.relaxation μ) ∧
    Energy.Dirichlet (μ : Measure E) (Energy.SmoothGradient.Intrinsic.energy μ) :=
  ⟨Energy.SmoothGradient.markovian μ, Energy.SmoothGradient.dirichlet μ,
    Energy.SmoothGradient.Intrinsic.dirichlet μ⟩

/-- Typed application on the Euclidean family of the KLS statement, in every dimension: the
contraction inequality for every normal contraction and every `L²` class. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (φ : Energy.NormalContraction) (f : Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    Energy.SmoothGradient.relaxation μ (φ.compL2 (μ : Measure (EuclideanSpace ℝ (Fin n))) f) ≤
      Energy.SmoothGradient.relaxation μ f :=
  (certificate μ).1 φ f

/-- Dimension zero: the relaxation is still a Dirichlet energy, and so is the intrinsic one. -/
example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    Energy.Dirichlet (μ : Measure (EuclideanSpace ℝ (Fin 0))) (Energy.SmoothGradient.relaxation μ) ∧
      Energy.Dirichlet (μ : Measure (EuclideanSpace ℝ (Fin 0)))
        (Energy.SmoothGradient.Intrinsic.energy μ) :=
  ⟨(certificate μ).2.1, (certificate μ).2.2⟩

/-- A singular example: the Dirac law at the origin of the real line. -/
example : Energy.Dirichlet (Measure.dirac (0 : ℝ))
    (Energy.SmoothGradient.relaxation (Probability.ofMeasure (Measure.dirac (0 : ℝ)))) :=
  (certificate (Probability.ofMeasure (Measure.dirac (0 : ℝ)))).2.1

end Solutions.ThmSmoothGradientRelaxationDirichlet

/--
info: 'Solutions.ThmSmoothGradientRelaxationDirichlet.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmSmoothGradientRelaxationDirichlet.certificate

/--
info: 'FunctionalInequalities.Energy.NormalContraction.contDiff_smoothed'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.NormalContraction.contDiff_smoothed

/--
info: 'FunctionalInequalities.Energy.NormalContraction.lipschitzWith_smoothed'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.NormalContraction.lipschitzWith_smoothed

/--
info: 'FunctionalInequalities.Energy.NormalContraction.norm_smoothed_sub_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.NormalContraction.norm_smoothed_sub_le

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Test.energy_compSmoothed_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.energy_compSmoothed_le

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Test.norm_toL2_compSmoothed_sub_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.norm_toL2_compSmoothed_sub_le

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.relaxedContractionBound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.relaxedContractionBound

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.markovian'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.markovian

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.dirichlet'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.dirichlet

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Intrinsic.toIntrinsicL2_compL2'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Intrinsic.toIntrinsicL2_compL2

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Intrinsic.markovian'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Intrinsic.markovian

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Intrinsic.dirichlet'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Intrinsic.dirichlet

import FunctionalInequalities.Energy.SmoothGradient.Core
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `thm:smooth-gradient-raw-core-agreement-density`

For a probability law `ν` on a finite-dimensional real inner-product space with a local density
(`Energy.SmoothGradient.LocalDensity ν m`: an open set `Ω` carrying `ν` on which `ν` has an
`m`-density `ρ` for a Haar measure `m`, positive almost everywhere with locally essentially bounded
reciprocal), the smooth-gradient pre-energy agrees on every smooth test with its sequential
relaxation (`AgreesOnTests`) and is therefore a sequential form core (`IsSequentialCoreFor`). The
intrinsic law of a law `μ` on the affine support direction is the case named by the Blueprint. No
statement is made without a local density, and no Cheeger-energy identification is asserted.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.ThmSmoothGradientRawCoreAgreementDensity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The complete statement of the Blueprint for every law with a local density: agreement on
tests and the sequential-core property of the smooth-gradient pre-energy. -/
theorem certificate (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]
    (D : Energy.SmoothGradient.LocalDensity ν m) :
    (Energy.SmoothGradient.preEnergy ν).AgreesOnTests (Energy.SmoothGradient.relaxation ν) ∧
    (Energy.SmoothGradient.preEnergy ν).IsSequentialCoreFor (Energy.SmoothGradient.relaxation ν) :=
  ⟨Energy.SmoothGradient.preEnergy_agreesOnTests ν m D,
    Energy.SmoothGradient.preEnergy_isSequentialCoreFor ν m D⟩

/-- The intrinsic form named by the Blueprint: the intrinsic law of `μ` on the direction of its
affine support. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
    [m.IsAddHaarMeasure] (D : Energy.SmoothGradient.LocalDensity (Probability.intrinsicMeasure μ) m) :
    (Energy.SmoothGradient.preEnergy (Probability.intrinsicMeasure μ)).IsSequentialCoreFor
      (Energy.SmoothGradient.relaxation (Probability.intrinsicMeasure μ)) :=
  (certificate _ m D).2

/-- Typed application on the Euclidean family: the relaxed energy of the class of a smooth test is
its raw energy. -/
example (n : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (m : Measure (EuclideanSpace ℝ (Fin n))) [m.IsAddHaarMeasure]
    (D : Energy.SmoothGradient.LocalDensity ν m) (f : Energy.SmoothGradient.Test ν) :
    Energy.SmoothGradient.relaxation ν f.toL2 = (f.energy : ENNReal) :=
  (certificate ν m D).1 f

/-- Agreement forces the pre-energy to respect realization fibers: two smooth tests with the same
`L²` class have the same raw energy. -/
example (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]
    (D : Energy.SmoothGradient.LocalDensity ν m) (f g : Energy.SmoothGradient.Test ν)
    (h : f.toL2 = g.toL2) : f.energy = g.energy :=
  Energy.PreEnergy.AgreesOnTests.respectsAmbientFibers (Energy.SmoothGradient.preEnergy ν)
    (certificate ν m D).1 f g h

end Solutions.ThmSmoothGradientRawCoreAgreementDensity

/--
info: 'Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate

/--
info: 'FunctionalInequalities.Energy.WeightedGradient.operator_isClosable_of_isOpen'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.WeightedGradient.operator_isClosable_of_isOpen

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.LocalDensity.absolutelyContinuous'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.LocalDensity.absolutelyContinuous

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.LocalDensity.frontier_support_null'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.LocalDensity.frontier_support_null

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.LocalDensity.locallyDominatesOn'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.LocalDensity.locallyDominatesOn

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator_isClosable'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator_isClosable

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Test.toL2_mem_closure_domain'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.toL2_mem_closure_domain

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.lipschitzRelaxation_le_relaxation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.lipschitzRelaxation_le_relaxation

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.preEnergy_agreesOnTests'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.preEnergy_agreesOnTests

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.preEnergy_isSequentialCoreFor'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.preEnergy_isSequentialCoreFor

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Intrinsic.preEnergy_isSequentialCoreFor'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Intrinsic.preEnergy_isSequentialCoreFor

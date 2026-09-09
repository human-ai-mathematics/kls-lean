import FunctionalInequalities.Poincare.Foundation
import FunctionalInequalities.Poincare.Euclidean.RawEnergyObstruction

/-!
# Transitive axiom audit for the Poincaré foundation

These guards cover approximation, recovery, closed quadratic structure, intrinsic coordinates,
and the selected optimal-constant interface. They complement the six node certificates and
the Gaussian audit; this file does not introduce another mathematical certificate or ledger node.

Each audited declaration must use only the standard propositional-extensionality, classical-choice
and quotient axioms. A new dependency on an unproved declaration makes the default build fail.
-/

/--
info: 'FunctionalInequalities.Energy.PreEnergy.lowerSemicontinuous_sequentialRelaxation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.lowerSemicontinuous_sequentialRelaxation

/--
info: 'FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt

/--
info: 'FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation

/--
info: 'FunctionalInequalities.Energy.PreEnergy.Quadratic.closedQuadratic_sequentialRelaxation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.Quadratic.closedQuadratic_sequentialRelaxation

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.relaxation_closedQuadratic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.relaxation_closedQuadratic

/--
info: 'FunctionalInequalities.Energy.Euclidean.intrinsicL2Equiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.intrinsicL2Equiv

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Intrinsic.closedQuadratic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Intrinsic.closedQuadratic

/--
info: 'FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.holds_iff_constant_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.holds_iff_constant_le

/--
info: 'FunctionalInequalities.L2.continuous_variance'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.L2.continuous_variance

/--
info: 'FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le

/--
info: 'FunctionalInequalities.Poincare.TestFamily.holds_ofPreEnergy_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.TestFamily.holds_ofPreEnergy_iff

/--
info: 'FunctionalInequalities.Poincare.TestFamily.constant_ofPreEnergy_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.TestFamily.constant_ofPreEnergy_eq

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Test.exists_intrinsic_restriction'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.exists_intrinsic_restriction

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy

/--
info: 'FunctionalInequalities.Poincare.SmoothGradient.Ambient.holds_iff_intrinsic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.SmoothGradient.Ambient.holds_iff_intrinsic

/--
info: 'FunctionalInequalities.Poincare.SmoothGradient.Ambient.constant_eq_intrinsic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.SmoothGradient.Ambient.constant_eq_intrinsic

/--
info: 'FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy

/--
info: 'FunctionalInequalities.Poincare.SmoothTest.holds_iff_ambient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.SmoothTest.holds_iff_ambient

/--
info: 'FunctionalInequalities.Poincare.SmoothTest.constant_eq_ambient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.SmoothTest.constant_eq_ambient

/--
info: 'FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsic

/--
info: 'FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsic

/--
info: 'FunctionalInequalities.Energy.PreEnergy.le_sequentialRelaxation_of_lowerSemicontinuous'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.le_sequentialRelaxation_of_lowerSemicontinuous

/--
info: 'FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_of_recovery_sequences'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_of_recovery_sequences

/--
info: 'FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_eq_of_recovery_sequences'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_eq_of_recovery_sequences

/--
info: 'FunctionalInequalities.Poincare.L2Energy.Holds.of_energy_le_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.L2Energy.Holds.of_energy_le_mul

/--
info: 'FunctionalInequalities.Poincare.L2Energy.constant_le_mul_of_energy_le_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.L2Energy.constant_le_mul_of_energy_le_mul

/-- info: 'FunctionalInequalities.Poincare.Euclidean.dirac_raw_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.dirac_raw_energy

/-- info: 'FunctionalInequalities.Poincare.Euclidean.dirac_toLp_zero_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.dirac_toLp_zero_eq_id

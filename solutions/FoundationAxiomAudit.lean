import FunctionalInequalities.Poincare.Foundation

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
info: 'FunctionalInequalities.Energy.Euclidean.smoothGradientRelaxation_closedQuadratic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.smoothGradientRelaxation_closedQuadratic

/--
info: 'FunctionalInequalities.Energy.Euclidean.intrinsicL2Equiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.intrinsicL2Equiv

/--
info: 'FunctionalInequalities.Energy.Canonical.closedQuadratic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Canonical.closedQuadratic

/--
info: 'FunctionalInequalities.Poincare.Canonical.holds_iff_constant_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Canonical.holds_iff_constant_le

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
info: 'FunctionalInequalities.Energy.Euclidean.SmoothGradientTest.exists_intrinsic_restriction'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.SmoothGradientTest.exists_intrinsic_restriction

/--
info: 'FunctionalInequalities.Energy.Euclidean.SmoothGradientTest.exists_ambient_extension'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.SmoothGradientTest.exists_ambient_extension

/--
info: 'FunctionalInequalities.Energy.Euclidean.smoothGradientRelaxation_eq_canonical'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.smoothGradientRelaxation_eq_canonical

/--
info: 'FunctionalInequalities.Poincare.Ambient.holds_iff_canonical'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Ambient.holds_iff_canonical

/--
info: 'FunctionalInequalities.Poincare.Ambient.constant_eq_canonical'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Ambient.constant_eq_canonical

/--
info: 'FunctionalInequalities.Poincare.Euclidean.holds_iff_preEnergy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.holds_iff_preEnergy

/--
info: 'FunctionalInequalities.Poincare.Euclidean.holds_iff_ambient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.holds_iff_ambient

/--
info: 'FunctionalInequalities.Poincare.Euclidean.constant_eq_ambient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.constant_eq_ambient

/--
info: 'FunctionalInequalities.Poincare.Euclidean.holds_iff_canonical'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.holds_iff_canonical

/--
info: 'FunctionalInequalities.Poincare.Euclidean.constant_eq_canonical'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.constant_eq_canonical

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

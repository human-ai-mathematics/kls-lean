import FunctionalInequalities.KLS.LogConcaveDensity

/-!
# Lean certificate: `lem:logconcave-intrinsic-absolute-continuity`

The compact-set definition implies intrinsic absolute continuity for arbitrary finite-dimensional
log-concave probability laws. This certifies the precise input needed by the selected/literature
comparison; the full Borell density-representative and moment theorem remains separate.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.LemLogConcaveIntrinsicAbsoluteContinuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- Absolute continuity on the direction of the affine support, for any additive Haar reference. -/
theorem certificate (μ : ProbabilityMeasure E) (hμ : KLS.LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure] :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m :=
  hμ.intrinsic_absolutelyContinuous m

end Solutions.LemLogConcaveIntrinsicAbsoluteContinuity

/--
info: 'Solutions.LemLogConcaveIntrinsicAbsoluteContinuity.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemLogConcaveIntrinsicAbsoluteContinuity.certificate

/--
info: 'FunctionalInequalities.Probability.affineSupport_intrinsicMeasure'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.affineSupport_intrinsicMeasure

/--
info: 'FunctionalInequalities.KLS.LogConcave.of_affineIsometry_map'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.of_affineIsometry_map

/--
info: 'FunctionalInequalities.KLS.LogConcave.closedBall_mul_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.closedBall_mul_le

/--
info: 'FunctionalInequalities.KLS.LogConcave.convex_support'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.convex_support

/--
info: 'FunctionalInequalities.KLS.LogConcave.convex_closedBall_superlevel'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.convex_closedBall_superlevel

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsicMeasure'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicMeasure

/--
info: 'FunctionalInequalities.KLS.LogConcave.interior_intrinsic_support_nonempty'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.interior_intrinsic_support_nonempty

/--
info: 'FunctionalInequalities.KLS.LogConcave.haar_frontier_intrinsic_support'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.haar_frontier_intrinsic_support

/--
info: 'FunctionalInequalities.KLS.LogConcave.exists_eventually_closedBall_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.exists_eventually_closedBall_le

/--
info: 'FunctionalInequalities.KLS.LogConcave.absolutelyContinuous_of_interior_support_nonempty'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.absolutelyContinuous_of_interior_support_nonempty

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsic_frontier_support'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsic_frontier_support

/--
info: 'FunctionalInequalities.Probability.exists_pos_le_measure_ball_on_isCompact'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.exists_pos_le_measure_ball_on_isCompact

/--
info: 'FunctionalInequalities.Probability.lintegral_measure_closedBall'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.lintegral_measure_closedBall

/--
info: 'FunctionalInequalities.Probability.lintegral_measure_closedBall_swap'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.lintegral_measure_closedBall_swap

/--
info: 'FunctionalInequalities.Probability.measure_ball_mul_closedBall_le_lintegral'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.measure_ball_mul_closedBall_le_lintegral

/--
info: 'FunctionalInequalities.Probability.measure_le_smul_of_eventually_closedBall_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.measure_le_smul_of_eventually_closedBall_le

/--
info: 'FunctionalInequalities.Probability.absolutelyContinuous_of_eventually_closedBall_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.absolutelyContinuous_of_eventually_closedBall_le

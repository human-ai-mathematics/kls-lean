import FunctionalInequalities.Probability.IntrinsicCovariance
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `lem:ambient-intrinsic-covariance`

For a Borel probability law with finite second moment on a finite-dimensional Euclidean space,
the ambient covariance operator annihilates the orthogonal complement of the direction of the
affine support, restricts on that direction to the covariance operator of the intrinsic law, has
the same operator norm, and the intrinsic covariance is positive definite; a zero-dimensional
direction gives zero operators. No log-concavity, density, Poincaré or whitening statement is
packaged here.
-/

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.Probability

namespace Solutions.LemAmbientIntrinsicCovariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The complete ambient/intrinsic covariance comparison from the Blueprint. -/
theorem certificate (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E)) :
    (∀ w ∈ (affineSupport μ).directionᗮ, Covariance.operator (μ : Measure E) w = 0) ∧
    (∀ v : (affineSupport μ).direction, Covariance.operator (μ : Measure E) v =
      (Covariance.operator (intrinsicMeasure μ).toMeasure v : E)) ∧
    ‖Covariance.operator (intrinsicMeasure μ).toMeasure‖ = ‖Covariance.operator (μ : Measure E)‖ ∧
    (∀ v : (affineSupport μ).direction, v ≠ 0 →
      0 < inner ℝ (Covariance.operator (intrinsicMeasure μ).toMeasure v) v) ∧
    ((affineSupport μ).direction = ⊥ →
      Covariance.operator (μ : Measure E) = 0 ∧
        Covariance.operator (intrinsicMeasure μ).toMeasure = 0) := by
  refine ⟨fun _ hw ↦ Covariance.operator_apply_eq_zero_of_mem_orthogonal μ hμ hw,
    Covariance.operator_coe_intrinsic μ hμ, Covariance.opNorm_operator_intrinsic μ hμ,
    fun _ hv ↦ Covariance.intrinsic_operator_inner_self_pos μ hμ hv, fun h ↦
    ⟨Covariance.operator_eq_zero_of_direction_eq_bot μ hμ h, ?_⟩⟩
  ext v
  have hv : (v : E) = 0 := (Submodule.eq_bot_iff _).mp h v v.property
  have hv0 : v = 0 := Subtype.ext hv
  simp [hv0]

/-- Typed applications cover the exact Euclidean family of the KLS statement. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖Covariance.operator (intrinsicMeasure μ).toMeasure‖ =
      ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖ :=
  (certificate μ hμ).2.2.1

/-- Dimension zero: the ambient covariance vanishes. -/
example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)))
    (hμ : MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin 0)))) :
    Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin 0))) = 0 :=
  ((certificate μ hμ).2.2.2.2 (Subsingleton.elim _ _)).1

end Solutions.LemAmbientIntrinsicCovariance

/--
info: 'Solutions.LemAmbientIntrinsicCovariance.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemAmbientIntrinsicCovariance.certificate

/--
info: 'FunctionalInequalities.Covariance.operator_apply_eq_zero_of_mem_orthogonal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.operator_apply_eq_zero_of_mem_orthogonal

/--
info: 'FunctionalInequalities.Covariance.covarianceBilin_intrinsic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.covarianceBilin_intrinsic

/--
info: 'FunctionalInequalities.Covariance.operator_coe_intrinsic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.operator_coe_intrinsic

/--
info: 'FunctionalInequalities.Covariance.opNorm_operator_intrinsic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.opNorm_operator_intrinsic

/--
info: 'FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos

/--
info: 'FunctionalInequalities.Covariance.operator_eq_zero_of_direction_eq_bot'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.operator_eq_zero_of_direction_eq_bot

/--
info: 'FunctionalInequalities.Probability.intrinsicMap_ae_eq_orthogonalProjection'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.intrinsicMap_ae_eq_orthogonalProjection

/--
info: 'FunctionalInequalities.Probability.integral_id_mem_affineSupport'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.integral_id_mem_affineSupport

/--
info: 'FunctionalInequalities.Probability.memLp_id_two_intrinsicMeasure'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.memLp_id_two_intrinsicMeasure

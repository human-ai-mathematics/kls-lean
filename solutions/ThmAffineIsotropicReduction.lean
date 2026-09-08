import FunctionalInequalities.KLS.LogConcave.IsotropicReduction
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `thm:affine-isotropic-reduction`

For a fixed finite `K ≥ 0` and a fixed universe, the three KLS formulations are equivalent:
`KLS.IsotropicBound K` (every isotropic log-concave law `ν` has `C_P^lit(ν) ≤ K`),
`KLS.CovarianceBound K` (every log-concave law `μ` has `C_P^lit(μ) ≤ K ‖Cov_μ‖`) and
`KLS.AffineBound K` (every log-concave law `μ` has `C_P^aff(μ) ≤ K`), each quantified over every
finite-dimensional Euclidean space of the universe. Moreover the affine formulation for some finite
`K` on the Euclidean family implies the literal KLS proposition `KLS.Conjecture`. The
zero-dimensional law is included in all three statements. Nothing here asserts that any of the
three statements holds for some `K`.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.ThmAffineIsotropicReduction

universe u

/-- The complete equivalence of the Blueprint, with the specialization to the KLS proposition. -/
theorem certificate (K : NNReal) :
    (KLS.IsotropicBound.{u} K ↔ KLS.CovarianceBound.{u} K) ∧
    (KLS.CovarianceBound.{u} K ↔ KLS.AffineBound.{u} K) ∧
    (KLS.IsotropicBound.{u} K ↔ KLS.AffineBound.{u} K) ∧
    (KLS.AffineBound.{0} K → KLS.Conjecture) :=
  ⟨(KLS.affine_isotropic_reduction K).1, (KLS.affine_isotropic_reduction K).2,
    (KLS.affine_isotropic_reduction K).1.trans (KLS.affine_isotropic_reduction K).2,
    KLS.conjecture_of_affineBound⟩

/-- Typed application on the Euclidean family of the KLS statement: the affine bound gives the
covariance-normalized literature bound in every dimension. -/
example (K : NNReal) (h : KLS.AffineBound.{0} K) (n : ℕ)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : KLS.LogConcave μ) :
    KLS.literatureConstant μ ≤
      (K : ENNReal) * ENNReal.ofReal ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖ :=
  ((certificate K).2.1.mpr h) (EuclideanSpace ℝ (Fin n)) μ hμ

/-- Dimension zero: both constants vanish, so every `K` bounds them. -/
example (K : NNReal) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    Poincare.Affine.constant μ ≤ (K : ENNReal) ∧ KLS.literatureConstant μ ≤ (K : ENNReal) := by
  rw [Poincare.Affine.constant_eq_zero_of_subsingleton μ, KLS.literatureConstant_eq_zero_of_subsingleton μ]
  exact ⟨zero_le, zero_le⟩

end Solutions.ThmAffineIsotropicReduction

/--
info: 'Solutions.ThmAffineIsotropicReduction.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmAffineIsotropicReduction.certificate

/--
info: 'FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul

/--
info: 'FunctionalInequalities.Energy.Euclidean.gradient_comp_continuousLinearEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.gradient_comp_continuousLinearEquiv

/--
info: 'FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv

/--
info: 'FunctionalInequalities.Energy.Euclidean.covarianceRelaxation_mapEquivLaw'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.covarianceRelaxation_mapEquivLaw

/--
info: 'FunctionalInequalities.Poincare.L2Energy.constant_covarianceRelaxation_mapEquivLaw'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.L2Energy.constant_covarianceRelaxation_mapEquivLaw

/--
info: 'FunctionalInequalities.exists_whitening_of_isSymmetric'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.exists_whitening_of_isSymmetric

/--
info: 'FunctionalInequalities.Covariance.exists_whitening'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.exists_whitening

/--
info: 'FunctionalInequalities.Poincare.L2Energy.holds_lipschitzGradientRelaxation_iff_literatureHolds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.L2Energy.holds_lipschitzGradientRelaxation_iff_literatureHolds

/--
info: 'FunctionalInequalities.Poincare.constant_eq_lipschitzGradientRelaxation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.constant_eq_lipschitzGradientRelaxation

/--
info: 'FunctionalInequalities.Energy.Euclidean.covarianceRelaxation_le_opNorm_mul_lipschitzGradientRelaxation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.covarianceRelaxation_le_opNorm_mul_lipschitzGradientRelaxation

/--
info: 'FunctionalInequalities.KLS.LogConcave.of_continuousLinearEquiv_map'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.of_continuousLinearEquiv_map

/--
info: 'FunctionalInequalities.KLS.LogConcave.exists_isotropic_literatureConstant_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.exists_isotropic_literatureConstant_eq

/--
info: 'FunctionalInequalities.KLS.LogConcave.literatureConstant_le_opNorm_mul_affine_constant'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.literatureConstant_le_opNorm_mul_affine_constant

/--
info: 'FunctionalInequalities.KLS.affine_isotropic_reduction'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.affine_isotropic_reduction

/--
info: 'FunctionalInequalities.KLS.conjecture_of_affineBound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.conjecture_of_affineBound

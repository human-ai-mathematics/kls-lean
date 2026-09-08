import FunctionalInequalities.KLS.LogConcave.AffineClosedForm
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `thm:affine-covariance-relaxation-closed`

For every compact-set log-concave law `μ` on a finite-dimensional Euclidean space, with intrinsic
law `ν` on the direction space `V` of its affine support: the affine covariance pre-energy of
`def:affine-poincare-constant` has dense realization in `L²(ν)`; its sequential relaxation
`Energy.Affine.energy μ` is a closed quadratic form; the globally Lipschitz tests form a sequential
core, so the relaxation agrees with the raw covariance energy on every test; translating `ν` by any
`c ∈ V` leaves the covariance operator unchanged, gives an `L²` isometry preserving variance under
which the relaxation is pulled back, and leaves the optimal constant unchanged; and for a square
root `B` of the intrinsic covariance (`⟪Σ v, v⟫ = ‖B v‖²`) the weighted gradient `B ∇` is closable,
the affine relaxation equals the squared-norm energy of the closure of `B ∇` restricted to the core
`ℝ + C_c^∞(V)` of the pinned CMH source, and `Poincare.Affine.constant μ` is the optimal constant
of that closed form. Dimension zero is included. No Poincaré inequality, ambient translation
invariance of the affine constant, isotropic reduction or KLS statement is packaged here.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.ThmAffineCovarianceRelaxationClosed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The complete closed-form statement of the Blueprint for the affine covariance relaxation. -/
theorem certificate (μ : ProbabilityMeasure E) (hμ : KLS.LogConcave μ) :
    (Energy.Euclidean.covariancePreEnergy (Probability.intrinsicMeasure μ)).DenseRealization ∧
    Energy.ClosedQuadratic (Energy.Affine.energy μ) ∧
    (Energy.Euclidean.covariancePreEnergy (Probability.intrinsicMeasure μ)).IsSequentialCoreFor
      (Energy.Affine.energy μ) ∧
    (∀ c : (Probability.affineSupport μ).direction,
      Covariance.operator (Energy.Euclidean.translateLaw (Probability.intrinsicMeasure μ) c :
          Measure (Probability.affineSupport μ).direction) =
        Covariance.operator (Probability.intrinsicMeasure μ :
          Measure (Probability.affineSupport μ).direction) ∧
      (∀ f : Lp ℝ 2 (Energy.Euclidean.translateLaw (Probability.intrinsicMeasure μ) c :
          Measure (Probability.affineSupport μ).direction),
        L2.variance (Probability.intrinsicMeasure μ)
            (Energy.Euclidean.translateL2 (Probability.intrinsicMeasure μ) c f) =
          L2.variance (Energy.Euclidean.translateLaw (Probability.intrinsicMeasure μ) c) f) ∧
      (∀ f : Lp ℝ 2 (Energy.Euclidean.translateLaw (Probability.intrinsicMeasure μ) c :
          Measure (Probability.affineSupport μ).direction),
        Energy.Euclidean.covarianceRelaxation
            (Energy.Euclidean.translateLaw (Probability.intrinsicMeasure μ) c) f =
          Energy.Affine.energy μ (Energy.Euclidean.translateL2 (Probability.intrinsicMeasure μ) c f)) ∧
      Poincare.Affine.constant μ =
        Poincare.L2Energy.constant (Energy.Euclidean.translateLaw (Probability.intrinsicMeasure μ) c)
          (Energy.Euclidean.covarianceRelaxation
            (Energy.Euclidean.translateLaw (Probability.intrinsicMeasure μ) c))) ∧
    (∃ B : (Probability.affineSupport μ).direction →L[ℝ] (Probability.affineSupport μ).direction,
      (∀ v, inner ℝ (Covariance.operator (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction) v) v = ‖B v‖ ^ 2) ∧
      (hμ.intrinsicGradientOperator Measure.addHaar B).IsClosable ∧
      Energy.Affine.energy μ =
        Energy.PreEnergy.normSqEnergy ((hμ.intrinsicGradientOperator Measure.addHaar B).domRestrict
          (Energy.Euclidean.constantSmoothCore (Probability.intrinsicMeasure μ))).closure ∧
      Poincare.Affine.constant μ =
        Poincare.L2Energy.constant (Probability.intrinsicMeasure μ)
          (Energy.PreEnergy.normSqEnergy ((hμ.intrinsicGradientOperator Measure.addHaar B).domRestrict
            (Energy.Euclidean.constantSmoothCore (Probability.intrinsicMeasure μ))).closure)) := by
  obtain ⟨B, hB⟩ := KLS.exists_intrinsic_covariance_sqrt μ
  refine ⟨hμ.affine_denseRealization, hμ.affine_closedQuadratic, hμ.affine_isSequentialCoreFor,
    fun c ↦ ⟨Covariance.operator_translateLaw _ c, L2.variance_translateL2 _ c,
      Energy.Affine.energy_translateLaw μ c, Poincare.Affine.constant_translateLaw μ c⟩,
    B, hB, hμ.intrinsicGradientOperator_isClosable Measure.addHaar B,
    hμ.affine_energy_eq_normSqEnergy Measure.addHaar B hB,
    hμ.affine_constant_eq_normSqEnergy Measure.addHaar B hB⟩

/-- Typed application on the Euclidean family of the KLS statement, in every dimension. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : KLS.LogConcave μ) :
    Energy.ClosedQuadratic (Energy.Affine.energy μ) ∧
      (Energy.Euclidean.covariancePreEnergy (Probability.intrinsicMeasure μ)).AgreesOnTests
        (Energy.Affine.energy μ) :=
  ⟨(certificate μ hμ).2.1, (certificate μ hμ).2.2.1.agreesOnTests⟩

/-- Dimension zero: the affine constant is zero and the closed form is still a closed quadratic
form on the intrinsic `L²` space. -/
example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) (hμ : KLS.LogConcave μ) :
    Poincare.Affine.constant μ = 0 ∧ Energy.ClosedQuadratic (Energy.Affine.energy μ) :=
  ⟨Poincare.Affine.constant_eq_zero_of_subsingleton μ, (certificate μ hμ).2.1⟩

end Solutions.ThmAffineCovarianceRelaxationClosed

/--
info: 'Solutions.ThmAffineCovarianceRelaxationClosed.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmAffineCovarianceRelaxationClosed.certificate

/--
info: 'FunctionalInequalities.exists_norm_sq_eq_inner_of_isSymmetric'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.exists_norm_sq_eq_inner_of_isSymmetric

/--
info: 'FunctionalInequalities.Covariance.exists_sqrt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.exists_sqrt

/--
info: 'FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy

/--
info: 'FunctionalInequalities.Energy.Euclidean.covarianceRelaxation_translateLaw'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.covarianceRelaxation_translateLaw

/--
info: 'FunctionalInequalities.L2.variance_translateL2'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.L2.variance_translateL2

/--
info: 'FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv

/--
info: 'FunctionalInequalities.KLS.LogConcave.affine_closedQuadratic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.affine_closedQuadratic

/--
info: 'FunctionalInequalities.KLS.LogConcave.affine_agreesOnTests'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.affine_agreesOnTests

/--
info: 'FunctionalInequalities.KLS.LogConcave.affine_energy_eq_normSqEnergy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.affine_energy_eq_normSqEnergy

/--
info: 'FunctionalInequalities.KLS.LogConcave.affine_constant_eq_normSqEnergy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.affine_constant_eq_normSqEnergy

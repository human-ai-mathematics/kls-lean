import FunctionalInequalities.KLS.LogConcave.ClosedForm
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `thm:affine-covariance-relaxation-closed`

For every compact-set log-concave law `μ` on a finite-dimensional Euclidean space, with intrinsic
law `ν` on the direction space `V` of its affine support: the affine covariance pre-energy of
`def:affine-poincare-constant` has dense realization in `L²(ν)`; its sequential relaxation
`Energy.CovarianceGradient.Intrinsic.energy μ` is a closed quadratic form; the globally Lipschitz tests form a sequential
core, so the relaxation agrees with the raw covariance energy on every test; translating `ν` by any
`c ∈ V` leaves the covariance operator unchanged, gives an `L²` isometry preserving variance under
which the relaxation is pulled back, and leaves the optimal constant unchanged; and for a square
root `B` of the intrinsic covariance (`⟪Σ v, v⟫ = ‖B v‖²`) the weighted gradient `B ∇` is closable,
the affine relaxation equals the squared-norm energy of the closure of `B ∇` restricted to the core
`ℝ + C_c^∞(V)` of the pinned CMH source, and `Poincare.CovarianceGradient.Intrinsic.constant μ` is the optimal constant
of that closed form. Dimension zero is included. No Poincaré inequality, ambient translation
invariance of the affine constant, isotropic reduction or KLS statement is packaged here.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.ThmAffineCovarianceRelaxationClosed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- The complete closed-form statement of the Blueprint for the affine covariance relaxation. -/
theorem certificate (μ : ProbabilityMeasure E) (hμ : KLS.LogConcave μ) :
    (FunctionalInequalities.Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)).DenseRealization ∧
    Energy.ClosedQuadratic (FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy μ) ∧
    (FunctionalInequalities.Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)).IsSequentialCoreFor
      (FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy μ) ∧
    (∀ c : (Probability.affineSupport μ).direction,
      Covariance.operator (FunctionalInequalities.Probability.translateLaw (Probability.intrinsicMeasure μ) c :
          Measure (Probability.affineSupport μ).direction) =
        Covariance.operator (Probability.intrinsicMeasure μ :
          Measure (Probability.affineSupport μ).direction) ∧
      (∀ f : Lp ℝ 2 (FunctionalInequalities.Probability.translateLaw (Probability.intrinsicMeasure μ) c :
          Measure (Probability.affineSupport μ).direction),
        L2.variance (Probability.intrinsicMeasure μ)
            (FunctionalInequalities.L2.Translation.pullbackEquiv (Probability.intrinsicMeasure μ) c f) =
          L2.variance (FunctionalInequalities.Probability.translateLaw (Probability.intrinsicMeasure μ) c) f) ∧
      (∀ f : Lp ℝ 2 (FunctionalInequalities.Probability.translateLaw (Probability.intrinsicMeasure μ) c :
          Measure (Probability.affineSupport μ).direction),
        FunctionalInequalities.Energy.CovarianceGradient.relaxation
            (FunctionalInequalities.Probability.translateLaw (Probability.intrinsicMeasure μ) c) f =
          FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy μ (FunctionalInequalities.L2.Translation.pullbackEquiv (Probability.intrinsicMeasure μ) c f)) ∧
      FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ =
        Poincare.L2Energy.constant (FunctionalInequalities.Probability.translateLaw (Probability.intrinsicMeasure μ) c)
          (FunctionalInequalities.Energy.CovarianceGradient.relaxation
            (FunctionalInequalities.Probability.translateLaw (Probability.intrinsicMeasure μ) c))) ∧
    (∃ B : (Probability.affineSupport μ).direction →L[ℝ] (Probability.affineSupport μ).direction,
      (∀ v, inner ℝ (Covariance.operator (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction) v) v = ‖B v‖ ^ 2) ∧
      (hμ.intrinsicWeightedOperator Measure.addHaar B).IsClosable ∧
      FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy μ =
        Energy.PreEnergy.normSqEnergy ((hμ.intrinsicWeightedOperator Measure.addHaar B).domRestrict
          (FunctionalInequalities.Energy.WeightedGradient.constantSmoothCore (Probability.intrinsicMeasure μ))).closure ∧
      FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ =
        Poincare.L2Energy.constant (Probability.intrinsicMeasure μ)
          (Energy.PreEnergy.normSqEnergy ((hμ.intrinsicWeightedOperator Measure.addHaar B).domRestrict
            (FunctionalInequalities.Energy.WeightedGradient.constantSmoothCore (Probability.intrinsicMeasure μ))).closure)) := by
  obtain ⟨B, hB⟩ := FunctionalInequalities.Covariance.exists_intrinsic_inner_eq_norm_sq μ
  refine ⟨hμ.intrinsicCovariance_denseRealization, hμ.intrinsicCovariance_closedQuadratic, hμ.intrinsicCovariance_isSequentialCoreFor,
    fun c ↦ ⟨Covariance.operator_translateLaw _ c, FunctionalInequalities.L2.Translation.variance_pullbackEquiv _ c,
      FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.relaxation_translate_intrinsicMeasure μ c, FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq_translate_intrinsicMeasure μ c⟩,
    B, hB, hμ.intrinsicWeightedOperator_isClosable Measure.addHaar B,
    hμ.intrinsicCovariance_energy_eq_normSq Measure.addHaar B hB,
    hμ.intrinsicCovariance_constant_eq_normSq Measure.addHaar B hB⟩

/-- Typed application on the Euclidean family of the KLS statement, in every dimension. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : KLS.LogConcave μ) :
    Energy.ClosedQuadratic (FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy μ) ∧
      (FunctionalInequalities.Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)).AgreesOnTests
        (FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy μ) :=
  ⟨(certificate μ hμ).2.1, (certificate μ hμ).2.2.1.agreesOnTests⟩

/-- Dimension zero: the affine constant is zero and the closed form is still a closed quadratic
form on the intrinsic `L²` space. -/
example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) (hμ : KLS.LogConcave μ) :
    FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ = 0 ∧ Energy.ClosedQuadratic (FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy μ) :=
  ⟨FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq_zero_of_subsingleton μ, (certificate μ hμ).2.1⟩

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
info: 'FunctionalInequalities.Covariance.exists_inner_eq_norm_sq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.exists_inner_eq_norm_sq

/--
info: 'FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy

/--
info: 'FunctionalInequalities.Energy.CovarianceGradient.relaxation_translateLaw'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.CovarianceGradient.relaxation_translateLaw

/--
info: 'FunctionalInequalities.L2.Translation.variance_pullbackEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.L2.Translation.variance_pullbackEquiv

/--
info: 'FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_closedQuadratic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_closedQuadratic

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_agreesOnTests'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_agreesOnTests

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_energy_eq_normSq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_energy_eq_normSq

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_constant_eq_normSq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_constant_eq_normSq

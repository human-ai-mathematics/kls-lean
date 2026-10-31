module

public import FunctionalInequalities.KLS.LogConcave.Translation
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `lem:affine-poincare-translation-invariance`

For every compact-set log-concave law `μ` on a finite-dimensional Euclidean space `E` and every
`b ∈ E`, with `τ_b(x) = b + x` and `(τ_b)_# μ = Probability.translateLaw μ b`: the translated
law is log-concave; its ambient covariance operator is that of `μ`; the direction of its affine
support is the direction of the affine support of `μ`; there is a linear isometric equivalence of
the two intrinsic `L²` spaces preserving variance and intertwining the affine covariance
relaxations;
and `Poincare.CovarianceGradient.Intrinsic.constant (translateLaw μ b) =
Poincare.CovarianceGradient.Intrinsic.constant μ`. Moreover `μ` has a
finite ambient second moment, so its barycenter exists, and translating by the negative barycenter
gives a law with zero mean. Dimension zero is included. No Poincaré inequality, finiteness of the
constant, isotropic reduction or KLS statement is packaged here, and the constant identity itself is
proved for every Borel law.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.LemAffinePoincareTranslationInvariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The complete translation-invariance statement of the Blueprint for the affine constant. -/
theorem certificate (μ : ProbabilityMeasure E) (hμ : KLS.LogConcave μ) :
    (∀ b : E,
        KLS.LogConcave (FunctionalInequalities.Probability.translateLaw μ b) ∧
          Covariance.operator
                (FunctionalInequalities.Probability.translateLaw μ b : Measure E) =
              Covariance.operator (μ : Measure E) ∧
            (Probability.affineSupport
                    (FunctionalInequalities.Probability.translateLaw μ b)).direction =
                (Probability.affineSupport μ).direction ∧
              (∃ e :
                  Lp ℝ 2
                      (Probability.intrinsicMeasure
                          (FunctionalInequalities.Probability.translateLaw μ b) :
                        Measure
                          (Probability.affineSupport
                              (FunctionalInequalities.Probability.translateLaw μ
                                b)).direction) ≃ₗᵢ[ℝ]
                    Lp ℝ 2
                      (Probability.intrinsicMeasure μ :
                        Measure (Probability.affineSupport μ).direction),
                  (∀ f,
                      L2.variance (Probability.intrinsicMeasure μ) (e f) =
                        L2.variance
                          (Probability.intrinsicMeasure
                            (FunctionalInequalities.Probability.translateLaw μ b))
                          f) ∧
                    ∀ f,
                      FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy
                          (FunctionalInequalities.Probability.translateLaw μ b) f =
                        FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy μ
                          (e f)) ∧
                FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant
                    (FunctionalInequalities.Probability.translateLaw μ b) =
                  FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ) ∧
      MemLp id 2 (μ : Measure E) ∧
        ∫ x,
            x ∂(FunctionalInequalities.Probability.translateLaw μ (-∫ x, x ∂(μ : Measure E)) :
              Measure E) =
          0 :=
  ⟨fun b ↦
    ⟨hμ.translateLaw b, Covariance.operator_translateLaw μ b,
      Probability.direction_affineSupport_translateLaw μ b,
      FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.exists_translateLaw_isometry μ
        b,
      FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_translateLaw μ b⟩,
    hμ.memLp_id_two, hμ.integral_id_translateLaw_neg_integral⟩

/--
Typed application on the Euclidean family of the KLS statement, in every dimension: centering
by the barycenter keeps log-concavity and the affine constant. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : KLS.LogConcave μ) :
    KLS.LogConcave
        (FunctionalInequalities.Probability.translateLaw μ
          (-∫ x, x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) ∧
      ∫ x,
            x ∂(FunctionalInequalities.Probability.translateLaw μ
                (-∫ x, x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) :
              Measure (EuclideanSpace ℝ (Fin n))) =
          0 ∧
        FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant
            (FunctionalInequalities.Probability.translateLaw μ
              (-∫ x, x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) =
          FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ :=
  ⟨((certificate μ hμ).1 _).1, (certificate μ hμ).2.2, ((certificate μ hμ).1 _).2.2.2.2⟩

/--
Dimension zero: both affine constants are zero and the translated law is still log-concave. -/
example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) (hμ : KLS.LogConcave μ)
    (b : EuclideanSpace ℝ (Fin 0)) :
    FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant
          (FunctionalInequalities.Probability.translateLaw μ b) =
        0 ∧
      FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ = 0 ∧
        KLS.LogConcave (FunctionalInequalities.Probability.translateLaw μ b) :=
  ⟨FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq_zero_of_subsingleton
      _,
    FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq_zero_of_subsingleton
      μ,
    ((certificate μ hμ).1 b).1⟩

end Solutions.LemAffinePoincareTranslationInvariance

/--
info: 'Solutions.LemAffinePoincareTranslationInvariance.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemAffinePoincareTranslationInvariance.certificate

/--
info: 'FunctionalInequalities.Energy.Euclidean.gradient_comp_linearIsometryEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.gradient_comp_linearIsometryEquiv

/--
info: 'FunctionalInequalities.Covariance.operator_map_linearIsometryEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Covariance.operator_map_linearIsometryEquiv

/--
info: 'FunctionalInequalities.L2.LinearIsometry.variance_pullbackEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.L2.LinearIsometry.variance_pullbackEquiv

/--
info: 'FunctionalInequalities.Energy.CovarianceGradient.relaxation_mapLinearIsometryEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.CovarianceGradient.relaxation_mapLinearIsometryEquiv

/--
info: 'FunctionalInequalities.Poincare.CovarianceGradient.constant_mapLinearIsometryEquiv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.CovarianceGradient.constant_mapLinearIsometryEquiv

/--
info: 'FunctionalInequalities.Probability.affineSupport_translateLaw'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.affineSupport_translateLaw

/--
info: 'FunctionalInequalities.Probability.intrinsicMeasure_translateLaw'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.intrinsicMeasure_translateLaw

/--
info: 'FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.exists_translateLaw_isometry'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms
    FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.exists_translateLaw_isometry

/--
info: 'FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_translateLaw'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_translateLaw

/--
info: 'FunctionalInequalities.KLS.LogConcave.translateLaw'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.translateLaw

/--
info: 'FunctionalInequalities.KLS.LogConcave.memLp_id_two'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.memLp_id_two

/--
info: 'FunctionalInequalities.KLS.LogConcave.integral_id_translateLaw_neg_integral'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.integral_id_translateLaw_neg_integral

module

public import FunctionalInequalities.Energy.CovarianceGradient.Translation
public import FunctionalInequalities.Energy.Relaxation.Quadratic
public import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic
public import FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic
public import FunctionalInequalities.Poincare.CovarianceGradient.Transport
public import FunctionalInequalities.Probability.Covariance.Factorization

/-!
# The affine covariance relaxation is the closed covariance form

Source: Blueprint `thm:affine-covariance-relaxation-closed`. Read
`LogConcave.intrinsicCovariance_closedQuadratic`,
`LogConcave.intrinsicCovariance_agreesOnTests`,
`LogConcave.intrinsicCovariance_isSequentialCoreFor`,
`LogConcave.intrinsicCovariance_denseRealization`, the translation statements, and finally
`LogConcave.intrinsicCovariance_energy_eq_normSq` and
`LogConcave.intrinsicCovariance_constant_eq_normSq`.

For a compact-set log-concave law `μ` on a finite-dimensional Euclidean space, with intrinsic law
`ν` on the direction space `V` and `Σ` its covariance operator, choose a norm factor `B` satisfying
`⟪Σ v, v⟫ = ‖B v‖²` (`Covariance.exists_inner_eq_norm_sq`). Then the affine covariance pre-energy of
`def:affine-poincare-constant` has the same realization and energies as the quadratic pre-energy
`f ↦ ‖B ∇f‖²` of the closable weighted gradient operator of `lem:covariance-core-closure`, so:

* its realization is dense in `L²(ν)` and its sequential relaxation
  `Energy.CovarianceGradient.Intrinsic.energy μ` is a
  closed quadratic form;
* the relaxation agrees with the raw covariance energy on every globally Lipschitz test, so the
  tests form a sequential core;
* translating `ν` by any `c ∈ V` gives an `L²` isometry preserving variance and covariance
  energy, under which the relaxation and its optimal constant are unchanged;
* `Energy.CovarianceGradient.Intrinsic.energy μ` equals the squared-norm energy of the closure of `B
  ∇` restricted to the
  core `ℝ + C_c^∞(V)`, which is the closed covariance form of the pinned CMH source, and
  `Poincare.CovarianceGradient.Intrinsic.constant μ` is the optimal constant of that closed form.

The zero-dimensional direction space is included: `B = 0` and every class is constant. Nothing here
asserts a Poincaré inequality, the translation invariance of
`Poincare.CovarianceGradient.Intrinsic.constant` under
translations of `μ` in the ambient space (a separate node), an isotropic reduction, or KLS.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities

open KLS Energy Energy.Euclidean Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E}


namespace KLS.LogConcave

section CovarianceRelaxation

variable (hμ : LogConcave μ)

include hμ in
/-- The affine covariance pre-energy has dense realization in the intrinsic `L²` space. -/
theorem intrinsicCovariance_denseRealization :
    (Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)).DenseRealization := by
  obtain ⟨B, hB⟩ := Covariance.exists_intrinsic_inner_eq_norm_sq μ
  refine (hμ.dense_domain_intrinsicWeightedOperator Measure.addHaar B).mono ?_
  intro f hf
  obtain ⟨g, h, rfl⟩ := (Energy.WeightedGradient.mem_domain_operator_iff _ B _ f).mp hf
  obtain ⟨c, rfl⟩ := (Energy.CovarianceGradient.weightedTest_iff_exists_test _ B hB g).mp h
  exact ⟨c, rfl⟩

include hμ in
/-- The affine covariance relaxation is a densely defined closed quadratic form. -/
theorem intrinsicCovariance_closedQuadratic :
    ClosedQuadratic (Energy.CovarianceGradient.Intrinsic.energy μ) := by
  obtain ⟨B, hB⟩ := Covariance.exists_intrinsic_inner_eq_norm_sq μ
  rw [hμ.intrinsicCovariance_energy_eq_operator Measure.addHaar B hB]
  exact
    PreEnergy.Quadratic.closedQuadratic_sequentialRelaxation
      (PreEnergy.ofLinearPMap_quadratic _)
      ((PreEnergy.ofLinearPMap_denseRealization_iff _).mpr
        (hμ.dense_domain_intrinsicWeightedOperator Measure.addHaar B))

include hμ in
/-- The relaxation returns the raw covariance energy on every globally Lipschitz test. -/
theorem intrinsicCovariance_agreesOnTests :
    (Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)).AgreesOnTests
      (Energy.CovarianceGradient.Intrinsic.energy μ) := by
  intro f
  obtain ⟨B, hB⟩ := Covariance.exists_intrinsic_inner_eq_norm_sq μ
  have h : Energy.WeightedGradient.IsTest (Probability.intrinsicMeasure μ) B f.toFun :=
    (Energy.CovarianceGradient.weightedTest_iff_exists_test _ B hB f.toFun).mpr ⟨f, rfl⟩
  have hmem : f.toL2 ∈ (hμ.intrinsicWeightedOperator Measure.addHaar B).domain :=
    Energy.WeightedGradient.toLp_mem_domain_operator _ B _ h
  change Energy.CovarianceGradient.Intrinsic.energy μ f.toL2 = ((f.energy : NNReal) : ℝ≥0∞)
  rw [hμ.intrinsicCovariance_energy_eq_operator Measure.addHaar B hB,
    PreEnergy.sequentialRelaxation_ofLinearPMap_toAmbient _
      (hμ.intrinsicWeightedOperator_isClosable Measure.addHaar B) ⟨f.toL2, hmem⟩]
  congr 1
  apply NNReal.eq
  change
    ((‖hμ.intrinsicWeightedOperator Measure.addHaar B ⟨f.toL2, hmem⟩‖₊ ^ 2 : NNReal) : ℝ) =
      (f.energy : ℝ)
  rw [Energy.CovarianceGradient.Test.coe_energy_eq_norm_sq _ B hB f h,
    Energy.WeightedGradient.operator_apply _ B _
      (hμ.intrinsicMeasure.frontier_support_eq_zero hμ.interior_intrinsic_support_nonempty) h
      hmem rfl]
  push_cast
  rfl

include hμ in
/-- The globally Lipschitz covariance tests form a sequential core of the affine relaxation. -/
theorem intrinsicCovariance_isSequentialCoreFor :
    (Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)).IsSequentialCoreFor
      (Energy.CovarianceGradient.Intrinsic.energy μ) :=
  ⟨hμ.intrinsicCovariance_agreesOnTests, rfl⟩

include hμ in
/-- The covariance energy of a test depends only on its intrinsic `L²` class. -/
theorem intrinsicCovariance_respectsAmbientFibers :
    (Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)).RespectsAmbientFibers :=
  hμ.intrinsicCovariance_agreesOnTests.respectsAmbientFibers

end CovarianceRelaxation

end KLS.LogConcave

section Translation

variable (μ) (c : (affineSupport μ).direction)

namespace Energy.CovarianceGradient.Intrinsic

/-- Translating the intrinsic law: the covariance relaxation of the translated law is the affine
relaxation pulled back along the translation isometry. No log-concavity is needed. -/
theorem relaxation_translate_intrinsicMeasure
    (f :
      Lp ℝ 2
        (Probability.translateLaw (Probability.intrinsicMeasure μ) c :
          Measure (affineSupport μ).direction)) :
    Energy.CovarianceGradient.relaxation
        (Probability.translateLaw (Probability.intrinsicMeasure μ) c) f =
      energy μ (L2.Translation.pullbackEquiv (Probability.intrinsicMeasure μ) c f) :=
  Energy.CovarianceGradient.relaxation_translateLaw (Probability.intrinsicMeasure μ) c f

end Energy.CovarianceGradient.Intrinsic

namespace Poincare.CovarianceGradient.Intrinsic

/--
The affine constant is the optimal constant of the covariance relaxation of every translate of
the intrinsic law. No log-concavity is needed. -/
theorem constant_eq_translate_intrinsicMeasure :
    constant μ =
      Poincare.L2Energy.constant (Probability.translateLaw (Probability.intrinsicMeasure μ) c)
        (Energy.CovarianceGradient.relaxation
          (Probability.translateLaw (Probability.intrinsicMeasure μ) c)) :=
  (Poincare.CovarianceGradient.constant_translateLaw (Probability.intrinsicMeasure μ) c).symm

end Poincare.CovarianceGradient.Intrinsic

end Translation

section ClosedForm

variable (hμ : LogConcave μ) (m : Measure (affineSupport μ).direction) [m.IsAddHaarMeasure]
  (B : (affineSupport μ).direction →L[ℝ] (affineSupport μ).direction)

namespace KLS.LogConcave

/-- The affine relaxation is the squared-norm energy of the closure of the weighted gradient
restricted to the core `ℝ + C_c^∞(V)`: the closed covariance form of the pinned CMH source. -/
theorem intrinsicCovariance_energy_eq_normSq
    (hB :
      ∀ v,
        inner ℝ (Covariance.operator (Probability.intrinsicMeasure μ : Measure _) v) v =
          ‖B v‖ ^ 2) :
    Energy.CovarianceGradient.Intrinsic.energy μ =
      PreEnergy.normSqEnergy
        ((hμ.intrinsicWeightedOperator m B).domRestrict
            (Energy.WeightedGradient.constantSmoothCore
              (Probability.intrinsicMeasure μ))).closure := by
  rw [hμ.intrinsicCovariance_energy_eq_operator m B hB,
    PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy _
      (hμ.intrinsicWeightedOperator_isClosable m B),
    hμ.closure_domRestrict_intrinsicWeightedOperator m B
      (Energy.WeightedGradient.smoothCore_le_constantSmoothCore _)
      (Energy.WeightedGradient.constantSmoothCore_le_domain_operator _ B _)]

/-- The affine Poincaré constant is the optimal constant of the closed covariance form. -/
theorem intrinsicCovariance_constant_eq_normSq
    (hB :
      ∀ v,
        inner ℝ (Covariance.operator (Probability.intrinsicMeasure μ : Measure _) v) v =
          ‖B v‖ ^ 2) :
    Poincare.CovarianceGradient.Intrinsic.constant μ =
      Poincare.L2Energy.constant (Probability.intrinsicMeasure μ)
        (PreEnergy.normSqEnergy
          ((hμ.intrinsicWeightedOperator m B).domRestrict
              (Energy.WeightedGradient.constantSmoothCore
                (Probability.intrinsicMeasure μ))).closure) := by
  unfold Poincare.CovarianceGradient.Intrinsic.constant
  rw [hμ.intrinsicCovariance_energy_eq_normSq m B hB]

end KLS.LogConcave

end ClosedForm

end FunctionalInequalities

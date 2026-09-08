import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Translation
import FunctionalInequalities.Energy.Relaxation.Quadratic
import FunctionalInequalities.KLS.LogConcave.CovarianceClosure
import FunctionalInequalities.Poincare.Euclidean.AffineCovariance
import FunctionalInequalities.Probability.CovarianceSqrt

/-!
# The affine covariance relaxation is the closed covariance form

Source: Blueprint `thm:affine-covariance-relaxation-closed`. Read `LogConcave.affine_closedQuadratic`,
`LogConcave.affine_agreesOnTests`, `LogConcave.affine_isSequentialCoreFor`,
`LogConcave.affine_denseRealization`, the translation statements, and finally
`LogConcave.affine_energy_eq_normSqEnergy` and `LogConcave.affine_constant_eq_normSqEnergy`.

For a compact-set log-concave law `μ` on a finite-dimensional Euclidean space, with intrinsic law
`ν` on the direction space `V` and `Σ` its covariance operator, choose a square root `B` with
`⟪Σ v, v⟫ = ‖B v‖²` (`Covariance.exists_sqrt`). Then the affine covariance pre-energy of
`def:affine-poincare-constant` has the same realization and energies as the quadratic pre-energy
`f ↦ ‖B ∇f‖²` of the closable weighted gradient operator of `lem:covariance-core-closure`, so:

* its realization is dense in `L²(ν)` and its sequential relaxation `Energy.Affine.energy μ` is a
  closed quadratic form;
* the relaxation agrees with the raw covariance energy on every globally Lipschitz test, so the
  tests form a sequential core;
* translating `ν` by any `c ∈ V` gives an `L²` isometry preserving variance and covariance
  energy, under which the relaxation and its optimal constant are unchanged;
* `Energy.Affine.energy μ` equals the squared-norm energy of the closure of `B ∇` restricted to the
  core `ℝ + C_c^∞(V)`, which is the closed covariance form of the pinned CMH source, and
  `Poincare.Affine.constant μ` is the optimal constant of that closed form.

The zero-dimensional direction space is included: `B = 0` and every class is constant. Nothing here
asserts a Poincaré inequality, the translation invariance of `Poincare.Affine.constant` under
translations of `μ` in the ambient space (a separate node), an isotropic reduction, or KLS.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS

open Energy Energy.Euclidean Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E}

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

section Sqrt

variable (μ)

/-- A square root of the intrinsic covariance operator. -/
theorem exists_intrinsic_covariance_sqrt :
    ∃ B : (affineSupport μ).direction →L[ℝ] (affineSupport μ).direction,
      ∀ v, inner ℝ (Covariance.operator (Probability.intrinsicMeasure μ : Measure _) v) v = ‖B v‖ ^ 2 :=
  Covariance.exists_sqrt _

end Sqrt

/-- The affine covariance pre-energy has dense realization in the intrinsic `L²` space. -/
theorem LogConcave.affine_denseRealization (hμ : LogConcave μ) :
    (covariancePreEnergy (Probability.intrinsicMeasure μ)).DenseRealization := by
  obtain ⟨B, hB⟩ := exists_intrinsic_covariance_sqrt μ
  refine (hμ.dense_domain_intrinsicGradientOperator Measure.addHaar B).mono ?_
  intro f hf
  obtain ⟨g, h, rfl⟩ := (mem_domain_gradientOperator_iff _ B _ f).mp hf
  obtain ⟨c, rfl⟩ := (isGradientTest_iff_exists_covarianceGradientTest _ B hB g).mp h
  exact ⟨c, rfl⟩

/-- The affine covariance relaxation is a densely defined closed quadratic form. -/
theorem LogConcave.affine_closedQuadratic (hμ : LogConcave μ) :
    ClosedQuadratic (Energy.Affine.energy μ) := by
  obtain ⟨B, hB⟩ := exists_intrinsic_covariance_sqrt μ
  rw [hμ.affine_energy_eq Measure.addHaar B hB]
  exact PreEnergy.Quadratic.closedQuadratic_sequentialRelaxation (PreEnergy.ofLinearPMap_quadratic _)
    ((PreEnergy.ofLinearPMap_denseRealization_iff _).mpr
      (hμ.dense_domain_intrinsicGradientOperator Measure.addHaar B))

/-- The relaxation returns the raw covariance energy on every globally Lipschitz test. -/
theorem LogConcave.affine_agreesOnTests (hμ : LogConcave μ) :
    (covariancePreEnergy (Probability.intrinsicMeasure μ)).AgreesOnTests (Energy.Affine.energy μ) := by
  intro f
  obtain ⟨B, hB⟩ := exists_intrinsic_covariance_sqrt μ
  have h : IsGradientTest (Probability.intrinsicMeasure μ) B f.toFun :=
    (isGradientTest_iff_exists_covarianceGradientTest _ B hB f.toFun).mpr ⟨f, rfl⟩
  have hmem : f.toL2 ∈ (hμ.intrinsicGradientOperator Measure.addHaar B).domain :=
    toLp_mem_domain_gradientOperator _ B _ h
  change Energy.Affine.energy μ f.toL2 = ((f.covarianceEnergy : NNReal) : ℝ≥0∞)
  rw [hμ.affine_energy_eq Measure.addHaar B hB,
    PreEnergy.sequentialRelaxation_ofLinearPMap_toAmbient _
      (hμ.intrinsicGradientOperator_isClosable Measure.addHaar B) ⟨f.toL2, hmem⟩]
  congr 1
  apply NNReal.eq
  change ((‖hμ.intrinsicGradientOperator Measure.addHaar B ⟨f.toL2, hmem⟩‖₊ ^ 2 : NNReal) : ℝ) =
    (f.covarianceEnergy : ℝ)
  rw [coe_covarianceEnergy_eq_norm_sq _ B hB f h,
    gradientOperator_apply _ B _ (hμ.intrinsicMeasure.frontier_support_eq_zero
      hμ.interior_intrinsic_support_nonempty) h hmem rfl]
  push_cast
  rfl

/-- The globally Lipschitz covariance tests form a sequential core of the affine relaxation. -/
theorem LogConcave.affine_isSequentialCoreFor (hμ : LogConcave μ) :
    (covariancePreEnergy (Probability.intrinsicMeasure μ)).IsSequentialCoreFor (Energy.Affine.energy μ) :=
  ⟨hμ.affine_agreesOnTests, rfl⟩

/-- The covariance energy of a test depends only on its intrinsic `L²` class. -/
theorem LogConcave.affine_respectsAmbientFibers (hμ : LogConcave μ) :
    (covariancePreEnergy (Probability.intrinsicMeasure μ)).RespectsAmbientFibers :=
  hμ.affine_agreesOnTests.respectsAmbientFibers

section Translation

variable (μ) (c : (affineSupport μ).direction)

/-- Translating the intrinsic law: the covariance relaxation of the translated law is the affine
relaxation pulled back along the translation isometry. No log-concavity is needed. -/
theorem _root_.FunctionalInequalities.Energy.Affine.energy_translateLaw
    (f : Lp ℝ 2 (translateLaw (Probability.intrinsicMeasure μ) c :
      Measure (affineSupport μ).direction)) :
    covarianceRelaxation (translateLaw (Probability.intrinsicMeasure μ) c) f =
      Energy.Affine.energy μ (translateL2 (Probability.intrinsicMeasure μ) c f) :=
  covarianceRelaxation_translateLaw (Probability.intrinsicMeasure μ) c f

/-- The affine constant is the optimal constant of the covariance relaxation of every translate of
the intrinsic law. No log-concavity is needed. -/
theorem _root_.FunctionalInequalities.Poincare.Affine.constant_translateLaw :
    Poincare.Affine.constant μ =
      Poincare.L2Energy.constant (translateLaw (Probability.intrinsicMeasure μ) c)
        (covarianceRelaxation (translateLaw (Probability.intrinsicMeasure μ) c)) :=
  (Poincare.L2Energy.constant_covarianceRelaxation_translateLaw (Probability.intrinsicMeasure μ) c).symm

end Translation

section ClosedForm

variable (hμ : LogConcave μ) (m : Measure (affineSupport μ).direction) [m.IsAddHaarMeasure]
  (B : (affineSupport μ).direction →L[ℝ] (affineSupport μ).direction)

/-- The affine relaxation is the squared-norm energy of the closure of the weighted gradient
restricted to the core `ℝ + C_c^∞(V)`: the closed covariance form of the pinned CMH source. -/
theorem LogConcave.affine_energy_eq_normSqEnergy
    (hB : ∀ v, inner ℝ (Covariance.operator (Probability.intrinsicMeasure μ : Measure _) v) v = ‖B v‖ ^ 2) :
    Energy.Affine.energy μ =
      PreEnergy.normSqEnergy ((hμ.intrinsicGradientOperator m B).domRestrict
        (constantSmoothCore (Probability.intrinsicMeasure μ))).closure := by
  rw [hμ.affine_energy_eq m B hB,
    PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy _
      (hμ.intrinsicGradientOperator_isClosable m B),
    hμ.closure_domRestrict_intrinsicGradientOperator m B
      (smoothCore_le_constantSmoothCore _) (constantSmoothCore_le_domain_gradientOperator _ B _)]

/-- The affine Poincaré constant is the optimal constant of the closed covariance form. -/
theorem LogConcave.affine_constant_eq_normSqEnergy
    (hB : ∀ v, inner ℝ (Covariance.operator (Probability.intrinsicMeasure μ : Measure _) v) v = ‖B v‖ ^ 2) :
    Poincare.Affine.constant μ =
      Poincare.L2Energy.constant (Probability.intrinsicMeasure μ)
        (PreEnergy.normSqEnergy ((hμ.intrinsicGradientOperator m B).domRestrict
          (constantSmoothCore (Probability.intrinsicMeasure μ))).closure) := by
  unfold Poincare.Affine.constant
  rw [hμ.affine_energy_eq_normSqEnergy m B hB]

end ClosedForm

end FunctionalInequalities.KLS

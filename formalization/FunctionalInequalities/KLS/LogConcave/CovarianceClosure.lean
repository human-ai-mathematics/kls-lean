import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Closable
import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Core
import FunctionalInequalities.KLS.LogConcave.BorellRepresentation

/-!
# Closable weighted gradient on a full-dimensional log-concave law

Source: Blueprint `lem:covariance-core-closure`. Read the three hypothesis lemmas
`LogConcave.absolutelyContinuous_haar`, `LogConcave.frontier_support_eq_zero`,
`LogConcave.locallyDominates`, then the conclusions `LogConcave.gradientOperator_isClosable`,
`LogConcave.dense_domain_gradientOperator`, `LogConcave.closure_domRestrict_eq_of_smoothCore_le`,
`LogConcave.sequentialRelaxation_gradientOperator_of_mem`,
`LogConcave.sequentialRelaxation_gradientOperator_of_notMem`, and the intrinsic-law versions.

For a compact-set log-concave probability `ν` on a finite-dimensional Euclidean space `V` with
nonempty support interior (the Blueprint's "full-dimensional"), and for every Haar measure `m`:
`ν ≪ m`, the frontier of the convex support is `ν`-null, and the Borell density representative is
bounded below by a positive constant on compact subsets of the interior, so `m` is locally
dominated by `ν` there. These are exactly the hypotheses of the generic operator modules. Hence,
for every `B : V →L[ℝ] V`, the operator `g ↦ B ∘ ∇g` on globally Lipschitz `L²(ν)` tests is densely
defined and closable, its closure equals the closure of its restriction to any core between the
smooth compactly supported functions and the full domain (in particular `ℝ + C_c^∞(V)`), and the
sequential relaxation of `‖B ∇g‖²` is `‖T̄ f‖²` on the domain of the closure and `⊤` outside it.
The Blueprint's `Σ^{1/2}` is one choice of `B`; every `B` gives a positive semidefinite `Σ = B†B`.

The intrinsic law of any log-concave law on any finite-dimensional Euclidean space is
full-dimensional on its direction space, so the same conclusions hold there, including the
zero-dimensional direction space, where the operator vanishes on the whole `L²` space.

No Poincaré inequality, translation invariance, isotropic reduction or KLS statement is made.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS

open Energy Energy.Euclidean Probability

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

section FullDimensional

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]

/-- A full-dimensional log-concave law is absolutely continuous with respect to Haar measure. -/
theorem LogConcave.absolutelyContinuous_haar (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) : (ν : Measure V) ≪ m :=
  hν.absolutelyContinuous_of_interior_support_nonempty m hi

/-- The frontier of the convex support of a full-dimensional log-concave law is null. -/
theorem LogConcave.frontier_support_eq_zero (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (ν : Measure V) (frontier (ν : Measure V).support) = 0 :=
  hν.absolutelyContinuous_haar Measure.addHaar hi
    (hν.convex_support.addHaar_frontier Measure.addHaar)

/-- On compact subsets of the support interior the Borell density is bounded below by a positive
constant, so Haar measure is locally dominated by the law. -/
theorem LogConcave.locallyDominates (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) : LocallyDominates ν m := by
  obtain ⟨ρ, hρ⟩ := hν.exists_isBorellDensity_of_interior_support_nonempty m hi
    (hν.absolutelyContinuous_haar m hi)
  intro K hK hKΩ
  obtain ⟨a, b, ha, hab⟩ := hρ.exists_bounds_of_isCompact hK hKΩ
  set a' : ℝ≥0 := Real.toNNReal a with ha'
  have ha'0 : a' ≠ 0 := (Real.toNNReal_pos.mpr ha).ne'
  refine ⟨a'⁻¹, Measure.le_iff.mpr fun s hs ↦ ?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs, smul_eq_mul,
    ENNReal.coe_inv ha'0]
  have hν' : (ν : Measure V) (s ∩ K) = ∫⁻ x in s ∩ K, ENNReal.ofReal (ρ x) ∂m := by
    rw [← hρ.withDensity_eq, withDensity_apply _ (hs.inter hK.measurableSet)]
  have hlow : (a' : ℝ≥0∞) * m (s ∩ K) ≤ (ν : Measure V) (s ∩ K) := by
    rw [hν', ← setLIntegral_const]
    refine setLIntegral_mono hρ.measurable.ennreal_ofReal fun x hx ↦ ?_
    exact ENNReal.ofReal_le_ofReal (hab x hx.2).1
  have ha'top : (a' : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have ha'0' : (a' : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha'0
  calc m (s ∩ K) = ((a' : ℝ≥0∞))⁻¹ * ((a' : ℝ≥0∞) * m (s ∩ K)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha'0' ha'top, one_mul]
    _ ≤ ((a' : ℝ≥0∞))⁻¹ * (ν : Measure V) (s ∩ K) := by gcongr

variable (B : V →L[ℝ] V)

/-- The weighted gradient operator of a full-dimensional log-concave law. -/
abbrev LogConcave.gradientOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  Energy.Euclidean.gradientOperator ν B (hν.absolutelyContinuous_haar m hi)

/-- Closability on a full-dimensional log-concave law. -/
theorem LogConcave.gradientOperator_isClosable (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (hν.gradientOperator m B hi).IsClosable :=
  Energy.Euclidean.gradientOperator_isClosable ν B _ (hν.frontier_support_eq_zero hi)
    (hν.locallyDominates m hi)

/-- Dense domain on a full-dimensional log-concave law. -/
theorem LogConcave.dense_domain_gradientOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Dense ((hν.gradientOperator m B hi).domain : Set (Lp ℝ 2 (ν : Measure V))) :=
  Energy.Euclidean.dense_domain_gradientOperator ν B _

/-- Every core between the smooth compactly supported classes and the full domain has the same
closure as the operator; the Blueprint's `ℝ + C_c^∞(V)` is such a core. -/
theorem LogConcave.closure_domRestrict_eq_of_smoothCore_le (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    {S : Submodule ℝ (Lp ℝ 2 (ν : Measure V))} (hS : smoothCore ν ≤ S)
    (hS' : S ≤ (hν.gradientOperator m B hi).domain) :
    ((hν.gradientOperator m B hi).domRestrict S).closure = (hν.gradientOperator m B hi).closure :=
  Energy.Euclidean.closure_domRestrict_eq_of_smoothCore_le ν B _
    (hν.frontier_support_eq_zero hi) (hν.gradientOperator_isClosable m B hi) hS hS'

/-- On the domain of the closure, the sequential relaxation of `‖B ∇g‖²` is `‖T̄ f‖²`. -/
theorem LogConcave.sequentialRelaxation_gradientOperator_of_mem (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    (f : (hν.gradientOperator m B hi).closure.domain) :
    (PreEnergy.ofLinearPMap (hν.gradientOperator m B hi)).sequentialRelaxation f =
      (‖(hν.gradientOperator m B hi).closure f‖₊ ^ 2 : ℝ≥0) :=
  PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem _ (hν.gradientOperator_isClosable m B hi) f

/-- Outside the domain of the closure, the sequential relaxation is infinite. -/
theorem LogConcave.sequentialRelaxation_gradientOperator_of_notMem (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {f : Lp ℝ 2 (ν : Measure V)}
    (hf : f ∉ (hν.gradientOperator m B hi).closure.domain) :
    (PreEnergy.ofLinearPMap (hν.gradientOperator m B hi)).sequentialRelaxation f = ⊤ :=
  PreEnergy.sequentialRelaxation_ofLinearPMap_of_notMem _ (hν.gradientOperator_isClosable m B hi) hf

/-- The relaxation agrees with the raw energy `‖B ∇g‖²` on every test class. -/
theorem LogConcave.sequentialRelaxation_gradientOperator_toAmbient (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    (f : (hν.gradientOperator m B hi).domain) :
    (PreEnergy.ofLinearPMap (hν.gradientOperator m B hi)).sequentialRelaxation f =
      ((PreEnergy.ofLinearPMap (hν.gradientOperator m B hi)).energy f : ℝ≥0∞) :=
  PreEnergy.sequentialRelaxation_ofLinearPMap_toAmbient _ (hν.gradientOperator_isClosable m B hi) f

/-- With `⟪Σ v, v⟫ = ‖B v‖²` for the covariance operator of `ν`, the covariance relaxation of the
affine node is the operator relaxation. -/
theorem LogConcave.covarianceRelaxation_eq (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) :
    covarianceRelaxation ν =
      (PreEnergy.ofLinearPMap (hν.gradientOperator m B hi)).sequentialRelaxation :=
  covarianceRelaxation_eq_sequentialRelaxation_ofLinearPMap ν B _
    (hν.frontier_support_eq_zero hi) hB

end FullDimensional

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E} (m : Measure (Probability.affineSupport μ).direction)
  [m.IsAddHaarMeasure] (B : (Probability.affineSupport μ).direction →L[ℝ]
    (Probability.affineSupport μ).direction)

/-- The intrinsic weighted gradient operator of a log-concave law. -/
abbrev LogConcave.intrinsicGradientOperator (hμ : LogConcave μ) :
    Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) →ₗ.[ℝ]
      Lp (Probability.affineSupport μ).direction 2
        (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) :=
  hμ.intrinsicMeasure.gradientOperator m B hμ.interior_intrinsic_support_nonempty

/-- Closability of the intrinsic weighted gradient of any log-concave law. -/
theorem LogConcave.intrinsicGradientOperator_isClosable (hμ : LogConcave μ) :
    (hμ.intrinsicGradientOperator m B).IsClosable :=
  hμ.intrinsicMeasure.gradientOperator_isClosable m B hμ.interior_intrinsic_support_nonempty

/-- Dense domain of the intrinsic weighted gradient of any log-concave law. -/
theorem LogConcave.dense_domain_intrinsicGradientOperator (hμ : LogConcave μ) :
    Dense ((hμ.intrinsicGradientOperator m B).domain : Set (Lp ℝ 2
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction))) :=
  hμ.intrinsicMeasure.dense_domain_gradientOperator m B hμ.interior_intrinsic_support_nonempty

/-- The intrinsic operator has the same closure as its restriction to any core containing the
smooth compactly supported classes. -/
theorem LogConcave.closure_domRestrict_intrinsicGradientOperator (hμ : LogConcave μ)
    {S : Submodule ℝ (Lp ℝ 2
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction))}
    (hS : smoothCore (Probability.intrinsicMeasure μ) ≤ S)
    (hS' : S ≤ (hμ.intrinsicGradientOperator m B).domain) :
    ((hμ.intrinsicGradientOperator m B).domRestrict S).closure =
      (hμ.intrinsicGradientOperator m B).closure :=
  hμ.intrinsicMeasure.closure_domRestrict_eq_of_smoothCore_le m B
    hμ.interior_intrinsic_support_nonempty hS hS'

/-- The affine covariance relaxation of the definition node is the operator relaxation for any
`B` with `⟪Σ v, v⟫ = ‖B v‖²`, `Σ` the intrinsic covariance. -/
theorem LogConcave.affine_energy_eq (hμ : LogConcave μ)
    (hB : ∀ v, inner ℝ (Covariance.operator
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) v) v =
        ‖B v‖ ^ 2) :
    Energy.Affine.energy μ =
      (PreEnergy.ofLinearPMap (hμ.intrinsicGradientOperator m B)).sequentialRelaxation :=
  hμ.intrinsicMeasure.covarianceRelaxation_eq m B hμ.interior_intrinsic_support_nonempty hB

end Intrinsic

end FunctionalInequalities.KLS

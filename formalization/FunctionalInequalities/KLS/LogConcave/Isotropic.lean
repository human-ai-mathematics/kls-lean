import FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv
import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.KLS.LogConcave.Translation
import FunctionalInequalities.KLS.LogConcave.WeightedGradient
import FunctionalInequalities.KLS.Statement
import FunctionalInequalities.Poincare.LipschitzGradient.Comparison
import FunctionalInequalities.Poincare.L2.Comparison
import FunctionalInequalities.KLS.LogConcave.Poincare
import FunctionalInequalities.Probability.Covariance.Whitening
import FunctionalInequalities.Probability.Covariance.Intrinsic

/-!
# Affine and isotropic KLS formulations

Source: Blueprint `thm:affine-isotropic-reduction`. Read `IsotropicBound`, `CovarianceBound`,
`AffineBound`, then `affineBound_of_isotropicBound`, `covarianceBound_of_affineBound`,
`isotropicBound_of_covarianceBound`, `affine_isotropic_reduction` and `conjecture_of_affineBound`.

For a fixed `K ≥ 0` the following statements about log-concave laws are equivalent, each quantified
over every finite-dimensional Euclidean space of a fixed universe:

1. every isotropic log-concave law `ν` satisfies `C_P^lit(ν) ≤ K` (`IsotropicBound K`);
2. every log-concave law `μ` satisfies `C_P^lit(μ) ≤ K ‖Cov_μ‖` (`CovarianceBound K`);
3. every log-concave law `μ` satisfies `C_P^aff(μ) ≤ K` (`AffineBound K`).

Proof route. (1) ⇒ (3): center the intrinsic law `ν` of `μ` by translating inside the direction space
and whiten it by a self-adjoint whitening `W` of the intrinsic covariance (`Covariance.exists_whitening`,
positive definite by `lem:ambient-intrinsic-covariance`); the result is an isotropic log-concave law
`ν̃` with `C_P^aff(μ) = C_P(ν̃, covariance relaxation) = C_P(ν̃, Lipschitz gradient relaxation) =
C_P^lit(ν̃)` by translation and linear transport of the covariance relaxation and by the Lipschitz
bridge with the literature constant. (3) ⇒ (2): `C_P^lit(μ)` is the optimal constant of the Lipschitz
gradient relaxation of `ν`, the covariance relaxation is at most `‖Σ‖` times it, and
`‖Σ‖ = ‖Cov_μ‖`. (2) ⇒ (1): an isotropic law has covariance operator `1`, of norm at most one.
The zero-dimensional law is included in all three statements; there every constant is zero.

`conjecture_of_affineBound` specializes (2) to the Euclidean family `EuclideanSpace ℝ (Fin n)`:
item (3) for some finite `K` implies the literal KLS proposition `KLS.Conjecture`. The converse
passage from the `Fin n` family to arbitrary spaces is not stated here. Nothing here asserts that
any of the three statements holds for some `K`.
-/

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace

namespace FunctionalInequalities

open Energy Energy.Euclidean Probability

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

namespace KLS.LogConcave

/-- A probability law carried by a continuous linear equivalence inherits compact-set
log-concavity from its image law. -/
theorem of_continuousLinearEquiv_map {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (ν : ProbabilityMeasure F) (T : F ≃L[ℝ] E)
    (hmap : Measure.map T (ν : Measure F) = (μ : Measure E)) : LogConcave ν := by
  intro K L hK hL t ht ht1
  have hm (S : Set F) (hS : IsCompact S) : (μ : Measure E) (T '' S) = (ν : Measure F) S := by
    rw [← hmap, Measure.map_apply T.continuous.measurable (hS.image T.continuous).measurableSet,
      Set.preimage_image_eq _ T.injective]
  have hcomb : T '' {z | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
      {z | ∃ x ∈ T '' K, ∃ y ∈ T '' L, z = t • x + (1 - t) • y} := by
    have hf (x y : F) : T (t • x + (1 - t) • y) = t • T x + (1 - t) • T y := by
      rw [map_add, map_smul, map_smul]
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨T x, ⟨x, hx, rfl⟩, T y, ⟨y, hy, rfl⟩, hf x y⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨t • x + (1 - t) • y, ⟨x, hx, y, hy, rfl⟩, hf x y⟩
  have hc : IsCompact {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} := by
    have he : {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
        (fun p : F × F => t • p.1 + (1 - t) • p.2) '' (K ×ˢ L) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
    rw [he]
    exact (hK.prod hL).image (by fun_prop)
  have h := hμ (T '' K) (T '' L) (hK.image T.continuous) (hL.image T.continuous) t ht ht1
  rwa [hm K hK, hm L hL, ← hcomb, hm _ hc] at h

end KLS.LogConcave

end Transport

section Euclidean

variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]


namespace KLS.LogConcave

omit [CompleteSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [CompleteSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂] in
/-- The image of a log-concave law under a continuous linear equivalence is log-concave. -/
theorem mapContinuousLinearEquiv {ν : ProbabilityMeasure V₁} (hν : LogConcave ν) (T : V₁ ≃L[ℝ] V₂) :
    LogConcave (Probability.mapContinuousLinearEquiv ν T) :=
  hν.of_continuousLinearEquiv_map _ T.symm (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T).map_eq

end KLS.LogConcave

namespace Probability

omit [CompleteSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] in
omit [InnerProductSpace ℝ V₁] in
/-- Translation keeps a finite second moment. -/
theorem memLp_id_two_translateLaw
    (ν : ProbabilityMeasure V₁) (c : V₁) (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (translateLaw ν c : Measure V₁) := by
  rw [coe_translateLaw]
  exact (measurableEmbedding_addLeft c).memLp_map_measure_iff.mpr ((memLp_const c).add h)

end Probability

namespace KLS.LogConcave

omit [CompleteSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] in
/-- A log-concave law with full affine support has support with nonempty interior. -/
theorem interior_support_nonempty_of_affineSupport_eq_top {ν : ProbabilityMeasure V₁}
    (hν : LogConcave ν) (h : affineSupport ν = ⊤) :
    (interior (ν : Measure V₁).support).Nonempty :=
  hν.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr h

end KLS.LogConcave

end Euclidean

section Statements

universe u

namespace KLS

/-- Item (1): every isotropic log-concave law on every finite-dimensional Euclidean space of the
universe `u` has literature constant at most `K`. -/
def IsotropicBound (K : NNReal) : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V), LogConcave ν → Isotropic ν → Poincare.LocalSlope.Intrinsic.constant ν ≤ (K : ENNReal)

/-- Item (2): every log-concave law on every finite-dimensional Euclidean space of the universe `u`
has literature constant at most `K` times the operator norm of its covariance. -/
def CovarianceBound (K : NNReal) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E), LogConcave μ →
      Poincare.LocalSlope.Intrinsic.constant μ ≤ (K : ENNReal) * ENNReal.ofReal ‖Covariance.operator (μ : Measure E)‖

/-- Item (3): every log-concave law on every finite-dimensional Euclidean space of the universe `u`
has affine covariance Poincaré constant at most `K`. -/
def AffineBound (K : NNReal) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E), LogConcave μ → Poincare.CovarianceGradient.Intrinsic.constant μ ≤ (K : ENNReal)

end KLS

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]


namespace KLS.LogConcave

omit [CompleteSpace E] in
/-- The centered and whitened intrinsic law of a log-concave law: there is an isotropic log-concave
law on the direction space with the same affine covariance Poincaré constant, equal to its literature
constant. -/
theorem exists_isotropic_localSlope_constant_eq {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    ∃ ν' : ProbabilityMeasure (affineSupport μ).direction,
      LogConcave ν' ∧ Isotropic ν' ∧ Poincare.CovarianceGradient.Intrinsic.constant μ = Poincare.LocalSlope.Intrinsic.constant ν' := by
  set ν := Probability.intrinsicMeasure μ with hνdef
  have hν : LogConcave ν := hμ.intrinsicMeasure
  have hν2 : MemLp id 2 (ν : Measure (affineSupport μ).direction) := hμ.intrinsic_memLp_id_two
  have hpos : ∀ v : (affineSupport μ).direction, v ≠ 0 →
      0 < inner ℝ (Covariance.operator (ν : Measure (affineSupport μ).direction) v) v :=
    fun v hv ↦ Covariance.intrinsic_operator_inner_self_pos μ hμ.memLp_id_two hv
  obtain ⟨W, hWadj, hW⟩ := Covariance.exists_whitening (ν : Measure (affineSupport μ).direction) hpos
  set c : (affineSupport μ).direction := -∫ x, x ∂(ν : Measure (affineSupport μ).direction) with hcdef
  set νc := Probability.translateLaw ν c with hνc
  set νt := Probability.mapContinuousLinearEquiv νc W with hνt
  have hνc_lc : LogConcave νc := hν.translateLaw c
  have hνt_lc : LogConcave νt := hνc_lc.mapContinuousLinearEquiv W
  have hνc2 : MemLp id 2 (νc : Measure (affineSupport μ).direction) := Probability.memLp_id_two_translateLaw ν c hν2
  have hνt2 : MemLp id 2 (νt : Measure (affineSupport μ).direction) := Probability.memLp_id_two_mapContinuousLinearEquiv νc W hνc2
  have hmean_c : ∫ x, x ∂(νc : Measure (affineSupport μ).direction) = 0 :=
    Probability.integral_id_translateLaw_neg_integral ν (hν2.integrable one_le_two)
  have hmean_t : ∫ y, y ∂(νt : Measure (affineSupport μ).direction) = 0 := by
    rw [hνt, Probability.integral_id_mapContinuousLinearEquiv νc W (hνc2.integrable one_le_two), hmean_c, map_zero]
  have hcov_c : Covariance.operator (νc : Measure (affineSupport μ).direction) = Covariance.operator (ν : Measure (affineSupport μ).direction) :=
    Covariance.operator_translateLaw ν c
  have hcov_t : Covariance.operator (νt : Measure (affineSupport μ).direction) = ContinuousLinearMap.id ℝ _ := by
    rw [hνt, Covariance.operator_mapContinuousLinearEquiv, hcov_c, hWadj]
    refine ContinuousLinearMap.ext fun u ↦ ext_inner_right ℝ fun v ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    rw [← hWadj, ContinuousLinearMap.adjoint_inner_left, hWadj]
    exact hW u v
  have hiso : Isotropic νt := ⟨hνt2, hmean_t, hcov_t⟩
  -- full support of the whitened law
  have htop : affineSupport νt = ⊤ := by
    apply Probability.affineSupport_mapContinuousLinearEquiv_eq_top
    rw [hνc, affineSupport_translateLaw, affineSupport_intrinsicMeasure]
    exact AffineMap.map_top_of_surjective _ (AffineEquiv.constVAdd ℝ _ c).surjective
  have hi : (interior (νt : Measure (affineSupport μ).direction).support).Nonempty :=
    hνt_lc.interior_support_nonempty_of_affineSupport_eq_top htop
  have hac : (νt : Measure (affineSupport μ).direction) ≪ (Measure.addHaar : Measure (affineSupport μ).direction) :=
    hνt_lc.absolutelyContinuous_haar Measure.addHaar hi
  have hfr : (νt : Measure (affineSupport μ).direction) (frontier (νt : Measure (affineSupport μ).direction).support) = 0 :=
    hνt_lc.frontier_support_eq_zero hi
  refine ⟨νt, hνt_lc, hiso, ?_⟩
  calc Poincare.CovarianceGradient.Intrinsic.constant μ
      = Poincare.L2Energy.constant ν (Energy.CovarianceGradient.relaxation ν) := Poincare.CovarianceGradient.Intrinsic.constant_eq μ
    _ = Poincare.L2Energy.constant νc (Energy.CovarianceGradient.relaxation νc) :=
        (Poincare.CovarianceGradient.constant_translateLaw ν c).symm
    _ = Poincare.L2Energy.constant νt (Energy.CovarianceGradient.relaxation νt) :=
        (Poincare.CovarianceGradient.constant_mapContinuousLinearEquiv νc W).symm
    _ = Poincare.L2Energy.constant νt (FunctionalInequalities.Energy.LipschitzGradient.relaxation νt Measure.addHaar hac) := by
        rw [FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_lipschitz νt Measure.addHaar hac hfr hcov_t]
    _ = Poincare.SmoothTest.constant (νt : Measure (affineSupport μ).direction) :=
        (FunctionalInequalities.Poincare.SmoothTest.constant_eq_lipschitz νt Measure.addHaar hac hfr).symm
    _ = Poincare.LocalSlope.Intrinsic.constant νt := hνt_lc.smoothTest_constant_eq_localSlope

/-- The literature constant of a log-concave law is at most the operator norm of its covariance
times its affine covariance Poincaré constant. -/
theorem localSlope_le_mul_intrinsicCovariance {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) {K : NNReal} (hK : Poincare.CovarianceGradient.Intrinsic.constant μ ≤ (K : ENNReal)) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (K : ENNReal) * ENNReal.ofReal ‖Covariance.operator (μ : Measure E)‖ := by
  have hν : LogConcave (Probability.intrinsicMeasure μ) := hμ.intrinsicMeasure
  have hi : (interior (Probability.intrinsicMeasure μ : Measure (affineSupport μ).direction).support).Nonempty :=
    hμ.interior_intrinsic_support_nonempty
  have hac : (Probability.intrinsicMeasure μ : Measure (affineSupport μ).direction) ≪
      (Measure.addHaar : Measure (affineSupport μ).direction) :=
    hν.absolutelyContinuous_haar Measure.addHaar hi
  have hfr : (Probability.intrinsicMeasure μ : Measure (affineSupport μ).direction)
      (frontier (Probability.intrinsicMeasure μ : Measure (affineSupport μ).direction).support) = 0 :=
    hν.frontier_support_eq_zero hi
  have hlit : Poincare.LocalSlope.Intrinsic.constant μ =
      Poincare.L2Energy.constant (Probability.intrinsicMeasure μ)
        (FunctionalInequalities.Energy.LipschitzGradient.relaxation (Probability.intrinsicMeasure μ) Measure.addHaar hac) := by
    rw [← hμ.smoothTest_constant_eq_intrinsic_and_localSlope.2,
      FunctionalInequalities.Poincare.SmoothTest.constant_eq_lipschitz _ Measure.addHaar hac hfr]
  have hholds : Poincare.L2Energy.Holds (Probability.intrinsicMeasure μ)
      (Energy.CovarianceGradient.relaxation (Probability.intrinsicMeasure μ)) K := by
    have h : Poincare.CovarianceGradient.Intrinsic.Holds μ K := (Poincare.CovarianceGradient.Intrinsic.holds_iff_constant_le μ K).mpr hK
    rw [Poincare.CovarianceGradient.Intrinsic.Holds, Energy.CovarianceGradient.Intrinsic.energy_eq_relaxation_intrinsicMeasure] at h
    exact h
  have hcmp : ∀ f : (FunctionalInequalities.Energy.LipschitzGradient.relaxation (Probability.intrinsicMeasure μ)
      Measure.addHaar hac).domain,
      Energy.CovarianceGradient.relaxation (Probability.intrinsicMeasure μ) f.1 ≤
        (‖Covariance.operator (Probability.intrinsicMeasure μ : Measure (affineSupport μ).direction)‖₊ : ENNReal) *
          FunctionalInequalities.Energy.LipschitzGradient.relaxation (Probability.intrinsicMeasure μ) Measure.addHaar hac f.1 :=
    fun f ↦ FunctionalInequalities.Energy.CovarianceGradient.relaxation_le_mul_lipschitz
      (Probability.intrinsicMeasure μ) Measure.addHaar hac hfr f.1
      ((Energy.Functional.mem_domain _ _).mp f.2)
  have hle := Poincare.L2Energy.constant_le_mul_of_energy_le_mul hholds hcmp
  rw [hlit]
  refine hle.trans (le_of_eq ?_)
  rw [ENNReal.coe_mul, mul_comm, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
  congr 2
  exact NNReal.eq (Covariance.opNorm_operator_intrinsic μ hμ.memLp_id_two)

end KLS.LogConcave

namespace KLS

/-- (1) ⇒ (3). -/
theorem affineBound_of_isotropicBound {K : NNReal} (h : IsotropicBound.{u} K) : AffineBound.{u} K := by
  intro E _ _ _ _ _ _ _ μ hμ
  obtain ⟨ν', hν', hiso, heq⟩ := hμ.exists_isotropic_localSlope_constant_eq
  rw [heq]
  exact h _ ν' hν' hiso

/-- (3) ⇒ (2). -/
theorem covarianceBound_of_affineBound {K : NNReal} (h : AffineBound.{u} K) : CovarianceBound.{u} K := by
  intro E _ _ _ _ _ _ _ μ hμ
  exact hμ.localSlope_le_mul_intrinsicCovariance (h E μ hμ)

/-- (2) ⇒ (1). -/
theorem isotropicBound_of_covarianceBound {K : NNReal} (h : CovarianceBound.{u} K) :
    IsotropicBound.{u} K := by
  intro V _ _ _ _ _ _ _ ν hν hiso
  refine (h V ν hν).trans ?_
  rw [hiso.covariance_identity]
  refine mul_le_of_le_one_right' ?_
  exact ENNReal.ofReal_le_one.mpr ContinuousLinearMap.norm_id_le

/-- The affine and isotropic KLS formulations are equivalent for every fixed finite `K`. -/
theorem affine_isotropic_reduction (K : NNReal) :
    (IsotropicBound.{u} K ↔ CovarianceBound.{u} K) ∧ (CovarianceBound.{u} K ↔ AffineBound.{u} K) :=
  ⟨⟨fun h ↦ covarianceBound_of_affineBound (affineBound_of_isotropicBound h),
      isotropicBound_of_covarianceBound⟩,
    ⟨fun h ↦ affineBound_of_isotropicBound (isotropicBound_of_covarianceBound h),
      covarianceBound_of_affineBound⟩⟩

/-- Item (3) for some finite `K` implies the literal KLS proposition on the Euclidean family. -/
theorem conjecture_of_affineBound {K : NNReal} (h : AffineBound.{0} K) : Conjecture :=
  ⟨K, fun n μ hμ _ ↦ covarianceBound_of_affineBound h (EuclideanSpace ℝ (Fin n)) μ hμ⟩

end KLS

end Statements

end FunctionalInequalities

import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Isometry
import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Translation
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Linear change of variables for the covariance relaxation

Source: Blueprint `thm:affine-isotropic-reduction`, the sentence "whiten the centered intrinsic law
by `Cov^{-1/2}`; pullback of the isotropic inequality gives the covariance-form inequality". Read
`gradient_comp_continuousLinearEquiv`, `Covariance.operator_map_continuousLinearEquiv`,
`mapEquivLaw`, `mapEquivL2`, `L2.variance_mapEquivL2`, `covarianceRelaxation_mapEquivLaw`,
`L2Energy.constant_covarianceRelaxation_mapEquivLaw` and `Probability.affineSupport_mapEquivLaw`.

For a probability law `ν` on a finite-dimensional Euclidean space `V₁` and a continuous linear
equivalence `T : V₁ ≃L[ℝ] V₂`, the image law `mapEquivLaw ν T` lives on `V₂`. Its covariance
operator is `T ∘ Σ ∘ T†` with `T†` the adjoint; the gradient of `g ∘ T` is `T† ∇g ∘ T`; composition
with `T` is a linear isometric equivalence `L²(mapEquivLaw ν T) ≃ L²(ν)` (because `T` is measure
preserving between the two laws) which preserves variance; globally Lipschitz covariance tests
correspond by composition with equal covariance energies, since
`⟪T Σ T† w, w⟫ = ⟪Σ T† w, T† w⟫`; hence the covariance relaxations correspond under the isometry and
the optimal `L²` Poincaré constants of the two relaxations coincide. The affine support of the
image law is the image of the affine support.

This is the non-isometric generalization of `CovarianceGradient/Isometry.lean`; the isometric
module is retained as the certified special case used for translation invariance. Everything holds
for every Borel probability law; no log-concavity, density or closability is used, and no Poincaré
inequality is asserted. The zero-dimensional spaces are included.
-/

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace

namespace FunctionalInequalities.Energy.Euclidean

universe u v

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

section Gradient

/-- The gradient of a function composed with a continuous linear equivalence is the adjoint image
of the gradient at the image point. No differentiability premise is needed. -/
theorem gradient_comp_continuousLinearEquiv (g : V₂ → ℝ) (T : V₁ ≃L[ℝ] V₂) (x : V₁) :
    gradient (fun y ↦ g (T y)) x = (T : V₁ →L[ℝ] V₂).adjoint (gradient g (T x)) := by
  apply (toDual ℝ V₁).injective
  rw [toDual_gradient]
  have hcomp : fderiv ℝ (fun y ↦ g (T y)) x = (fderiv ℝ g (T x)).comp (T : V₁ →L[ℝ] V₂) := by
    have h := T.comp_right_fderiv (f := g) (x := x)
    simpa only [Function.comp_def] using h
  rw [hcomp]
  ext v
  change fderiv ℝ g (T x) (T v) = inner ℝ ((T : V₁ →L[ℝ] V₂).adjoint (gradient g (T x))) v
  rw [← toDual_gradient, toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]
  rfl

end Gradient

section Covariance

/-- Pushing a law forward along a continuous linear equivalence conjugates its covariance operator
by the map and its adjoint. Without a second moment both operators are zero. -/
theorem _root_.FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv
    (ν : Measure V₁) [IsFiniteMeasure ν] (T : V₁ ≃L[ℝ] V₂) :
    Covariance.operator (ν.map T) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator ν)).comp (T : V₁ →L[ℝ] V₂).adjoint := by
  have hcoe : ⇑(T : V₁ →L[ℝ] V₂) = ⇑T := rfl
  by_cases h : MemLp id 2 ν
  · ext u
    apply ext_inner_right ℝ
    intro v
    rw [Covariance.operator_inner, ← hcoe, ProbabilityTheory.covarianceBilin_map h (T : V₁ →L[ℝ] V₂),
      ← Covariance.operator_inner]
    simp only [ContinuousLinearMap.comp_apply]
    exact ContinuousLinearMap.adjoint_inner_right (T : V₁ →L[ℝ] V₂)
      (Covariance.operator ν ((T : V₁ →L[ℝ] V₂).adjoint u)) v
  · have h' : ¬ MemLp id 2 (ν.map T) := by
      intro h'
      apply h
      have h1 : MemLp (fun x ↦ T x) 2 ν :=
        (memLp_map_measure_iff aestronglyMeasurable_id T.continuous.measurable.aemeasurable).mp h'
      have h2 := (T.symm : V₂ →L[ℝ] V₁).comp_memLp' h1
      have h3 : (⇑(T.symm : V₂ →L[ℝ] V₁) ∘ fun x ↦ T x) = id := by
        funext x
        simp
      rwa [h3] at h2
    rw [Covariance.operator_of_not_memLp ν h, Covariance.operator_of_not_memLp (ν.map T) h']
    simp

end Covariance

section Law

variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)

/-- The image of `ν` under the continuous linear equivalence `T`. -/
def mapEquivLaw : ProbabilityMeasure V₂ :=
  ν.map T.continuous.measurable.aemeasurable

theorem coe_mapEquivLaw : (mapEquivLaw ν T : Measure V₂) = (ν : Measure V₁).map T := rfl

/-- `T` is measure preserving from `ν` to its image law. -/
theorem measurePreserving_mapEquivLaw :
    MeasurePreserving T (ν : Measure V₁) (mapEquivLaw ν T : Measure V₂) :=
  ⟨T.continuous.measurable, rfl⟩

/-- `T⁻¹` is measure preserving from the image law back to `ν`. -/
theorem measurePreserving_mapEquivLaw_symm :
    MeasurePreserving T.symm (mapEquivLaw ν T : Measure V₂) (ν : Measure V₁) := by
  refine ⟨T.symm.continuous.measurable, ?_⟩
  rw [coe_mapEquivLaw, Measure.map_map T.symm.continuous.measurable T.continuous.measurable]
  have : (⇑T.symm ∘ ⇑T) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

/-- The covariance operator of the image law. -/
theorem _root_.FunctionalInequalities.Covariance.operator_mapEquivLaw :
    Covariance.operator (mapEquivLaw ν T : Measure V₂) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator (ν : Measure V₁))).comp
        (T : V₁ →L[ℝ] V₂).adjoint :=
  Covariance.operator_map_continuousLinearEquiv (ν : Measure V₁) T

/-- The covariance quadratic form of the image law, read through the adjoint. -/
theorem _root_.FunctionalInequalities.Covariance.inner_operator_mapEquivLaw (w : V₂) :
    inner ℝ (Covariance.operator (mapEquivLaw ν T : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w) := by
  rw [Covariance.operator_mapEquivLaw]
  simp only [ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_right (T : V₁ →L[ℝ] V₂) _ w).symm

/-- The covariance quadratic form of `ν`, read through the adjoint of the inverse. -/
theorem _root_.FunctionalInequalities.Covariance.inner_operator_mapEquivLaw_symm (w : V₁) :
    inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (Covariance.operator (mapEquivLaw ν T : Measure V₂)
        ((T.symm : V₂ →L[ℝ] V₁).adjoint w)) ((T.symm : V₂ →L[ℝ] V₁).adjoint w) := by
  rw [Covariance.inner_operator_mapEquivLaw]
  have hT : (T : V₁ →L[ℝ] V₂).adjoint ((T.symm : V₂ →L[ℝ] V₁).adjoint w) = w := by
    have hcomp : (T.symm : V₂ →L[ℝ] V₁).comp (T : V₁ →L[ℝ] V₂) = ContinuousLinearMap.id ℝ V₁ := by
      ext x
      simp
    have := congrArg (fun A : V₁ →L[ℝ] V₁ ↦ A.adjoint w) hcomp
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] using this
  rw [hT]

/-- Pullback of `L²` classes along `T`. -/
def mapEquivForward : Lp ℝ 2 (mapEquivLaw ν T : Measure V₂) →ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V₁) :=
  Lp.compMeasurePreservingₗᵢ ℝ T (measurePreserving_mapEquivLaw ν T)

/-- Pullback of `L²` classes along `T⁻¹`. -/
def mapEquivBackward : Lp ℝ 2 (ν : Measure V₁) →ₗᵢ[ℝ] Lp ℝ 2 (mapEquivLaw ν T : Measure V₂) :=
  Lp.compMeasurePreservingₗᵢ ℝ T.symm (measurePreserving_mapEquivLaw_symm ν T)

theorem mapEquivForward_coeFn (f : Lp ℝ 2 (mapEquivLaw ν T : Measure V₂)) :
    mapEquivForward ν T f =ᵐ[(ν : Measure V₁)] fun x ↦ f (T x) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_mapEquivLaw ν T)

theorem mapEquivBackward_mapEquivForward (f : Lp ℝ 2 (mapEquivLaw ν T : Measure V₂)) :
    mapEquivBackward ν T (mapEquivForward ν T f) = f := by
  change Lp.compMeasurePreserving T.symm (measurePreserving_mapEquivLaw_symm ν T)
    (Lp.compMeasurePreserving T (measurePreserving_mapEquivLaw ν T) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_mapEquivLaw ν T)
    (measurePreserving_mapEquivLaw_symm ν T)]
  apply Subtype.ext
  change f.1.compMeasurePreserving (⇑T ∘ ⇑T.symm)
    ((measurePreserving_mapEquivLaw ν T).comp (measurePreserving_mapEquivLaw_symm ν T)) = f.1
  have hae : (⇑T ∘ ⇑T.symm) =ᵐ[(mapEquivLaw ν T : Measure V₂)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

theorem mapEquivForward_mapEquivBackward (f : Lp ℝ 2 (ν : Measure V₁)) :
    mapEquivForward ν T (mapEquivBackward ν T f) = f := by
  change Lp.compMeasurePreserving T (measurePreserving_mapEquivLaw ν T)
    (Lp.compMeasurePreserving T.symm (measurePreserving_mapEquivLaw_symm ν T) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_mapEquivLaw_symm ν T)
    (measurePreserving_mapEquivLaw ν T)]
  apply Subtype.ext
  change f.1.compMeasurePreserving (⇑T.symm ∘ ⇑T)
    ((measurePreserving_mapEquivLaw_symm ν T).comp (measurePreserving_mapEquivLaw ν T)) = f.1
  have hae : (⇑T.symm ∘ ⇑T) =ᵐ[(ν : Measure V₁)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

/-- Pullback along `T` as a linear isometric equivalence of real `L²` spaces. -/
def mapEquivL2 : Lp ℝ 2 (mapEquivLaw ν T : Measure V₂) ≃ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V₁) where
  toFun := mapEquivForward ν T
  invFun := mapEquivBackward ν T
  left_inv := mapEquivBackward_mapEquivForward ν T
  right_inv := mapEquivForward_mapEquivBackward ν T
  map_add' := map_add (mapEquivForward ν T)
  map_smul' := map_smul (mapEquivForward ν T)
  norm_map' := norm_map (mapEquivForward ν T)

@[simp]
theorem mapEquivL2_apply (f : Lp ℝ 2 (mapEquivLaw ν T : Measure V₂)) :
    mapEquivL2 ν T f = mapEquivForward ν T f := rfl

@[simp]
theorem mapEquivL2_symm_apply (f : Lp ℝ 2 (ν : Measure V₁)) :
    (mapEquivL2 ν T).symm f = mapEquivBackward ν T f := rfl

/-- Pullback along `T` preserves the intrinsic `L²` variance. -/
theorem _root_.FunctionalInequalities.L2.variance_mapEquivL2
    (f : Lp ℝ 2 (mapEquivLaw ν T : Measure V₂)) :
    L2.variance ν (mapEquivL2 ν T f) = L2.variance (mapEquivLaw ν T) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, mapEquivL2_apply,
    ProbabilityTheory.variance_congr (mapEquivForward_coeFn ν T f)]
  exact (measurePreserving_mapEquivLaw ν T).variance_fun_comp
    (Lp.aestronglyMeasurable f).aemeasurable

/-- The barycenter of the image law is the image of the barycenter. -/
theorem integral_id_mapEquivLaw (hint : Integrable id (ν : Measure V₁)) :
    ∫ y, y ∂(mapEquivLaw ν T : Measure V₂) = T (∫ x, x ∂(ν : Measure V₁)) := by
  rw [coe_mapEquivLaw, integral_map T.continuous.measurable.aemeasurable
    continuous_id'.aestronglyMeasurable]
  have hint' : Integrable (fun x : V₁ ↦ x) (ν : Measure V₁) := hint
  exact (T : V₁ →L[ℝ] V₂).integral_comp_comm hint'

/-- The image law keeps a finite second moment. -/
theorem memLp_id_two_mapEquivLaw (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (mapEquivLaw ν T : Measure V₂) := by
  rw [coe_mapEquivLaw, memLp_map_measure_iff aestronglyMeasurable_id
    T.continuous.measurable.aemeasurable]
  exact (T : V₁ →L[ℝ] V₂).comp_memLp' h

end Law

section Tests

variable {ν₁ : ProbabilityMeasure V₁} {ν₂ : ProbabilityMeasure V₂} {T : V₁ ≃L[ℝ] V₂}

/-- Composition of a covariance test with a measure-preserving continuous linear equivalence
between two laws whose covariance quadratic forms correspond under the adjoint. -/
def CovarianceGradientTest.compContinuousLinearEquiv
    (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w))
    (g : CovarianceGradientTest ν₂) : CovarianceGradientTest ν₁ where
  toFun := fun x ↦ g (T x)
  lipschitz := by
    obtain ⟨K, hK⟩ := g.lipschitz
    exact ⟨K * ‖(T : V₁ →L[ℝ] V₂)‖₊, hK.comp (T : V₁ →L[ℝ] V₂).lipschitz⟩
  memLp_two := by
    have := g.memLp_two
    rw [← hmp.map_eq] at this
    exact (memLp_map_measure_iff (hmp.map_eq ▸ g.memLp_two.1) hmp.aemeasurable).mp this
  integrable := by
    have hdens : covarianceGradientDensity ν₁ (fun x ↦ g (T x)) =
        covarianceGradientDensity ν₂ g.toFun ∘ T := by
      funext x
      simp only [covarianceGradientDensity, Function.comp_apply,
        gradient_comp_continuousLinearEquiv, hcov]
    rw [hdens]
    have := g.integrable
    rw [← hmp.map_eq] at this
    exact (integrable_map_measure (hmp.map_eq ▸ g.integrable.1) hmp.aemeasurable).mp this

/-- The composed test has the same covariance energy. -/
theorem CovarianceGradientTest.covarianceEnergy_compContinuousLinearEquiv
    (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w))
    (g : CovarianceGradientTest ν₂) :
    (g.compContinuousLinearEquiv hmp hcov).covarianceEnergy = g.covarianceEnergy := by
  apply NNReal.eq
  simp only [CovarianceGradientTest.coe_covarianceEnergy]
  have hdens : covarianceGradientDensity ν₁ (g.compContinuousLinearEquiv hmp hcov).toFun =
      covarianceGradientDensity ν₂ g.toFun ∘ T := by
    funext x
    simp only [CovarianceGradientTest.compContinuousLinearEquiv, covarianceGradientDensity,
      Function.comp_apply, gradient_comp_continuousLinearEquiv, hcov]
  rw [hdens, ← hmp.map_eq, integral_map hmp.aemeasurable (hmp.map_eq ▸ g.integrable.1)]
  rfl

/-- The composed test realizes the pullback of the original class. -/
theorem CovarianceGradientTest.toL2_compContinuousLinearEquiv
    (hmp : MeasurePreserving T (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w))
    (g : CovarianceGradientTest ν₂) :
    (g.compContinuousLinearEquiv hmp hcov).toL2 = Lp.compMeasurePreserving T hmp g.toL2 := by
  apply Lp.ext
  refine (g.compContinuousLinearEquiv hmp hcov).toL2_coeFn.trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving g.toL2 hmp).symm
  exact hmp.quasiMeasurePreserving.ae_eq_comp g.toL2_coeFn.symm

end Tests

section Relaxation

variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)

/-- The covariance relaxation of the image law is the covariance relaxation of `ν` pulled back
along `T`. -/
theorem covarianceRelaxation_mapEquivLaw (f : Lp ℝ 2 (mapEquivLaw ν T : Measure V₂)) :
    covarianceRelaxation (mapEquivLaw ν T) f = covarianceRelaxation ν (mapEquivL2 ν T f) := by
  have hcov : ∀ w, inner ℝ (Covariance.operator (mapEquivLaw ν T : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w) :=
    Covariance.inner_operator_mapEquivLaw ν T
  have hcov' : ∀ w, inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (Covariance.operator (mapEquivLaw ν T : Measure V₂)
        ((T.symm : V₂ →L[ℝ] V₁).adjoint w)) ((T.symm : V₂ →L[ℝ] V₁).adjoint w) :=
    Covariance.inner_operator_mapEquivLaw_symm ν T
  apply le_antisymm
  · have h := (covariancePreEnergy ν).sequentialRelaxation_comp_le
      (covariancePreEnergy (mapEquivLaw ν T)) (mapEquivBackward ν T)
      (mapEquivBackward ν T).continuous ?_ (mapEquivL2 ν T f)
    · rw [mapEquivL2_apply, mapEquivBackward_mapEquivForward] at h
      exact h
    · intro g
      refine ⟨g.compContinuousLinearEquiv (measurePreserving_mapEquivLaw_symm ν T) hcov', ?_,
        le_of_eq ?_⟩
      · exact g.toL2_compContinuousLinearEquiv _ _
      · exact g.covarianceEnergy_compContinuousLinearEquiv _ _
  · have h := (covariancePreEnergy (mapEquivLaw ν T)).sequentialRelaxation_comp_le
      (covariancePreEnergy ν) (mapEquivForward ν T) (mapEquivForward ν T).continuous ?_ f
    · exact h
    · intro g
      refine ⟨g.compContinuousLinearEquiv (measurePreserving_mapEquivLaw ν T) hcov, ?_,
        le_of_eq ?_⟩
      · exact g.toL2_compContinuousLinearEquiv _ _
      · exact g.covarianceEnergy_compContinuousLinearEquiv _ _

/-- The optimal `L²` Poincaré constant of the covariance relaxation is invariant under continuous
linear equivalences. -/
theorem _root_.FunctionalInequalities.Poincare.L2Energy.constant_covarianceRelaxation_mapEquivLaw :
    Poincare.L2Energy.constant (mapEquivLaw ν T) (covarianceRelaxation (mapEquivLaw ν T)) =
      Poincare.L2Energy.constant ν (covarianceRelaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv ν (mapEquivLaw ν T)
    (covarianceRelaxation ν) (covarianceRelaxation (mapEquivLaw ν T)) (mapEquivL2 ν T)
    (L2.variance_mapEquivL2 ν T) (covarianceRelaxation_mapEquivLaw ν T)

end Relaxation

end FunctionalInequalities.Energy.Euclidean

namespace FunctionalInequalities.Probability

open Energy.Euclidean

universe u v

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)

/-- The affine support of the image law is the image of the affine support. -/
theorem affineSupport_mapEquivLaw :
    affineSupport (mapEquivLaw ν T) = (affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap := by
  apply le_antisymm
  · apply affineSupport_le_of_ae_mem
    · exact ((affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap).closed_of_finiteDimensional
    · rw [coe_mapEquivLaw]
      refine (ae_map_iff T.continuous.measurable.aemeasurable
        ((affineSupport ν).map
          (T : V₁ →ₗ[ℝ] V₂).toAffineMap).closed_of_finiteDimensional.measurableSet).2 ?_
      filter_upwards [ae_mem_affineSupport ν] with x hx
      exact ⟨x, hx, rfl⟩
  · rw [AffineSubspace.map_le_iff_le_comap]
    apply affineSupport_le_of_ae_mem
    · change IsClosed ((fun x : V₁ ↦ T x) ⁻¹' (affineSupport (mapEquivLaw ν T) : Set V₂))
      exact (isClosed_affineSupport _).preimage T.continuous
    · have h := ae_mem_affineSupport (mapEquivLaw ν T)
      rw [coe_mapEquivLaw] at h
      filter_upwards [ae_of_ae_map T.continuous.measurable.aemeasurable h] with x hx
      exact hx

/-- A full affine support stays full under a continuous linear equivalence. -/
theorem affineSupport_mapEquivLaw_eq_top (h : affineSupport ν = ⊤) :
    affineSupport (mapEquivLaw ν T) = ⊤ := by
  rw [affineSupport_mapEquivLaw, h]
  exact AffineMap.map_top_of_surjective _ T.surjective

end FunctionalInequalities.Probability

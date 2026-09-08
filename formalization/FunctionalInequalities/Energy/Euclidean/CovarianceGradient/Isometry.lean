import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Translation
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Isometric transport of the covariance relaxation

Source: Blueprint `lem:affine-poincare-translation-invariance`, the sentence "translation preserves
covariance and identifies the two intrinsic laws by an `L²` isometry". Read `mapLaw`,
`Covariance.operator_mapLaw`, `gradient_comp_linearIsometryEquiv`, `mapL2`, `L2.variance_mapL2`,
`covarianceRelaxation_mapLaw` and `L2Energy.constant_covarianceRelaxation_mapLaw`.

For a probability law `ν` on a finite-dimensional Euclidean space `V₁` and a linear isometric
equivalence `L : V₁ ≃ₗᵢ[ℝ] V₂`, the image law `mapLaw ν L` lives on `V₂`. Its covariance operator
is the conjugate `L ∘ Σ ∘ L⁻¹` of the covariance operator `Σ` of `ν`; the gradient of `g ∘ L` is
`L⁻¹ ∇g ∘ L`; composition with `L` is a linear isometric equivalence `L²(mapLaw ν L) ≃ L²(ν)`
preserving variance; globally Lipschitz covariance tests correspond by composition with equal
covariance energies; hence the covariance relaxations correspond under the isometry and the optimal
`L²` Poincaré constants of the two relaxations coincide.

Together with `CovarianceGradient/Translation.lean` this covers every affine isometric change of
intrinsic coordinates, in two steps: a linear isometric equivalence of the direction spaces followed
by a translation. Everything holds for every Borel probability law; no log-concavity, density or
closability is used, and no Poincaré inequality is asserted. The zero-dimensional spaces are
included.
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

/-- The gradient of a function composed with a linear isometric equivalence is the inverse image
of the gradient at the image point. No differentiability premise is needed: both sides vanish
simultaneously at points of nondifferentiability. -/
theorem gradient_comp_linearIsometryEquiv (g : V₂ → ℝ) (L : V₁ ≃ₗᵢ[ℝ] V₂) (x : V₁) :
    gradient (fun y ↦ g (L y)) x = L.symm (gradient g (L x)) := by
  apply (toDual ℝ V₁).injective
  rw [toDual_gradient]
  have hcomp : fderiv ℝ (fun y ↦ g (L y)) x =
      (fderiv ℝ g (L x)).comp (L.toContinuousLinearEquiv : V₁ →L[ℝ] V₂) := by
    have h := L.toContinuousLinearEquiv.comp_right_fderiv (f := g) (x := x)
    simpa only [Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h
  rw [hcomp]
  ext v
  change fderiv ℝ g (L x) (L.toContinuousLinearEquiv v) = inner ℝ (L.symm (gradient g (L x))) v
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ← toDual_gradient, toDual_apply_apply]
  calc inner ℝ (gradient g (L x)) (L v)
      = inner ℝ (L (L.symm (gradient g (L x)))) (L v) := by rw [L.apply_symm_apply]
    _ = inner ℝ (L.symm (gradient g (L x))) v := L.inner_map_map _ _

end Gradient

section Covariance

/-- Without a finite second moment Mathlib's covariance operator is zero. -/
theorem _root_.FunctionalInequalities.Covariance.operator_of_not_memLp {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] (m : Measure W) (hm : ¬ MemLp id 2 m) : Covariance.operator m = 0 := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [Covariance.operator_inner, ProbabilityTheory.covarianceBilin_of_not_memLp hm]
  simp

/-- Pushing a law forward along a linear isometric equivalence conjugates its covariance operator.
Without a second moment both operators are zero. -/
theorem _root_.FunctionalInequalities.Covariance.operator_map_linearIsometryEquiv
    (ν : Measure V₁) [IsFiniteMeasure ν] (L : V₁ ≃ₗᵢ[ℝ] V₂) :
    Covariance.operator (ν.map L) =
      ((L : V₁ →L[ℝ] V₂).comp (Covariance.operator ν)).comp (L.symm : V₂ →L[ℝ] V₁) := by
  have hcoe : ⇑(L : V₁ →L[ℝ] V₂) = ⇑L := rfl
  by_cases h : MemLp id 2 ν
  · ext u
    apply ext_inner_right ℝ
    intro v
    rw [Covariance.operator_inner, ← hcoe, ProbabilityTheory.covarianceBilin_map h (L : V₁ →L[ℝ] V₂),
      LinearIsometryEquiv.adjoint_eq_symm, ← Covariance.operator_inner]
    simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'']
    rw [← L.inner_map_map (Covariance.operator ν (L.symm u)) (L.symm v), L.apply_symm_apply]
  · have h' : ¬ MemLp id 2 (ν.map L) := by
      intro h'
      apply h
      have h1 : MemLp (fun x ↦ L x) 2 ν :=
        (memLp_map_measure_iff aestronglyMeasurable_id L.continuous.measurable.aemeasurable).mp h'
      have h2 := (L.symm : V₂ →L[ℝ] V₁).comp_memLp' h1
      have h3 : (⇑(L.symm : V₂ →L[ℝ] V₁) ∘ fun x ↦ L x) = id := by
        funext x
        simp
      rwa [h3] at h2
    rw [Covariance.operator_of_not_memLp ν h, Covariance.operator_of_not_memLp (ν.map L) h']
    simp

end Covariance

section Law

variable (ν : ProbabilityMeasure V₁) (L : V₁ ≃ₗᵢ[ℝ] V₂)

/-- The image of `ν` under the linear isometric equivalence `L`. -/
def mapLaw : ProbabilityMeasure V₂ :=
  ν.map L.continuous.measurable.aemeasurable

theorem coe_mapLaw : (mapLaw ν L : Measure V₂) = (ν : Measure V₁).map L := rfl

/-- `L` is measure preserving from `ν` to its image law. -/
theorem measurePreserving_mapLaw :
    MeasurePreserving L (ν : Measure V₁) (mapLaw ν L : Measure V₂) :=
  ⟨L.continuous.measurable, rfl⟩

/-- `L⁻¹` is measure preserving from the image law back to `ν`. -/
theorem measurePreserving_mapLaw_symm :
    MeasurePreserving L.symm (mapLaw ν L : Measure V₂) (ν : Measure V₁) := by
  refine ⟨L.symm.continuous.measurable, ?_⟩
  rw [coe_mapLaw, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
  have : (⇑L.symm ∘ ⇑L) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

/-- The covariance operator of the image law is the conjugate of the covariance operator of `ν`. -/
theorem _root_.FunctionalInequalities.Covariance.operator_mapLaw :
    Covariance.operator (mapLaw ν L : Measure V₂) =
      ((L : V₁ →L[ℝ] V₂).comp (Covariance.operator (ν : Measure V₁))).comp (L.symm : V₂ →L[ℝ] V₁) :=
  Covariance.operator_map_linearIsometryEquiv (ν : Measure V₁) L

/-- The covariance quadratic form of the image law, read through `L⁻¹`. -/
theorem _root_.FunctionalInequalities.Covariance.inner_operator_mapLaw (w : V₂) :
    inner ℝ (Covariance.operator (mapLaw ν L : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν : Measure V₁) (L.symm w)) (L.symm w) := by
  rw [Covariance.operator_mapLaw]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'']
  rw [← L.inner_map_map (Covariance.operator (ν : Measure V₁) (L.symm w)) (L.symm w),
    L.apply_symm_apply]

/-- The covariance quadratic form of `ν`, read through `L`. -/
theorem _root_.FunctionalInequalities.Covariance.inner_operator_mapLaw_apply (w : V₁) :
    inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (Covariance.operator (mapLaw ν L : Measure V₂) (L w)) (L w) := by
  rw [Covariance.inner_operator_mapLaw, L.symm_apply_apply]

/-- Pullback of `L²` classes along `L`. -/
def mapForward : Lp ℝ 2 (mapLaw ν L : Measure V₂) →ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V₁) :=
  Lp.compMeasurePreservingₗᵢ ℝ L (measurePreserving_mapLaw ν L)

/-- Pullback of `L²` classes along `L⁻¹`. -/
def mapBackward : Lp ℝ 2 (ν : Measure V₁) →ₗᵢ[ℝ] Lp ℝ 2 (mapLaw ν L : Measure V₂) :=
  Lp.compMeasurePreservingₗᵢ ℝ L.symm (measurePreserving_mapLaw_symm ν L)

theorem mapForward_coeFn (f : Lp ℝ 2 (mapLaw ν L : Measure V₂)) :
    mapForward ν L f =ᵐ[(ν : Measure V₁)] fun x ↦ f (L x) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_mapLaw ν L)

theorem mapBackward_mapForward (f : Lp ℝ 2 (mapLaw ν L : Measure V₂)) :
    mapBackward ν L (mapForward ν L f) = f := by
  change Lp.compMeasurePreserving L.symm (measurePreserving_mapLaw_symm ν L)
    (Lp.compMeasurePreserving L (measurePreserving_mapLaw ν L) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_mapLaw ν L)
    (measurePreserving_mapLaw_symm ν L)]
  apply Subtype.ext
  change f.1.compMeasurePreserving (⇑L ∘ ⇑L.symm)
    ((measurePreserving_mapLaw ν L).comp (measurePreserving_mapLaw_symm ν L)) = f.1
  have hae : (⇑L ∘ ⇑L.symm) =ᵐ[(mapLaw ν L : Measure V₂)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

theorem mapForward_mapBackward (f : Lp ℝ 2 (ν : Measure V₁)) :
    mapForward ν L (mapBackward ν L f) = f := by
  change Lp.compMeasurePreserving L (measurePreserving_mapLaw ν L)
    (Lp.compMeasurePreserving L.symm (measurePreserving_mapLaw_symm ν L) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_mapLaw_symm ν L)
    (measurePreserving_mapLaw ν L)]
  apply Subtype.ext
  change f.1.compMeasurePreserving (⇑L.symm ∘ ⇑L)
    ((measurePreserving_mapLaw_symm ν L).comp (measurePreserving_mapLaw ν L)) = f.1
  have hae : (⇑L.symm ∘ ⇑L) =ᵐ[(ν : Measure V₁)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

/-- Pullback along `L` as a linear isometric equivalence of real `L²` spaces. -/
def mapL2 : Lp ℝ 2 (mapLaw ν L : Measure V₂) ≃ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V₁) where
  toFun := mapForward ν L
  invFun := mapBackward ν L
  left_inv := mapBackward_mapForward ν L
  right_inv := mapForward_mapBackward ν L
  map_add' := map_add (mapForward ν L)
  map_smul' := map_smul (mapForward ν L)
  norm_map' := norm_map (mapForward ν L)

@[simp]
theorem mapL2_apply (f : Lp ℝ 2 (mapLaw ν L : Measure V₂)) :
    mapL2 ν L f = mapForward ν L f := rfl

@[simp]
theorem mapL2_symm_apply (f : Lp ℝ 2 (ν : Measure V₁)) :
    (mapL2 ν L).symm f = mapBackward ν L f := rfl

/-- Pullback along `L` preserves the intrinsic `L²` variance. -/
theorem _root_.FunctionalInequalities.L2.variance_mapL2 (f : Lp ℝ 2 (mapLaw ν L : Measure V₂)) :
    L2.variance ν (mapL2 ν L f) = L2.variance (mapLaw ν L) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, mapL2_apply,
    ProbabilityTheory.variance_congr (mapForward_coeFn ν L f)]
  exact (measurePreserving_mapLaw ν L).variance_fun_comp (Lp.aestronglyMeasurable f).aemeasurable

end Law

section Tests

variable {ν₁ : ProbabilityMeasure V₁} {ν₂ : ProbabilityMeasure V₂} {L : V₁ ≃ₗᵢ[ℝ] V₂}

/-- Composition of a covariance test with a measure-preserving linear isometric equivalence
between two laws whose covariance quadratic forms correspond under `L`. -/
def CovarianceGradientTest.compLinearIsometryEquiv
    (hmp : MeasurePreserving L (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) (L.symm w)) (L.symm w))
    (g : CovarianceGradientTest ν₂) : CovarianceGradientTest ν₁ where
  toFun := fun x ↦ g (L x)
  lipschitz := by
    obtain ⟨K, hK⟩ := g.lipschitz
    exact ⟨K * 1, hK.comp L.lipschitz⟩
  memLp_two := by
    have := g.memLp_two
    rw [← hmp.map_eq] at this
    exact (memLp_map_measure_iff (hmp.map_eq ▸ g.memLp_two.1) hmp.aemeasurable).mp this
  integrable := by
    have hdens : covarianceGradientDensity ν₁ (fun x ↦ g (L x)) =
        covarianceGradientDensity ν₂ g.toFun ∘ L := by
      funext x
      simp only [covarianceGradientDensity, Function.comp_apply,
        gradient_comp_linearIsometryEquiv, hcov]
    rw [hdens]
    have := g.integrable
    rw [← hmp.map_eq] at this
    exact (integrable_map_measure (hmp.map_eq ▸ g.integrable.1) hmp.aemeasurable).mp this

/-- The composed test has the same covariance energy. -/
theorem CovarianceGradientTest.covarianceEnergy_compLinearIsometryEquiv
    (hmp : MeasurePreserving L (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) (L.symm w)) (L.symm w))
    (g : CovarianceGradientTest ν₂) :
    (g.compLinearIsometryEquiv hmp hcov).covarianceEnergy = g.covarianceEnergy := by
  apply NNReal.eq
  simp only [CovarianceGradientTest.coe_covarianceEnergy]
  have hdens : covarianceGradientDensity ν₁ (g.compLinearIsometryEquiv hmp hcov).toFun =
      covarianceGradientDensity ν₂ g.toFun ∘ L := by
    funext x
    simp only [CovarianceGradientTest.compLinearIsometryEquiv, covarianceGradientDensity,
      Function.comp_apply, gradient_comp_linearIsometryEquiv, hcov]
  rw [hdens, ← hmp.map_eq, integral_map hmp.aemeasurable (hmp.map_eq ▸ g.integrable.1)]
  rfl

/-- The composed test realizes the pullback of the original class. -/
theorem CovarianceGradientTest.toL2_compLinearIsometryEquiv
    (hmp : MeasurePreserving L (ν₁ : Measure V₁) (ν₂ : Measure V₂))
    (hcov : ∀ w, inner ℝ (Covariance.operator (ν₂ : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν₁ : Measure V₁) (L.symm w)) (L.symm w))
    (g : CovarianceGradientTest ν₂) :
    (g.compLinearIsometryEquiv hmp hcov).toL2 = Lp.compMeasurePreserving L hmp g.toL2 := by
  apply Lp.ext
  refine (g.compLinearIsometryEquiv hmp hcov).toL2_coeFn.trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving g.toL2 hmp).symm
  exact hmp.quasiMeasurePreserving.ae_eq_comp g.toL2_coeFn.symm

end Tests

section Relaxation

variable (ν : ProbabilityMeasure V₁) (L : V₁ ≃ₗᵢ[ℝ] V₂)

/-- The covariance relaxation of the image law is the covariance relaxation of `ν` pulled back
along `L`. -/
theorem covarianceRelaxation_mapLaw (f : Lp ℝ 2 (mapLaw ν L : Measure V₂)) :
    covarianceRelaxation (mapLaw ν L) f = covarianceRelaxation ν (mapL2 ν L f) := by
  have hcov : ∀ w, inner ℝ (Covariance.operator (mapLaw ν L : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν : Measure V₁) (L.symm w)) (L.symm w) :=
    Covariance.inner_operator_mapLaw ν L
  have hcov' : ∀ w, inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (Covariance.operator (mapLaw ν L : Measure V₂) (L.symm.symm w)) (L.symm.symm w) := by
    intro w
    rw [LinearIsometryEquiv.symm_symm]
    exact Covariance.inner_operator_mapLaw_apply ν L w
  apply le_antisymm
  · have h := (covariancePreEnergy ν).sequentialRelaxation_comp_le
      (covariancePreEnergy (mapLaw ν L)) (mapBackward ν L)
      (mapBackward ν L).continuous ?_ (mapL2 ν L f)
    · rw [mapL2_apply, mapBackward_mapForward] at h
      exact h
    · intro g
      refine ⟨g.compLinearIsometryEquiv (measurePreserving_mapLaw_symm ν L) hcov', ?_, le_of_eq ?_⟩
      · exact g.toL2_compLinearIsometryEquiv _ _
      · exact g.covarianceEnergy_compLinearIsometryEquiv _ _
  · have h := (covariancePreEnergy (mapLaw ν L)).sequentialRelaxation_comp_le
      (covariancePreEnergy ν) (mapForward ν L) (mapForward ν L).continuous ?_ f
    · exact h
    · intro g
      refine ⟨g.compLinearIsometryEquiv (measurePreserving_mapLaw ν L) hcov, ?_, le_of_eq ?_⟩
      · exact g.toL2_compLinearIsometryEquiv _ _
      · exact g.covarianceEnergy_compLinearIsometryEquiv _ _

/-- The optimal `L²` Poincaré constant of the covariance relaxation is invariant under linear
isometric equivalences. -/
theorem _root_.FunctionalInequalities.Poincare.L2Energy.constant_covarianceRelaxation_mapLaw :
    Poincare.L2Energy.constant (mapLaw ν L) (covarianceRelaxation (mapLaw ν L)) =
      Poincare.L2Energy.constant ν (covarianceRelaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv ν (mapLaw ν L)
    (covarianceRelaxation ν) (covarianceRelaxation (mapLaw ν L)) (mapL2 ν L)
    (L2.variance_mapL2 ν L) (covarianceRelaxation_mapLaw ν L)

end Relaxation

end FunctionalInequalities.Energy.Euclidean

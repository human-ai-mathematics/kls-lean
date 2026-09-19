import FunctionalInequalities.Probability.Covariance.Basic
import FunctionalInequalities.Probability.AffineSupport
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Pushforwards by translations and linear equivalences

The law is pushed forward in the direction of the underlying map. Covariance and moment
identities are statements about that probability law. L² pullbacks are in `L2.Transport`.
-/

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace

namespace FunctionalInequalities

universe u v

section Translation

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable (ν : ProbabilityMeasure V) (c : V)

/-- The image of `ν` under the translation `x ↦ c + x`. -/
def Probability.translateLaw : ProbabilityMeasure V :=
  ν.map (measurable_const_add c).aemeasurable

omit [InnerProductSpace ℝ V] in
theorem Probability.coe_translateLaw :
    (Probability.translateLaw ν c : Measure V) = (ν : Measure V).map (fun x ↦ c + x) := rfl

omit [InnerProductSpace ℝ V] in
/-- The translation is measure preserving from `ν` to the translated law. -/
theorem Probability.measurePreserving_translate :
    MeasurePreserving (fun x ↦ c + x) (ν : Measure V) (Probability.translateLaw ν c : Measure V) :=
  ⟨measurable_const_add c, rfl⟩

omit [InnerProductSpace ℝ V] in
/-- The inverse translation is measure preserving from the translated law back to `ν`. -/
theorem Probability.measurePreserving_translate_symm :
    MeasurePreserving (fun x ↦ -c + x) (Probability.translateLaw ν c : Measure V) (ν : Measure V) := by
  refine ⟨measurable_const_add _, ?_⟩
  rw [Probability.coe_translateLaw, Measure.map_map (measurable_const_add _) (measurable_const_add _)]
  have : ((fun x ↦ -c + x) ∘ fun x ↦ c + x) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

variable [CompleteSpace V]

/-- Translation does not change the covariance operator. -/
theorem Covariance.operator_translateLaw :
    Covariance.operator (Probability.translateLaw ν c : Measure V) = Covariance.operator (ν : Measure V) := by
  unfold Covariance.operator
  rw [Probability.coe_translateLaw, ProbabilityTheory.covarianceBilin_map_const_add]

end Translation

section LinearIsometry

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]

variable (ν : ProbabilityMeasure V₁) (L : V₁ ≃ₗᵢ[ℝ] V₂)

/-- The image of `ν` under the linear isometric equivalence `L`. -/
def Probability.mapLinearIsometryEquiv : ProbabilityMeasure V₂ :=
  ν.map L.continuous.measurable.aemeasurable

theorem Probability.coe_mapLinearIsometryEquiv : (Probability.mapLinearIsometryEquiv ν L : Measure V₂) = (ν : Measure V₁).map L := rfl

/-- `L` is measure preserving from `ν` to its image law. -/
theorem Probability.measurePreserving_mapLinearIsometryEquiv :
    MeasurePreserving L (ν : Measure V₁) (Probability.mapLinearIsometryEquiv ν L : Measure V₂) :=
  ⟨L.continuous.measurable, rfl⟩

/-- `L⁻¹` is measure preserving from the image law back to `ν`. -/
theorem Probability.measurePreserving_mapLinearIsometryEquiv_symm :
    MeasurePreserving L.symm (Probability.mapLinearIsometryEquiv ν L : Measure V₂) (ν : Measure V₁) := by
  refine ⟨L.symm.continuous.measurable, ?_⟩
  rw [Probability.coe_mapLinearIsometryEquiv, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
  have : (⇑L.symm ∘ ⇑L) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]

/-- Without a finite second moment Mathlib's covariance operator is zero. -/
theorem Covariance.operator_of_not_memLp {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] (m : Measure W) (hm : ¬ MemLp id 2 m) : Covariance.operator m = 0 := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [Covariance.operator_inner, ProbabilityTheory.covarianceBilin_of_not_memLp hm]
  simp

omit [SecondCountableTopology V₁] in
/-- Pushing a law forward along a linear isometric equivalence conjugates its covariance operator.
Without a second moment both operators are zero. -/
theorem Covariance.operator_map_linearIsometryEquiv
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

omit [SecondCountableTopology V₁] in
/-- The covariance operator of the image law is the conjugate of the covariance operator of `ν`. -/
theorem Covariance.operator_mapLinearIsometryEquiv :
    Covariance.operator (Probability.mapLinearIsometryEquiv ν L : Measure V₂) =
      ((L : V₁ →L[ℝ] V₂).comp (Covariance.operator (ν : Measure V₁))).comp (L.symm : V₂ →L[ℝ] V₁) :=
  Covariance.operator_map_linearIsometryEquiv (ν : Measure V₁) L

omit [SecondCountableTopology V₁] in
/-- The covariance quadratic form of the image law, read through `L⁻¹`. -/
theorem Covariance.inner_operator_mapLinearIsometryEquiv (w : V₂) :
    inner ℝ (Covariance.operator (Probability.mapLinearIsometryEquiv ν L : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν : Measure V₁) (L.symm w)) (L.symm w) := by
  rw [Covariance.operator_mapLinearIsometryEquiv]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'']
  rw [← L.inner_map_map (Covariance.operator (ν : Measure V₁) (L.symm w)) (L.symm w),
    L.apply_symm_apply]

omit [SecondCountableTopology V₁] in
/-- The covariance quadratic form of `ν`, read through `L`. -/
theorem Covariance.inner_operator_mapLinearIsometryEquiv_apply (w : V₁) :
    inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (Covariance.operator (Probability.mapLinearIsometryEquiv ν L : Measure V₂) (L w)) (L w) := by
  rw [Covariance.inner_operator_mapLinearIsometryEquiv, L.symm_apply_apply]

end LinearIsometry

section ContinuousLinearEquiv

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]

variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)

/-- The image of `ν` under the continuous linear equivalence `T`. -/
def Probability.mapContinuousLinearEquiv : ProbabilityMeasure V₂ :=
  ν.map T.continuous.measurable.aemeasurable

theorem Probability.coe_mapContinuousLinearEquiv : (Probability.mapContinuousLinearEquiv ν T : Measure V₂) = (ν : Measure V₁).map T := rfl

/-- `T` is measure preserving from `ν` to its image law. -/
theorem Probability.measurePreserving_mapContinuousLinearEquiv :
    MeasurePreserving T (ν : Measure V₁) (Probability.mapContinuousLinearEquiv ν T : Measure V₂) :=
  ⟨T.continuous.measurable, rfl⟩

/-- `T⁻¹` is measure preserving from the image law back to `ν`. -/
theorem Probability.measurePreserving_mapContinuousLinearEquiv_symm :
    MeasurePreserving T.symm (Probability.mapContinuousLinearEquiv ν T : Measure V₂) (ν : Measure V₁) := by
  refine ⟨T.symm.continuous.measurable, ?_⟩
  rw [Probability.coe_mapContinuousLinearEquiv, Measure.map_map T.symm.continuous.measurable T.continuous.measurable]
  have : (⇑T.symm ∘ ⇑T) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]

omit [SecondCountableTopology V₁] in
/-- Pushing a law forward along a continuous linear equivalence conjugates its covariance operator
by the map and its adjoint. Without a second moment both operators are zero. -/
theorem Covariance.operator_map_continuousLinearEquiv
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

omit [SecondCountableTopology V₁] in
/-- The covariance operator of the image law. -/
theorem Covariance.operator_mapContinuousLinearEquiv :
    Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator (ν : Measure V₁))).comp
        (T : V₁ →L[ℝ] V₂).adjoint :=
  Covariance.operator_map_continuousLinearEquiv (ν : Measure V₁) T

omit [SecondCountableTopology V₁] in
/-- The covariance quadratic form of the image law, read through the adjoint. -/
theorem Covariance.inner_operator_mapContinuousLinearEquiv (w : V₂) :
    inner ℝ (Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w) := by
  rw [Covariance.operator_mapContinuousLinearEquiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_right (T : V₁ →L[ℝ] V₂) _ w).symm

omit [SecondCountableTopology V₁] in
/-- The covariance quadratic form of `ν`, read through the adjoint of the inverse. -/
theorem Covariance.inner_operator_mapContinuousLinearEquiv_symm (w : V₁) :
    inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂)
        ((T.symm : V₂ →L[ℝ] V₁).adjoint w)) ((T.symm : V₂ →L[ℝ] V₁).adjoint w) := by
  rw [Covariance.inner_operator_mapContinuousLinearEquiv]
  have hT : (T : V₁ →L[ℝ] V₂).adjoint ((T.symm : V₂ →L[ℝ] V₁).adjoint w) = w := by
    have hcomp : (T.symm : V₂ →L[ℝ] V₁).comp (T : V₁ →L[ℝ] V₂) = ContinuousLinearMap.id ℝ V₁ := by
      ext x
      simp
    have := congrArg (fun A : V₁ →L[ℝ] V₁ ↦ A.adjoint w) hcomp
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] using this
  rw [hT]

omit [SecondCountableTopology V₁] in
/-- The barycenter of the image law is the image of the barycenter. -/
theorem Probability.integral_id_mapContinuousLinearEquiv (hint : Integrable id (ν : Measure V₁)) :
    ∫ y, y ∂(Probability.mapContinuousLinearEquiv ν T : Measure V₂) = T (∫ x, x ∂(ν : Measure V₁)) := by
  rw [Probability.coe_mapContinuousLinearEquiv, integral_map T.continuous.measurable.aemeasurable
    continuous_id'.aestronglyMeasurable]
  have hint' : Integrable (fun x : V₁ ↦ x) (ν : Measure V₁) := hint
  exact (T : V₁ →L[ℝ] V₂).integral_comp_comm hint'

omit [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] in
/-- The image law keeps a finite second moment. -/
theorem Probability.memLp_id_two_mapContinuousLinearEquiv (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) := by
  rw [Probability.coe_mapContinuousLinearEquiv, memLp_map_measure_iff aestronglyMeasurable_id
    T.continuous.measurable.aemeasurable]
  exact (T : V₁ →L[ℝ] V₂).comp_memLp' h

variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]

omit [CompleteSpace V₁] [CompleteSpace V₂] [FiniteDimensional ℝ V₁] in
/-- The affine support of the image law is the image of the affine support. -/
theorem Probability.affineSupport_mapContinuousLinearEquiv :
    affineSupport (mapContinuousLinearEquiv ν T) = (affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap := by
  apply le_antisymm
  · apply affineSupport_le_of_ae_mem
    · exact ((affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap).closed_of_finiteDimensional
    · rw [coe_mapContinuousLinearEquiv]
      refine (ae_map_iff T.continuous.measurable.aemeasurable
        ((affineSupport ν).map
          (T : V₁ →ₗ[ℝ] V₂).toAffineMap).closed_of_finiteDimensional.measurableSet).2 ?_
      filter_upwards [ae_mem_affineSupport ν] with x hx
      exact ⟨x, hx, rfl⟩
  · rw [AffineSubspace.map_le_iff_le_comap]
    apply affineSupport_le_of_ae_mem
    · change IsClosed ((fun x : V₁ ↦ T x) ⁻¹' (affineSupport (mapContinuousLinearEquiv ν T) : Set V₂))
      exact (isClosed_affineSupport _).preimage T.continuous
    · have h := ae_mem_affineSupport (mapContinuousLinearEquiv ν T)
      rw [coe_mapContinuousLinearEquiv] at h
      filter_upwards [ae_of_ae_map T.continuous.measurable.aemeasurable h] with x hx
      exact hx

omit [CompleteSpace V₁] [CompleteSpace V₂] [FiniteDimensional ℝ V₁] in
/-- A full affine support stays full under a continuous linear equivalence. -/
theorem Probability.affineSupport_mapContinuousLinearEquiv_eq_top (h : affineSupport ν = ⊤) :
    affineSupport (mapContinuousLinearEquiv ν T) = ⊤ := by
  rw [affineSupport_mapContinuousLinearEquiv, h]
  exact AffineMap.map_top_of_surjective _ T.surjective

end ContinuousLinearEquiv

end FunctionalInequalities

import FunctionalInequalities.KLS.LogConcave.Regular.Isotropic
import FunctionalInequalities.KLS.BKL.GaussianTaylor
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Audit: centering and whitening of regular laws (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5 (reduction of Theorem 1.1 to
isotropic regular laws). Clients: the scaled and translated Gaussian potential `‖2x+3‖²/2` on `ℝ` is
regular with mean `−3/2` and covariance `1/4`; the producer yields an explicit isotropic regular law
with the predicted whitened potential and image law; the zero-dimensional case keeps positive
constants and full support. No whitening operator is chosen in the library; the approximation
theorem is not asserted.
-/

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace RegularIsotropicAudit

noncomputable def scaleTwo : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.equivOfInverse ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    (by intro x; simp) (by intro x; simp)

private theorem scaleTwo_apply (x : ℝ) : scaleTwo x = 2 * x := rfl
private theorem scaleTwo_symm_apply (x : ℝ) : scaleTwo.symm x = x / 2 := by
  change (1 / 2 : ℝ) * x = x / 2
  ring

private theorem scaleTwo_adjoint : (scaleTwo : ℝ →L[ℝ] ℝ).adjoint = scaleTwo := by
  change ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).adjoint =
    (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  simp [ContinuousLinearMap.adjoint_id]

private theorem scaleTwo_symm_adjoint : (scaleTwo.symm : ℝ →L[ℝ] ℝ).adjoint = scaleTwo.symm := by
  change ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).adjoint =
    (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  simp [ContinuousLinearMap.adjoint_id]

theorem gaussianRegular : KLS.RegularPotential (fun x : ℝ => ‖x‖ ^ 2 / 2) 1 1 :=
  KLS.regularPotential_half_norm_sq

private theorem gaussian_mean : ∫ x, x ∂(gaussianRegular.law : Measure ℝ) = 0 :=
  KLS.integral_id_tilted_half_norm_sq

private theorem gaussian_second : ∫ x, x ^ 2 ∂(gaussianRegular.law : Measure ℝ) = 1 := by
  have h := KLS.integral_inner_sq_tilted_half_norm_sq (E := ℝ) 1
  change (∫ x : ℝ, x ^ 2 ∂((volume : Measure ℝ).tilted (-fun x : ℝ => ‖x‖ ^ 2 / 2))) = 1
  simpa using h

private theorem gaussian_covariance :
    Covariance.operator (gaussianRegular.law : Measure ℝ) = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [Covariance.operator_inner, ProbabilityTheory.covarianceBilin_apply (KLS.RegularPotential.memLp_id_two gaussianRegular)]
  have h0 : ∫ y, id y ∂(gaussianRegular.law : Measure ℝ) = 0 := gaussian_mean
  rw [h0]
  simp only [sub_zero, Real.inner_apply, ContinuousLinearMap.id_apply]
  have heq : (fun x : ℝ => u * x * (v * x)) = fun x => (u * v) * x ^ 2 := by
    funext x
    ring
  rw [heq, integral_const_mul, gaussian_second, mul_one]

theorem inputRegular : KLS.RegularPotential (fun x : ℝ => ‖scaleTwo x + 3‖ ^ 2 / 2)
    (KLS.RegularPotential.affineLowerConstant 1 scaleTwo) (KLS.RegularPotential.affineUpperConstant 1 scaleTwo) :=
  KLS.RegularPotential.comp_affine gaussianRegular scaleTwo (3 : ℝ)

/-- Before normalization the actual input barycenter is −3/2. -/
theorem input_mean : ∫ x, x ∂(inputRegular.law : Measure ℝ) = -3 / 2 := by
  have htr2 : MemLp id 2 (Probability.translateLaw gaussianRegular.law (-3) : Measure ℝ) := by
    rw [Probability.coe_translateLaw]
    exact (measurableEmbedding_addLeft (-3 : ℝ)).memLp_map_measure_iff.mpr
      ((memLp_const (-3 : ℝ)).add (KLS.RegularPotential.memLp_id_two gaussianRegular))
  rw [KLS.RegularPotential.law_comp_affine_eq_map gaussianRegular scaleTwo 3,
    Probability.integral_id_mapContinuousLinearEquiv _ _ (htr2.integrable one_le_two),
    Probability.integral_id_translateLaw _ ((KLS.RegularPotential.memLp_id_two gaussianRegular).integrable one_le_two),
    gaussian_mean]
  norm_num [scaleTwo_symm_apply]

/-- Before whitening the genuine covariance operator is scalar 1/4, rather than identity. -/
theorem input_covariance : Covariance.operator (inputRegular.law : Measure ℝ) =
    (1 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  rw [KLS.RegularPotential.law_comp_affine_eq_map gaussianRegular scaleTwo 3,
    Covariance.operator_mapContinuousLinearEquiv, Covariance.operator_translateLaw,
    gaussian_covariance, scaleTwo_symm_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe, scaleTwo_symm_apply]
  ring

private theorem input_whitening (u v : ℝ) :
    inner ℝ (Covariance.operator (inputRegular.law : Measure ℝ) (scaleTwo u)) (scaleTwo v) =
      inner ℝ u v := by
  rw [input_covariance]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    scaleTwo_apply, Real.inner_apply]
  ring

/-- The actual source regular/isotropic producer accepts a nonorthogonal, translated law;
neither a positive covariance premise nor an isotropic output is supplied. -/
theorem input_actual_producer :
    ∃ (W : ℝ ≃L[ℝ] ℝ) (V' : ℝ → ℝ) (a' b' : ℝ)
      (hV' : KLS.RegularPotential V' a' b'),
      0 < a' ∧ 0 < b' ∧ KLS.Isotropic hV'.law ∧
      hV'.law = Probability.mapContinuousLinearEquiv
        (Probability.translateLaw inputRegular.law (3 / 2)) W := by
  obtain ⟨W, c, V', a', b', hV', hc, _, _, _, ha, hb, hiso, hlaw⟩ :=
    KLS.RegularPotential.exists_regular_isotropic inputRegular
  rw [input_mean] at hc
  refine ⟨W, V', a', b', hV', ha, hb, hiso, ?_⟩
  rw [hc] at hlaw
  convert hlaw using 1
  norm_num

/-- The explicit covariance whitening 2 gives genuine isotropy of the concrete output law. -/
theorem input_explicit_isotropic :
    KLS.Isotropic (KLS.RegularPotential.comp_affine inputRegular scaleTwo.symm
      (∫ x, x ∂(inputRegular.law : Measure ℝ))).law :=
  KLS.RegularPotential.isotropic_comp_affine_of_whitening inputRegular scaleTwo scaleTwo_adjoint input_whitening

/-- Combining actual input mean and actual inverse map gives the original standard Gaussian
potential after centering and whitening. This tests both directions of affine transport. -/
theorem input_whitened_potential (x : ℝ) :
    (fun y : ℝ => ‖scaleTwo (scaleTwo.symm y +
      ∫ z, z ∂(inputRegular.law : Measure ℝ)) + 3‖ ^ 2 / 2) x = ‖x‖ ^ 2 / 2 := by
  dsimp only
  rw [input_mean, scaleTwo_apply, scaleTwo_symm_apply]
  have heq : 2 * (x / 2 + -3 / 2) + 3 = x := by ring
  rw [heq]

/-- Exact law round trip of the nonorthogonal translated input through the actual mean and
explicit covariance whitening. The Jacobian-normalized law is the original Gaussian. -/
theorem input_whitened_law :
    (KLS.RegularPotential.comp_affine inputRegular scaleTwo.symm
      (∫ x, x ∂(inputRegular.law : Measure ℝ))).law = gaussianRegular.law := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [KLS.RegularPotential.law_comp_affine inputRegular scaleTwo.symm _, ContinuousLinearEquiv.symm_symm,
    input_mean, KLS.RegularPotential.law_comp_affine gaussianRegular scaleTwo 3,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have heq : ((fun y : ℝ => scaleTwo (y - -3 / 2)) ∘
      (fun y => scaleTwo.symm (y - 3))) = id := by
    funext y
    simp only [Function.comp_apply, scaleTwo_apply, scaleTwo_symm_apply, id_eq]
    ring
  rw [heq, Measure.map_id]

/-- Actual ambient covariance positivity on the concrete input is substantive. -/
theorem input_covariance_positive :
    0 < inner ℝ (Covariance.operator (inputRegular.law : Measure ℝ) (1 : ℝ)) 1 :=
  KLS.RegularPotential.covariance_pos inputRegular (by norm_num)

private theorem zero_regular :
    KLS.RegularPotential (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ)) 2 (-4) := by
  refine ⟨Function.HasTemperateGrowth.const 7, by norm_num, ?_, ?_⟩
  · intro x v
    rw [Subsingleton.elim v 0]
    simp [bilinearIteratedFDerivTwo]
  · intro x v
    rw [Subsingleton.elim v 0]
    simp [bilinearIteratedFDerivTwo]

/-- The same actual constructor works in rank zero, producing positive output coefficients
even from the structure's permitted negative input upper coefficient. -/
theorem zero_actual_producer :
    ∃ (_W : EuclideanSpace ℝ (Fin 0) ≃L[ℝ] EuclideanSpace ℝ (Fin 0))
      (V' : EuclideanSpace ℝ (Fin 0) → ℝ) (a' b' : ℝ)
      (hV' : KLS.RegularPotential V' a' b'),
      0 < a' ∧ 0 < b' ∧ KLS.Isotropic hV'.law ∧
      hV'.law = zero_regular.law := by
  obtain ⟨W, c, V', a', b', hV', _, _, _, _, ha, hb, hiso, hlaw⟩ :=
    KLS.RegularPotential.exists_regular_isotropic zero_regular
  refine ⟨W, V', a', b', hV', ha, hb, hiso, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  rw [hlaw, Probability.coe_mapContinuousLinearEquiv, Probability.coe_translateLaw,
    Measure.map_map W.continuous.measurable (by fun_prop)]
  have heq : ((fun x => W x) ∘ (fun x => -c + x)) = id := by
    funext x
    exact Subsingleton.elim _ _
  rw [heq, Measure.map_id]

/-- Rank-zero positivity input to whitening is vacuous, not an assertion of a positive
nonzero eigenvalue or positive operator norm. -/
theorem zero_covariance_and_full_support :
    Covariance.operator (zero_regular.law : Measure (EuclideanSpace ℝ (Fin 0))) = 0 ∧
      (zero_regular.law : Measure (EuclideanSpace ℝ (Fin 0))).support = Set.univ :=
  ⟨Subsingleton.elim _ _, KLS.RegularPotential.support_law zero_regular⟩

end RegularIsotropicAudit

#print axioms FunctionalInequalities.KLS.RegularPotential.covariance_pos
#print axioms FunctionalInequalities.KLS.RegularPotential.support_law
#print axioms FunctionalInequalities.KLS.RegularPotential.exists_isotropic_comp_affine
#print axioms FunctionalInequalities.KLS.RegularPotential.exists_regular_isotropic
#print axioms RegularIsotropicAudit.input_actual_producer
#print axioms RegularIsotropicAudit.input_explicit_isotropic
#print axioms RegularIsotropicAudit.input_whitened_law
#print axioms RegularIsotropicAudit.zero_actual_producer
#print axioms RegularIsotropicAudit.zero_covariance_and_full_support

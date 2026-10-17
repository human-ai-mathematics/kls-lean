import FunctionalInequalities.KLS.LogConcave.Regular.Poincare
import FunctionalInequalities.KLS.BKL.GaussianTaylor
import FunctionalInequalities.KLS.LogConcave.Line.SharpPoincare

/-!
# Audit: conditional Poincaré transfer (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5. Clients: in dimension one the
universal premise is discharged by the proved bound `C_P ≤ 4 Var` for isotropic regular laws, so the
non-isotropic input `‖2x+3‖²/2` (covariance `1/4`) gets `C_P ≤ 1`; in dimension zero the premise is
the zero constant and the transfer gives `0`; the envelope coefficient stays positive. The
all-dimensional universal premise is not proved. Clients adapted from the Codex bundle
`Regular-Poincare-Reduction/RealConsumers.lean` (independently accepted, receipt 215b0ade…), with
the input law reconstructed as in `RegularIsotropicAudit`.
-/

open MeasureTheory ProbabilityTheory FunctionalInequalities FunctionalInequalities.KLS
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace RegularPoincareAudit

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

/-- One-dimensional regular-isotropic premise actually follows from proved 4Var, not an assumption. -/
theorem real_regular_isotropic_four {V : ℝ → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (_hb : 0 < b) (hiso : KLS.Isotropic hV.law) :
    Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (4 : ENNReal) := by
  have hv : variance id (hV.law : Measure ℝ) = 1 := by
    have h := Covariance.operator_inner (hV.law : Measure ℝ) (1 : ℝ) 1
    rw [hiso.covariance_identity, covarianceBilin_self hiso.memLp_two] at h
    simpa only [ContinuousLinearMap.id_apply, Real.inner_apply, one_mul, Function.id_def] using h.symm
  have h := hV.logConcave_law.localSlope_constant_le_four_variance
  rw [hv] at h
  norm_num at h
  exact h

/-- The actual nonorthogonal input has covariance1/4; the conditional transfer derives CP<=1. -/
theorem nonorthogonal_input_poincare : Poincare.LocalSlope.Intrinsic.constant inputRegular.law ≤ 1 := by
  have hn : ‖Covariance.operator (inputRegular.law : Measure ℝ)‖ = 1 / 4 := by
    rw [input_covariance, norm_smul, ContinuousLinearMap.norm_id]
    norm_num
  have h := KLS.RegularPotential.localSlope_le_covariance_norm (K := (4 : NNReal)) real_regular_isotropic_four inputRegular
  rw [hn] at h
  have he : ((4 : NNReal) : ENNReal) * ENNReal.ofReal (1 / 4 : ℝ) = 1 := by
    norm_num [ENNReal.ofReal_div_of_pos]
    exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
  exact h.trans_eq he

/-- The same actual input consumes the source envelope, with no moment/covariance/CP output premise. -/
theorem nonorthogonal_input_envelope :
    Poincare.LocalSlope.Intrinsic.constant inputRegular.law ≤
      ENNReal.ofReal ((4 : ℝ) * (1 + ‖Covariance.operator (inputRegular.law : Measure ℝ) -
        ContinuousLinearMap.id ℝ ℝ‖)) :=
  KLS.RegularPotential.localSlope_le_covariance_envelope (K := (4 : NNReal)) real_regular_isotropic_four inputRegular

abbrev ZeroSpace := EuclideanSpace ℝ (Fin 0)
private theorem zero_regular : KLS.RegularPotential (fun _ : ZeroSpace => (7 : ℝ)) 2 (-4) := by
  refine ⟨Function.HasTemperateGrowth.const 7, by norm_num, ?_, ?_⟩
  · intro x v
    rw [Subsingleton.elim v 0]
    simp [bilinearIteratedFDerivTwo]
  · intro x v
    rw [Subsingleton.elim v 0]
    simp [bilinearIteratedFDerivTwo]

/-- A rank-zero universal source bound is genuinely zero for every law. -/
theorem zero_regular_isotropic_bound {V : ZeroSpace → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (_hb : 0 < b) (_hiso : KLS.Isotropic hV.law) :
    Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (0 : ENNReal) := by
  rw [Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton]

/-- Negative old upperb is permitted in rank0; the actual producer/transfer still gives CP0. -/
theorem zero_input_poincare : Poincare.LocalSlope.Intrinsic.constant zero_regular.law ≤ 0 := by
  have h := KLS.RegularPotential.localSlope_le_covariance_norm (K := (0 : NNReal)) zero_regular_isotropic_bound zero_regular
  simpa only [ENNReal.coe_zero, zero_mul] using h

/-- The identity norm is really zero; the future positive envelope does not divide by it. -/
theorem zero_identity_norm : ‖ContinuousLinearMap.id ℝ ZeroSpace‖ = 0 := by
  have h : ContinuousLinearMap.id ℝ ZeroSpace = 0 := Subsingleton.elim _ _
  rw [h, norm_zero]

theorem zero_positive_envelope :
    0 < (2 : ℝ) * (1 + ‖Covariance.operator (zero_regular.law : Measure ZeroSpace) -
      ContinuousLinearMap.id ℝ ZeroSpace‖) :=
  KLS.RegularPotential.envelope_coefficient_pos (2 : NNReal) (by norm_num) _

end RegularPoincareAudit

#print axioms FunctionalInequalities.KLS.RegularPotential.localSlope_le_covariance_norm
#print axioms FunctionalInequalities.KLS.RegularPotential.localSlope_le_covariance_envelope
#print axioms FunctionalInequalities.KLS.RegularPotential.envelope_coefficient_tendsto
#print axioms RegularPoincareAudit.real_regular_isotropic_four
#print axioms RegularPoincareAudit.nonorthogonal_input_poincare
#print axioms RegularPoincareAudit.nonorthogonal_input_envelope
#print axioms RegularPoincareAudit.zero_input_poincare

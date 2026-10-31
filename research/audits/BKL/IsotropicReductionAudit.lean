module

public import FunctionalInequalities.KLS.BKL.Reduction
public import FunctionalInequalities.KLS.LogConcave.Line.SharpPoincare
public import FunctionalInequalities.KLS.BKL.GaussianTaylor

/-!
# Audit: the isotropic log-concave reduction and the conditional Theorem 1.1 (BKL)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2 (p. 5) and p. 30. Clients: in
dimension one the regular-isotropic premise is discharged by the certified bound `C_P ≤ 4 Var`, so
every isotropic log-concave law on `ℝ` has `C_P ≤ 4` through the full approximation passage,
exercised on the standard Gaussian (variance `1`); the zero-dimensional Dirac law has constant `0`
without any positive-dimensional premise. These clients test the conditional reduction. The
all-dimensional bound and Theorem 4.1 have separate closed producers in
`KLS/BKL/Poincare.lean` and `KLS/BKL/Cumulant/Bound.lean`.
-/

open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped RealInnerProductSpace

namespace IsotropicReductionAudit

theorem variance_one_of_real_isotropic {μ : ProbabilityMeasure ℝ} (hiso : KLS.Isotropic μ) :
    variance id (μ : Measure ℝ) = 1 := by
  have h := Covariance.operator_inner (μ := (μ : Measure ℝ)) (1 : ℝ) (1 : ℝ)
  rw [hiso.covariance_identity, ContinuousLinearMap.id_apply, Real.inner_apply,
    covarianceBilin_real] at h
  norm_num at h
  exact h.symm

/-- The fixed-carrier conditional premise is truly discharged, so this invokes the actual
approximation passage with no unproved-bound premise remaining. -/
theorem real_isotropic_lc_four (μ : ProbabilityMeasure ℝ)
    (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (4 : ENNReal) := by
  apply KLS.LogConcave.localSlope_le_of_regular_isotropic_bound
    (K := (4 : NNReal)) ?_ μ hLC hiso
  intro V a b hV _hb hViso
  have h := hV.logConcave_law.localSlope_constant_le_four_variance
  rw [variance_one_of_real_isotropic hViso] at h
  norm_num at h ⊢
  exact h

private theorem hG : KLS.RegularPotential (fun x : ℝ => ‖x‖ ^ 2 / 2) 1 1 :=
  KLS.regularPotential_half_norm_sq

private theorem gaussian_mean : ∫ x, x ∂(hG.law : Measure ℝ) = 0 :=
  KLS.integral_id_tilted_half_norm_sq

private theorem gaussian_second : ∫ x, x ^ 2 ∂(hG.law : Measure ℝ) = 1 := by
  have h := KLS.integral_inner_sq_tilted_half_norm_sq (E := ℝ) 1
  change (∫ x : ℝ, x ^ 2 ∂((volume : Measure ℝ).tilted (-fun x : ℝ => ‖x‖ ^ 2 / 2))) = 1
  simpa using h

private theorem gaussian_isotropic : KLS.Isotropic hG.law := by
  have h2 := hG.logConcave_law.memLp_id_two
  refine ⟨h2, gaussian_mean, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [Covariance.operator_inner, covarianceBilin_apply h2]
  have h0 : ∫ y, id y ∂(hG.law : Measure ℝ) = 0 := gaussian_mean
  rw [h0]
  simp only [sub_zero, Real.inner_apply, ContinuousLinearMap.id_apply]
  have heq : (fun x : ℝ => u * x * (v * x)) = fun x => (u * v) * x ^ 2 := by
    funext x
    ring
  rw [heq, integral_const_mul, gaussian_second, mul_one]

/-- A concrete genuine nonzero-variance source consumes the full passage without an unproved
premise. Source LC/isotropy are established from actual Gaussian moments. -/
theorem actual_gaussian_four :
    variance id (hG.law : Measure ℝ) = 1 ∧
      Poincare.LocalSlope.Intrinsic.constant hG.law ≤ (4 : ENNReal) :=
  ⟨variance_one_of_real_isotropic gaussian_isotropic,
    real_isotropic_lc_four hG.law hG.logConcave_law gaussian_isotropic⟩

private noncomputable def μ0 : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)) :=
  Probability.ofMeasure (Measure.dirac 0)

private theorem zero_isotropic : KLS.Isotropic μ0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    exact integrable_dirac (by simp)
  · simp [μ0, Probability.ofMeasure]
  · exact Subsingleton.elim _ _

/-- The actual rank-zero source needs no separate `n = 0` hypothesis. Its fixed-carrier zero
bound is discharged for every regular law by the subsingleton bound `C_P = 0`. -/
theorem actual_rank_zero : Poincare.LocalSlope.Intrinsic.constant μ0 = 0 := by
  have hLC : KLS.LogConcave μ0 := KLS.logConcave_dirac 0
  have h := KLS.LogConcave.localSlope_le_of_regular_isotropic_bound
    (K := (0 : NNReal)) (μ := μ0) ?_ hLC zero_isotropic
  · exact le_antisymm h bot_le
  intro V a b hV _hb _hiso
  rw [Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton]
  exact bot_le

end IsotropicReductionAudit

#print axioms FunctionalInequalities.KLS.LogConcave.affineSupport_eq_top_of_isotropic
#print axioms FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity_of_isotropic
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_le_of_regular_isotropic_bound
#print axioms
  FunctionalInequalities.KLS.LogConcave.localSlope_le_of_euclidean_regular_isotropic_bound
#print axioms
  FunctionalInequalities.KLS.LogConcave.isotropicBound_of_euclidean_regular_isotropic_bound
#print axioms FunctionalInequalities.KLS.localSlope_le_of_cumulantBound_all
#print axioms FunctionalInequalities.KLS.conjecture_of_cumulantBound
#print axioms IsotropicReductionAudit.real_isotropic_lc_four
#print axioms IsotropicReductionAudit.actual_gaussian_four
#print axioms IsotropicReductionAudit.actual_rank_zero

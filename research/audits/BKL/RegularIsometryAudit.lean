import FunctionalInequalities.KLS.LogConcave.Regular.Isometry
import FunctionalInequalities.KLS.BKL.GaussianTaylor
import FunctionalInequalities.KLS.LogConcave.Translation
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Audit: regular potentials under linear isometries (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5. Clients: the Gaussian potential on
`ℝ` transported to `ℝ¹` keeps the constants `1, 1`, its law, isotropy, normalizer and literature
constant, and round-trips; a positive-dimensional Euclidean bound (hypothetical, not asserted) would
transfer to the real law; a zero-dimensional potential moves between carriers in different universes
with constants `2, −4` and literature constant `0`. Clients adapted from the Codex bundle
`Regular-Isometry-Transport/Clients.lean` (independently accepted, receipt a30a9de3…).
-/

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace RegularIsometryAudit

noncomputable def realCoordinates : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

theorem gaussianRegular : KLS.RegularPotential (fun x : ℝ => ‖x‖ ^ 2 / 2) 1 1 :=
  KLS.regularPotential_half_norm_sq

/-- A real Gaussian potential is genuinely regular on the different Fin1 carrier with
exactly the same lower and upper Hessian coefficients. -/
theorem fin1_regular : KLS.RegularPotential
    (fun y : EuclideanSpace ℝ (Fin 1) => ‖y‖ ^ 2 / 2) 1 1 := by
  simpa only [LinearIsometryEquiv.norm_map] using KLS.RegularPotential.comp_isometry gaussianRegular realCoordinates

/-- A nonzero input point tests the actual transported potential. -/
theorem fin1_nonzero_potential :
    (fun y : EuclideanSpace ℝ (Fin 1) => ‖realCoordinates.symm y‖ ^ 2 / 2)
      (realCoordinates (3 : ℝ)) = 9 / 2 := by
  dsimp only
  rw [realCoordinates.symm_apply_apply]
  norm_num

/-- The actual normalized law is the real law pushed forward into Fin1. -/
theorem fin1_actual_law :
    (KLS.RegularPotential.comp_isometry gaussianRegular realCoordinates).law =
      Probability.mapLinearIsometryEquiv gaussianRegular.law realCoordinates :=
  KLS.RegularPotential.law_comp_isometry_eq_map gaussianRegular realCoordinates

/-- Different-type Haar normalization uses true isometry volume preservation, not a
determinant with unrelated domain and codomain types. -/
theorem fin1_normalizer :
    (∫ y : EuclideanSpace ℝ (Fin 1), Real.exp (-(‖realCoordinates.symm y‖ ^ 2 / 2))) =
      ∫ x : ℝ, Real.exp (-(‖x‖ ^ 2 / 2)) :=
  KLS.RegularPotential.integral_exp_neg_comp_isometry (fun x : ℝ => ‖x‖ ^ 2 / 2) realCoordinates

private theorem gaussian_mean : ∫ x, x ∂(gaussianRegular.law : Measure ℝ) = 0 :=
  KLS.integral_id_tilted_half_norm_sq

private theorem gaussian_second : ∫ x, x ^ 2 ∂(gaussianRegular.law : Measure ℝ) = 1 := by
  have h := KLS.integral_inner_sq_tilted_half_norm_sq (E := ℝ) 1
  change (∫ x : ℝ, x ^ 2 ∂((volume : Measure ℝ).tilted (-fun x : ℝ => ‖x‖ ^ 2 / 2))) = 1
  simpa using h

private theorem gaussian_isotropic : KLS.Isotropic gaussianRegular.law := by
  have h2 := gaussianRegular.logConcave_law.memLp_id_two
  refine ⟨h2, gaussian_mean, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [Covariance.operator_inner, ProbabilityTheory.covarianceBilin_apply h2]
  have h0 : ∫ y, id y ∂(gaussianRegular.law : Measure ℝ) = 0 := gaussian_mean
  rw [h0]
  simp only [sub_zero, Real.inner_apply, ContinuousLinearMap.id_apply]
  have heq : (fun x : ℝ => u * x * (v * x)) = fun x => (u * v) * x ^ 2 := by
    funext x
    ring
  rw [heq, integral_const_mul, gaussian_second, mul_one]

/-- Isotropy on Fin1 is actually derived from canonical Gaussian moments and the new true
law identity; it is not a supplied isotropic image-law hypothesis. -/
theorem fin1_actual_isotropic : KLS.Isotropic (KLS.RegularPotential.comp_isometry gaussianRegular realCoordinates).law :=
  KLS.RegularPotential.isotropic_comp_isometry gaussianRegular gaussian_isotropic realCoordinates

/-- Moving back through the inverse gives the original probability law exactly. -/
theorem fin1_law_roundtrip :
    (KLS.RegularPotential.comp_isometry (KLS.RegularPotential.comp_isometry gaussianRegular realCoordinates) realCoordinates.symm).law =
      gaussianRegular.law := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [KLS.RegularPotential.law_comp_isometry (KLS.RegularPotential.comp_isometry gaussianRegular realCoordinates) realCoordinates.symm,
    KLS.RegularPotential.law_comp_isometry gaussianRegular realCoordinates,
    Measure.map_map realCoordinates.symm.continuous.measurable realCoordinates.continuous.measurable]
  have heq : (⇑realCoordinates.symm ∘ ⇑realCoordinates) = id :=
    funext realCoordinates.symm_apply_apply
  rw [heq, Measure.map_id]

/-- The actual intrinsic literature constant is unchanged between real and Fin1 carriers. -/
theorem fin1_literature_constant :
    Poincare.LocalSlope.Intrinsic.constant (KLS.RegularPotential.comp_isometry gaussianRegular realCoordinates).law =
      Poincare.LocalSlope.Intrinsic.constant gaussianRegular.law :=
  KLS.RegularPotential.localSlope_constant_comp_isometry gaussianRegular realCoordinates

/-- A future positive-dimensional Euclidean regular-isotropic bound has a real-law consumer;
all concrete law/regularity/isotropy premises are discharged from actual source facts. -/
theorem real_bound_consumer {K : NNReal}
    (hK : ∀ (n : ℕ), 0 < n → ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
      (hV : KLS.RegularPotential V a b), KLS.Isotropic hV.law →
        Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (K : ENNReal)) :
    Poincare.LocalSlope.Intrinsic.constant gaussianRegular.law ≤ (K : ENNReal) :=
  KLS.RegularPotential.localSlope_le_of_euclidean_bound hK gaussianRegular gaussian_isotropic

abbrev ZeroLow := EuclideanSpace ℝ (Fin 0)
abbrev ZeroHigh := EuclideanSpace ℝ PEmpty.{2}

/-- The empty-coordinate isometry has both a different type and a different universe. -/
noncomputable def zeroCoordinates : ZeroLow ≃ₗᵢ[ℝ] ZeroHigh :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.equivOfIsEmpty (Fin 0) PEmpty.{2})

private theorem zero_regular : KLS.RegularPotential (fun _ : ZeroLow => (7 : ℝ)) 2 (-4) := by
  refine ⟨Function.HasTemperateGrowth.const 7, by norm_num, ?_, ?_⟩
  · intro x v
    rw [Subsingleton.elim v 0]
    simp [bilinearIteratedFDerivTwo]
  · intro x v
    rw [Subsingleton.elim v 0]
    simp [bilinearIteratedFDerivTwo]

/-- Exact coefficients are retained even in the structure's stronger permitted rank-zero
scope b<0. This does not claim a negative b is the paper's stated regularity convention. -/
theorem zero_same_constants : KLS.RegularPotential (fun _ : ZeroHigh => (7 : ℝ)) 2 (-4) :=
  KLS.RegularPotential.comp_isometry zero_regular zeroCoordinates

/-- The law genuinely moves between the two carriers/universes. -/
theorem zero_actual_law : (KLS.RegularPotential.comp_isometry zero_regular zeroCoordinates).law =
    Probability.mapLinearIsometryEquiv zero_regular.law zeroCoordinates :=
  KLS.RegularPotential.law_comp_isometry_eq_map zero_regular zeroCoordinates

/-- Rank-zero literature constants are zero on both actual laws, without a future n=0
Euclidean bound premise. -/
theorem zero_actual_constants :
    Poincare.LocalSlope.Intrinsic.constant zero_regular.law = 0 ∧
      Poincare.LocalSlope.Intrinsic.constant (KLS.RegularPotential.comp_isometry zero_regular zeroCoordinates).law = 0 :=
  ⟨Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton _,
    Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton _⟩

end RegularIsometryAudit

#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_clm
#print axioms FunctionalInequalities.KLS.RegularPotential.comp_isometry
#print axioms FunctionalInequalities.KLS.RegularPotential.law_comp_isometry
#print axioms FunctionalInequalities.KLS.RegularPotential.localSlope_constant_comp_isometry
#print axioms FunctionalInequalities.KLS.RegularPotential.localSlope_le_of_euclidean_bound
#print axioms RegularIsometryAudit.fin1_actual_isotropic
#print axioms RegularIsometryAudit.fin1_law_roundtrip
#print axioms RegularIsometryAudit.real_bound_consumer
#print axioms RegularIsometryAudit.zero_actual_constants

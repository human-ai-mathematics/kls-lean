import FunctionalInequalities.KLS.LogConcave.Regular.Affine
import FunctionalInequalities.KLS.BKL.GaussianTaylor

/-!
# Audit: regular potentials under affine changes of variables (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5 (stability of the regular class
(12) under centering and whitening). Clients: the scaling `x ↦ 2x + 3` of the standard Gaussian
potential on `ℝ` is regular with the explicit constants `4/9 ≤ ∇² ≤ 9`, its law is the image law with
mean `−3/2` and centered second moment `1/4`, and its normalizer carries the factor `1/2`; the
zero-dimensional law with the original `b = −4` still yields positive constants. No whitening
operator is chosen and the approximation theorem is not asserted.
-/

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open FunctionalInequalities.Analysis.BakryEmery

namespace AffineRegularAudit

noncomputable def scaleTwo : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.equivOfInverse ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    (by intro x; simp) (by intro x; simp)

private theorem scaleTwo_apply (x : ℝ) : scaleTwo x = 2 * x := rfl
private theorem scaleTwo_symm_apply (x : ℝ) : scaleTwo.symm x = x / 2 := by
  change (1 / 2 : ℝ) * x = x / 2
  ring

private theorem scaleTwo_norm : ‖(scaleTwo : ℝ →L[ℝ] ℝ)‖ = 2 := by
  change ‖(2 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ = 2
  rw [norm_smul, ContinuousLinearMap.norm_id]
  norm_num

private theorem scaleTwo_symm_norm : ‖(scaleTwo.symm : ℝ →L[ℝ] ℝ)‖ = 1 / 2 := by
  change ‖(1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ = 1 / 2
  rw [norm_smul, ContinuousLinearMap.norm_id]
  norm_num

private theorem scaleTwo_lower : RegularPotential.affineLowerConstant 1 scaleTwo = 4 / 9 := by
  norm_num [RegularPotential.affineLowerConstant, scaleTwo_symm_norm]
private theorem scaleTwo_upper : RegularPotential.affineUpperConstant 1 scaleTwo = 9 := by
  norm_num [RegularPotential.affineUpperConstant, scaleTwo_norm]

/-- Nonorthogonal scaling 2 and nonzero translation 3 give a genuine regular potential. -/
theorem scaled_translated_regular :
    KLS.RegularPotential (fun x : ℝ => ‖2 * x + 3‖ ^ 2 / 2) (4 / 9) 9 := by
  have h := RegularPotential.comp_affine (KLS.regularPotential_half_norm_sq (E := ℝ)) scaleTwo (3 : ℝ)
  simpa only [scaleTwo_apply, scaleTwo_lower, scaleTwo_upper] using h

/-- The actual transformed Hessian is four, so the source bounds have substantive nonzero
content rather than an orthogonal/translation-only witness. -/
theorem scaled_translated_hessian (x : ℝ) :
    bilinearIteratedFDerivTwo ℝ (fun y : ℝ => ‖2 * y + 3‖ ^ 2 / 2) x 1 1 = 4 := by
  have h := Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_affine ((contDiff_norm_sq ℝ).div_const 2) scaleTwo 3 x 1 1
  rw [KLS.bilinearIteratedFDerivTwo_half_norm_sq] at h
  norm_num only [scaleTwo_apply] at h
  norm_num at h ⊢
  exact h

/-- Exact normalized image law, with inverse affine map (y−3)/2. -/
theorem scaled_translated_law :
    ((RegularPotential.comp_affine (KLS.regularPotential_half_norm_sq (E := ℝ)) scaleTwo 3).law : Measure ℝ) =
      ((KLS.regularPotential_half_norm_sq (E := ℝ)).law : Measure ℝ).map
        (fun y : ℝ => (y - 3) / 2) := by
  have h := RegularPotential.law_comp_affine (KLS.regularPotential_half_norm_sq (E := ℝ)) scaleTwo 3
  simpa only [scaleTwo_symm_apply] using h

/-- The nonorthogonal Jacobian has the actual inverse factor 1/2 in the normalizer. -/
theorem scaled_translated_normalizer :
    (∫ x : ℝ, Real.exp (-(‖2 * x + 3‖ ^ 2 / 2))) =
      (1 / 2 : ℝ) * ∫ y : ℝ, Real.exp (-(‖y‖ ^ 2 / 2)) := by
  have hdet : LinearMap.det (scaleTwo : ℝ →ₗ[ℝ] ℝ) = 2 := by
    change LinearMap.det ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) = 2
    rw [LinearMap.det_smul, LinearMap.det_id]
    norm_num [Module.finrank_self]
  have h := RegularPotential.integral_exp_neg_comp_affine (KLS.regularPotential_half_norm_sq (E := ℝ)) scaleTwo 3
  rw [hdet] at h
  simpa only [scaleTwo_apply, show |(2 : ℝ)⁻¹| = 1 / 2 by norm_num] using h

/-- Zero dimension admits an original negative upper coefficient. The strictly positive
upper coefficient is produced without any positive inverse-operator-norm assumption. -/
private theorem zero_regular :
    KLS.RegularPotential (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ)) 2 (-4) := by
  refine ⟨Function.HasTemperateGrowth.const 7, by norm_num, ?_, ?_⟩
  · intro x v
    rw [Subsingleton.elim v 0]
    simp [bilinearIteratedFDerivTwo]
  · intro x v
    rw [Subsingleton.elim v 0]
    simp [bilinearIteratedFDerivTwo]

theorem zero_dimension_regular_and_positive_constants :
    let L := ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))
    KLS.RegularPotential (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ))
      (RegularPotential.affineLowerConstant 2 L) (RegularPotential.affineUpperConstant (-4) L) ∧
      0 < RegularPotential.affineLowerConstant 2 L ∧ 0 < RegularPotential.affineUpperConstant (-4) L := by
  dsimp only
  exact ⟨RegularPotential.comp_affine zero_regular _ 0, RegularPotential.affineLowerConstant_pos (by norm_num) _, RegularPotential.affineUpperConstant_pos _ _⟩

theorem zero_dimension_actual_law :
    let L := ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))
    ((RegularPotential.comp_affine zero_regular L 0).law : Measure (EuclideanSpace ℝ (Fin 0))) =
      (zero_regular.law : Measure (EuclideanSpace ℝ (Fin 0))) := by
  dsimp only
  rw [RegularPotential.law_comp_affine zero_regular (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))) 0]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply, sub_zero]
  change Measure.map id (zero_regular.law : Measure (EuclideanSpace ℝ (Fin 0))) =
    (zero_regular.law : Measure (EuclideanSpace ℝ (Fin 0)))
  exact Measure.map_id

theorem zero_dimension_actual_constants :
    let L := ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))
    ‖(L.symm : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0))‖ = 0 ∧
      RegularPotential.affineLowerConstant 2 L = 2 ∧ RegularPotential.affineUpperConstant (-4) L = 1 := by
  dsimp only
  have hL : (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0)) :
      EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0)) = 0 := Subsingleton.elim _ _
  have hLi : ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))).symm :
      EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0)) = 0 := Subsingleton.elim _ _
  norm_num [RegularPotential.affineLowerConstant, RegularPotential.affineUpperConstant, hL, hLi]

end AffineRegularAudit

#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_affine
#print axioms FunctionalInequalities.KLS.RegularPotential.comp_affine
#print axioms FunctionalInequalities.Probability.map_tilted_measurableEquiv
#print axioms FunctionalInequalities.KLS.inverseAffine_map_volume
#print axioms FunctionalInequalities.KLS.RegularPotential.law_comp_affine
#print axioms FunctionalInequalities.KLS.RegularPotential.integral_exp_neg_comp_affine
#print axioms FunctionalInequalities.KLS.RegularPotential.law_comp_affine_eq_map
#print axioms AffineRegularAudit.scaled_translated_regular
#print axioms AffineRegularAudit.scaled_translated_law
#print axioms AffineRegularAudit.scaled_translated_normalizer
#print axioms AffineRegularAudit.zero_dimension_regular_and_positive_constants
#print axioms AffineRegularAudit.zero_dimension_actual_law

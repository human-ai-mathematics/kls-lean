module

public import FunctionalInequalities.KLS.Isotropic
public import FunctionalInequalities.KLS.BKL.GaussianTaylor
public import FunctionalInequalities.KLS.LogConcave.Translation
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Audit: mean Hessian of a convex potential (Letwin Lemma 2.3, analytic part)

Source: Letwin, arXiv:2607.24164v1, Lemma 2.3. Clients: the normalized Gaussian potential
`‖x‖²/2 + log Z` on `ℝ¹` has mean Hessian `1` in the unit direction (all integrability derived, none
assumed); the zero-dimensional constant potential gives `0` through the isotropic adapter. No moment
map is constructed.
-/

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace ConvexHessianAudit

abbrev E := EuclideanSpace ℝ (Fin 1)
/-- The standard Gaussian on `ℝ¹` as the law of the regular potential `‖x‖²/2`. -/
noncomputable def gaussian : ProbabilityMeasure E :=
  (KLS.regularPotential_half_norm_sq (E := E)).law
noncomputable def direction : E := EuclideanSpace.basisFun (Fin 1) ℝ 0
theorem gaussian_id_memLp : MemLp (id : E → E) 2 (gaussian : Measure E) :=
  KLS.LogConcave.memLp_id_two (KLS.regularPotential_half_norm_sq (E := E)).logConcave_law

private noncomputable def W (x : E) : ℝ := ‖x‖ ^ 2 / 2
private noncomputable def Z : ℝ := ∫ x, Real.exp (-W x) ∂(volume : Measure E)
private noncomputable def φ (x : E) : ℝ := W x + Real.log Z

private theorem exp_integrable : Integrable (fun x => Real.exp (-W x)) (volume : Measure E) :=
  (KLS.regularPotential_half_norm_sq (E := E)).integrable_exp_neg

private theorem Zpos : 0 < Z := integral_exp_pos exp_integrable

private theorem phi_exp (x : E) : Real.exp (-φ x) = Z⁻¹ * Real.exp (-W x) := by
  simp only [φ, neg_add_rev, Real.exp_add, Real.exp_neg, Real.exp_log Zpos]

private theorem phi_normalized : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1 := by
  simp_rw [phi_exp]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ Zpos.ne'

private theorem phi_smooth : ContDiff ℝ ∞ φ :=
  ((contDiff_norm_sq ℝ).div_const 2).add contDiff_const

private theorem phi_convex : ConvexOn ℝ Set.univ φ := by
  have h : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  have hw : ConvexOn ℝ Set.univ W := by
    have heq : W = fun x : E => (1 / 2 : ℝ) * ‖x‖ ^ 2 := by funext x; simp only [W]; ring
    rw [heq]
    exact h.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact hw.add_const (Real.log Z)

private theorem phi_hasFDerivAt (x : E) : HasFDerivAt φ (innerSL ℝ x) x := by
  have h : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa using (hasFDerivAt_id x).norm_sq
  have hw : HasFDerivAt W (innerSL ℝ x) x := by
    have hf : W = fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2 := by funext y; simp only [W]; ring
    have hL : innerSL ℝ x = (1 / 2 : ℝ) • (2 • innerSL ℝ x) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      norm_num
    rw [hf, hL]
    exact h.const_mul (1 / 2 : ℝ)
  exact hw.add_const _

private theorem phi_gradient : gradient φ = id := by
  funext x
  rw [gradient, (phi_hasFDerivAt x).fderiv]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply x

private theorem phi_law : (volume : Measure E).tilted (-φ) = (gaussian : Measure E) := by
  have hw : (-φ) = (-W) + fun _ => -Real.log Z := by funext x; simp [φ]; ring
  rw [hw, ← MeasureTheory.tilted_tilted (f := (-W)) exp_integrable]
  change ((gaussian : Measure E).tilted (fun _ => -Real.log Z)) = _
  exact tilted_const _ _

private theorem phi_gradL2 : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ)) := by
  rw [phi_gradient, phi_law]
  exact gaussian_id_memLp

theorem actual_nonzero_mean_hessian :
    (∫ x, bilinearIteratedFDerivTwo ℝ φ x direction direction ∂(gaussian : Measure E)) = 1 := by
  have h :=
    Analysis.BakryEmery.integral_hessian_tilted_eq_integral_fderiv_mul_of_convexOn φ phi_smooth
      phi_convex (Integrable.of_integral_ne_zero (by rw [phi_normalized]; norm_num))
      phi_normalized phi_gradL2 direction direction
  rw [phi_law] at h
  have hf :
    (fun x => fderiv ℝ φ x direction * fderiv ℝ φ x direction) = fun x => ⟪direction, x⟫ ^ 2 := by
    funext x
    rw [(phi_hasFDerivAt x).fderiv]
    simp only [innerSL_apply_apply, real_inner_comm, pow_two]
  rw [hf] at h
  have hg := KLS.integral_inner_sq_tilted_half_norm_sq direction
  change (∫ x, ⟪direction, x⟫ ^ 2 ∂(gaussian : Measure E)) = ‖direction‖ ^ 2 at hg
  have hd : ‖direction‖ = 1 := (EuclideanSpace.basisFun (Fin 1) ℝ).norm_eq_one 0
  rw [hg, hd] at h
  simpa only [one_pow] using h

private abbrev E0 := EuclideanSpace ℝ (Fin 0)
private noncomputable def ν0 : ProbabilityMeasure E0 := ⟨Measure.dirac 0, inferInstance⟩

private theorem zero_space_isotropic (μ : ProbabilityMeasure E0) : KLS.Isotropic μ where
  memLp_two := by
    have hi : (id : E0 → E0) = 0 := Subsingleton.elim _ _
    rw [hi]
    exact memLp_const (0 : E0)
  mean_zero := by
    have hi : (fun x : E0 => x) = fun _ => (0 : E0) := Subsingleton.elim _ _
    rw [hi]
    simp
  covariance_identity := Subsingleton.elim _ _

private theorem zero_normalized : ∫ _x : E0, Real.exp (-(0 : ℝ)) ∂volume = 1 := by
  rw [volume_euclideanSpace_eq_dirac (ι := Fin 0)]
  simp

private theorem zero_law : (ν0 : Measure E0) = volume.tilted (-(fun _ : E0 => (0 : ℝ))) := by
  rw [volume_euclideanSpace_eq_dirac (ι := Fin 0)]
  change Measure.dirac (0 : E0) = (Measure.dirac (0 : E0)).tilted (-(fun _ : E0 => (0 : ℝ)))
  have heq : (-(fun _ : E0 => (0 : ℝ))) = fun _ : E0 => (0 : ℝ) := by funext x; simp
  rw [heq]
  exact (tilted_const _ _).symm

theorem actual_zero_dimension_mean_hessian (u v : E0) :
    (∫ x, bilinearIteratedFDerivTwo ℝ (fun _ : E0 => (0 : ℝ)) x u v ∂(ν0 : Measure E0)) = 0 := by
  have h := KLS.integral_hessian_eq_inner_of_isotropic_map
    (fun _ : E0 => (0 : ℝ)) contDiff_const (convexOn_const 0 convex_univ) zero_normalized
    ν0 zero_law (zero_space_isotropic _) u v
  simpa only [Subsingleton.elim u 0, inner_zero_left] using h

end ConvexHessianAudit

#print axioms FunctionalInequalities.Analysis.integrable_of_cutoff_bounds
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_scaled_mul_hessian_tilted_eq
#print axioms FunctionalInequalities.Analysis.BakryEmery.integrable_hessian_diag_tilted_of_convexOn
#print axioms FunctionalInequalities.Analysis.BakryEmery.integrable_hessian_tilted_of_convexOn
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.integral_hessian_tilted_eq_integral_fderiv_mul_of_convexOn
#print axioms FunctionalInequalities.KLS.integral_hessian_eq_inner_of_isotropic_map
#print axioms ConvexHessianAudit.actual_nonzero_mean_hessian
#print axioms ConvexHessianAudit.actual_zero_dimension_mean_hessian

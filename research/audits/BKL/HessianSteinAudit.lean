import FunctionalInequalities.KLS.LogConcave.HessianStein
import FunctionalInequalities.KLS.BKL.GaussianTaylor
import FunctionalInequalities.KLS.LogConcave.Translation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Audit: the Hessian–Stein kernel of a given potential (Letwin Lemma 2.7, analytic part)

Source: Letwin, arXiv:2607.24164v1, Lemma 2.7. Clients: for the normalized Gaussian potential
`‖x‖²/2 + log Z` on `ℝ¹` (gradient `id`, inverse `id`) the constructed kernel is a symmetric
integrable Stein kernel with mean `1`, and is positive definite (a concrete fact of this example,
not a generic claim); the injective-gradient producer applies; the zero-dimensional constant
potential also yields a kernel. No moment map for an arbitrary law is constructed.
-/

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace HessianSteinAuditGaussian

abbrev E := EuclideanSpace ℝ (Fin 1)
noncomputable def μ : ProbabilityMeasure E := (KLS.regularPotential_half_norm_sq (E := E)).law
theorem gaussian_id_memLp : MemLp (id : E → E) 2 (μ : Measure E) :=
  KLS.LogConcave.memLp_id_two (KLS.regularPotential_half_norm_sq (E := E)).logConcave_law
private noncomputable def W (x : E) : ℝ := ‖x‖ ^ 2 / 2
private noncomputable def Z : ℝ := ∫ x, Real.exp (-W x) ∂(volume : Measure E)
noncomputable def φ (x : E) : ℝ := W x + Real.log Z

theorem phi_normalized : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1 := by
  have hi : Integrable (fun x : E => Real.exp (-W x)) volume :=
    (KLS.regularPotential_half_norm_sq (E := E)).integrable_exp_neg
  have hz : 0 < Z := integral_exp_pos hi
  have he (x : E) : Real.exp (-φ x) = Z⁻¹ * Real.exp (-W x) := by
    simp only [φ, neg_add_rev, Real.exp_add, Real.exp_neg, Real.exp_log hz]
  simp_rw [he]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ hz.ne'

theorem phi_smooth : ContDiff ℝ ∞ φ := ((contDiff_norm_sq ℝ).div_const 2).add contDiff_const

theorem phi_convex : ConvexOn ℝ Set.univ φ := by
  have h : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  have hw : ConvexOn ℝ Set.univ W := by
    have he : W = fun x : E => (1 / 2 : ℝ) * ‖x‖ ^ 2 := by funext x; unfold W; ring
    rw [he]
    exact h.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact hw.add_const (Real.log Z)

private theorem phi_hasFDerivAt (x : E) : HasFDerivAt φ (innerSL ℝ x) x := by
  have h : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa using (hasFDerivAt_id x).norm_sq
  have hw : HasFDerivAt W (innerSL ℝ x) x := by
    have he : W = fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2 := by funext y; unfold W; ring
    have hL : innerSL ℝ x = (1 / 2 : ℝ) • (2 • innerSL ℝ x) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      norm_num
    rw [he, hL]
    exact h.const_mul (1 / 2 : ℝ)
  exact hw.add_const _

theorem phi_gradient : gradient φ = id := by
  funext x
  rw [gradient, (phi_hasFDerivAt x).fderiv]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply x

theorem phi_law : (μ : Measure E) = volume.tilted (-φ) := by
  have hi : Integrable (fun x : E => Real.exp (-W x)) volume :=
    (KLS.regularPotential_half_norm_sq (E := E)).integrable_exp_neg
  have hf : (-φ) = (-W) + fun _ => -Real.log Z := by funext x; unfold φ; simp; ring
  rw [hf, ← MeasureTheory.tilted_tilted (f := (-W)) hi]
  change (μ : Measure E) = (μ : Measure E).tilted (fun _ => -Real.log Z)
  exact (tilted_const _ _).symm

theorem gradient_push : (μ : Measure E).map (gradient φ) = (μ : Measure E) := by
  rw [phi_gradient, Measure.map_id]

theorem actual_isotropic : KLS.Isotropic μ := by
  apply KLS.isotropic_of_moments μ gaussian_id_memLp
    KLS.integral_id_tilted_half_norm_sq
  intro u v
  have hs : (∫ x : E, x 0 ^ 2 ∂(μ : Measure E)) = 1 := by
    have h := KLS.integral_inner_sq_tilted_half_norm_sq (EuclideanSpace.basisFun (Fin 1) ℝ 0)
    have hm : (volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2) = (μ : Measure E) := rfl
    rw [hm] at h
    simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_pow] using h
  simp only [PiLp.inner_apply, Fin.sum_univ_one, Real.inner_apply]
  have he : (fun x : E => u 0 * x 0 * (v 0 * x 0)) = fun x => (u 0 * v 0) * x 0 ^ 2 := by
    funext x
    ring
  rw [he, integral_const_mul, hs, mul_one]

/-- Every stated genuine inverse prerequisite is discharged pointwise for actualgradientId. -/
theorem inverse_id : ∀ᵐ y ∂(μ : Measure E), (id : E → E) (gradient φ y) = y := by
  rw [phi_gradient]
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The actual given-potential producer constructs the canonical kernel from this real law. -/
theorem actual_hessian_stein : Probability.Stein.IsSteinKernel μ (Probability.Stein.hessianKernel φ id) :=
  KLS.LogConcave.hessianKernel_isSteinKernel φ phi_smooth phi_convex phi_normalized μ μ phi_law
    gradient_push actual_isotropic id measurable_id inverse_id

theorem actual_hessian_symmetric : Probability.Stein.SymmetricAE μ (Probability.Stein.hessianKernel φ id) :=
  Probability.Stein.hessianKernel_symmetricAE (phi_smooth.of_le (WithTop.coe_le_coe.mpr le_top)) id μ

theorem actual_hessian_entry_integrable (i j : Fin 1) :
    Integrable (fun x => Probability.Stein.hessianKernel φ id x i j) (μ : Measure E) :=
  KLS.LogConcave.integrable_hessianKernel_of_isotropic_map φ phi_smooth phi_convex phi_normalized μ μ phi_law
    gradient_push actual_isotropic id measurable_id inverse_id i j

theorem actual_kernel_mean_one : (∫ x, Probability.Stein.hessianKernel φ id x 0 0 ∂(μ : Measure E)) = 1 := by
  have h := KLS.LogConcave.integral_hessianKernel_eq_one φ phi_smooth phi_convex phi_normalized μ μ phi_law
    gradient_push actual_isotropic id measurable_id inverse_id 0 0
  simpa only [Matrix.one_apply, ite_true] using h

/-- This concrete inverse geometry is actually proved, not a source existence assumption. -/
theorem actual_gradient_injective : Function.Injective (gradient φ) := by
  rw [phi_gradient]
  exact Function.injective_id

/-- The conditional geometric variant is consumed with every source prerequisite discharged. -/
theorem actual_constructed_inverse_kernel :
    ∃ Ψ : E → E, Measurable Ψ ∧ Function.LeftInverse Ψ (gradient φ) ∧
      Probability.Stein.IsSteinKernel μ (Probability.Stein.hessianKernel φ Ψ) ∧
      Probability.Stein.SymmetricAE μ (Probability.Stein.hessianKernel φ Ψ) ∧
      (∀ i j, Integrable (fun x => Probability.Stein.hessianKernel φ Ψ x i j) (μ : Measure E)) := by
  obtain ⟨Ψ, hΨ, hi, hK, hS, hL, _⟩ := KLS.LogConcave.exists_hessianSteinKernel_of_injective_gradient
    φ phi_smooth phi_convex phi_normalized μ μ phi_law gradient_push actual_isotropic actual_gradient_injective
  exact ⟨Ψ, hΨ, hi, hK, hS, hL⟩

/-- Genuine Hessian identity for the concrete potential, computed from its actual first derivative. -/
theorem phi_hessian (x u v : E) : bilinearIteratedFDerivTwo ℝ φ x u v = ⟪u, v⟫ := by
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply (phi_smooth.of_le (WithTop.coe_le_coe.mpr le_top))]
  have hf : (fun y : E => fderiv ℝ φ y v) = fun y => ⟪v, y⟫ := by
    funext y
    rw [(phi_hasFDerivAt y).fderiv, innerSL_apply_apply, real_inner_comm]
  rw [hf]
  change (fderiv ℝ (innerSL ℝ v) x) u = _
  rw [(innerSL ℝ v).hasFDerivAt.fderiv, innerSL_apply_apply, real_inner_comm]

/-- Positive definiteness is proved for this actual Gaussian example, not inferred generically. -/
theorem actual_kernel_positive (x v : E) (hv : v ≠ 0) :
    0 < ⟪v, Probability.Stein.action (Probability.Stein.hessianKernel φ id x) v⟫ := by
  rw [Probability.Stein.hessianKernel, id_eq, Probability.Stein.inner_action_hessian,
    phi_hessian, real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

end HessianSteinAuditGaussian

namespace HessianSteinAuditZero

abbrev E := EuclideanSpace ℝ (Fin 0)
noncomputable def μ : ProbabilityMeasure E := ⟨Measure.dirac 0, inferInstance⟩
noncomputable def φ : E → ℝ := fun _ => 0

theorem phi_normalized : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1 := by
  rw [volume_euclideanSpace_eq_dirac (ι := Fin 0)]
  simp [φ]

theorem phi_gradient : gradient φ = id := Subsingleton.elim _ _

theorem phi_law : (μ : Measure E) = volume.tilted (-φ) := by
  rw [volume_euclideanSpace_eq_dirac (ι := Fin 0)]
  change Measure.dirac (0 : E) = (Measure.dirac (0 : E)).tilted (-φ)
  have hf : (-φ) = fun _ : E => (0 : ℝ) := by funext x; simp [φ]
  rw [hf]
  exact (tilted_const (Measure.dirac (0 : E)) (0 : ℝ)).symm

theorem gradient_push : (μ : Measure E).map (gradient φ) = (μ : Measure E) := by
  rw [phi_gradient, Measure.map_id]

theorem isotropic : KLS.Isotropic μ where
  memLp_two := by
    have hi : (id : E → E) = 0 := Subsingleton.elim _ _
    rw [hi]
    exact memLp_const (0 : E)
  mean_zero := by
    have hi : (fun x : E => x) = fun _ : E => (0 : E) := Subsingleton.elim _ _
    rw [hi]
    simp
  covariance_identity := Subsingleton.elim _ _

/-- The same actual givenpotential construction and inverse selector works in dimensionzero. -/
theorem actual_constructed_kernel :
    ∃ Ψ : E → E, Measurable Ψ ∧ Function.LeftInverse Ψ (gradient φ) ∧
      Probability.Stein.IsSteinKernel μ (Probability.Stein.hessianKernel φ Ψ) := by
  have hi : Function.Injective (gradient φ) := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨Ψ, hΨ, hinv, hK, _⟩ := KLS.LogConcave.exists_hessianSteinKernel_of_injective_gradient
    φ contDiff_const (convexOn_const 0 convex_univ) phi_normalized μ μ phi_law gradient_push isotropic hi
  exact ⟨Ψ, hΨ, hinv, hK⟩

end HessianSteinAuditZero

#print axioms FunctionalInequalities.Probability.Stein.chain_coordinate
#print axioms FunctionalInequalities.Probability.Stein.hessianKernel_quadratic_nonneg
#print axioms FunctionalInequalities.Probability.Stein.exists_measurable_leftInverse_gradient_of_injective
#print axioms FunctionalInequalities.KLS.LogConcave.hessianKernel_compact_identity
#print axioms FunctionalInequalities.KLS.LogConcave.hessianKernel_isSteinKernel
#print axioms FunctionalInequalities.KLS.LogConcave.integral_hessianKernel_eq_one
#print axioms FunctionalInequalities.KLS.LogConcave.exists_hessianSteinKernel_of_injective_gradient
#print axioms HessianSteinAuditGaussian.actual_hessian_stein
#print axioms HessianSteinAuditGaussian.actual_kernel_mean_one
#print axioms HessianSteinAuditGaussian.actual_constructed_inverse_kernel
#print axioms HessianSteinAuditGaussian.actual_kernel_positive
#print axioms HessianSteinAuditZero.actual_constructed_kernel

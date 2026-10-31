module

public import FunctionalInequalities.Probability.QuadraticTilt

/-!
# Audit: covariance of the quadratic tilt converges (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5 (quadratic tilt step). Clients:
the
two-point law `(δ₀ + δ₂)/2` on `ℝ` (mean `1`, raw second moment `2`, covariance `1`) has tilted
covariances converging to `1` as `δ → 0⁺`, and the tilts keep a finite second moment; the
zero-dimensional law converges to the zero operator.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory FunctionalInequalities Filter
open scoped Topology RealInnerProductSpace

namespace QuadraticCovarianceAudit

noncomputable def atomic : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 2, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩

private theorem integrable_atomic (f : ℝ → ℝ) : Integrable f (atomic : Measure ℝ) := by
  have h0 : Integrable f (Measure.dirac (0 : ℝ)) := integrable_dirac (by simp)
  have h2 : Integrable f (Measure.dirac (2 : ℝ)) := integrable_dirac (by simp)
  exact (h0.smul_measure (by norm_num)).add_measure (h2.smul_measure (by norm_num))

private theorem atomic_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂(atomic : Measure ℝ)) = (1 / 2 : ℝ) * f 0 + (1 / 2 : ℝ) * f 2 := by
  have h0 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h2 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, f x ∂((1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 2)) = _
  rw [integral_add_measure h0 h2, integral_smul_measure, integral_smul_measure]
  simp

theorem atomic_memLp_two : MemLp (id : ℝ → ℝ) 2 (atomic : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr
  exact integrable_atomic (fun x => ‖x‖ ^ 2)

theorem atomic_mean : (∫ x, x ∂(atomic : Measure ℝ)) = 1 := by
  rw [atomic_integral]
  norm_num

theorem atomic_raw_second : (∫ x : ℝ, x ^ 2 ∂(atomic : Measure ℝ)) = 2 := by
  rw [atomic_integral]
  norm_num

/-- Nonzero mean1 and raw second2 yield actual centered covariance1, not raw moment2. -/
theorem atomic_covariance :
    Covariance.operator (atomic : Measure ℝ) = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  have hX : MemLp (fun x : ℝ => ⟪u, x⟫) 2 (atomic : Measure ℝ) := by
    simpa only [id_eq] using atomic_memLp_two.const_inner (𝕜 := ℝ) u
  have hY : MemLp (fun x : ℝ => ⟪v, x⟫) 2 (atomic : Measure ℝ) := by
    simpa only [id_eq] using atomic_memLp_two.const_inner (𝕜 := ℝ) v
  rw [Covariance.operator_inner, covarianceBilin_apply_eq_cov atomic_memLp_two,
    covariance_eq_sub hX hY]
  rw [atomic_integral, atomic_integral, atomic_integral]
  simp only [Pi.mul_apply, Real.inner_apply, ContinuousLinearMap.id_apply]
  ring

/-- The exact generic source limit is consumed on an actual singular/noncentered law. -/
theorem atomic_covariance_limit :
    Tendsto (fun δ : ℝ => Covariance.operator
      ((atomic : Measure ℝ).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (ContinuousLinearMap.id ℝ ℝ)) := by
  have h := Probability.covariance_quadraticTilt_tendsto atomic atomic_memLp_two
  rw [atomic_covariance] at h
  exact h

/-- Tilted L2 is actually obtained on the same nonzero-covariance law. -/
theorem atomic_tilted_memLp_two {δ : ℝ} (hδ : 0 ≤ δ) :
    MemLp (id : ℝ → ℝ) 2 ((atomic : Measure ℝ).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) :=
  Probability.memLp_id_two_quadraticTilt atomic atomic_memLp_two hδ

abbrev ZeroSpace := EuclideanSpace ℝ (Fin 0)
noncomputable def zeroLaw : ProbabilityMeasure ZeroSpace := ⟨Measure.dirac 0, inferInstance⟩

theorem zero_memLp_two : MemLp (id : ZeroSpace → ZeroSpace) 2 (zeroLaw : Measure ZeroSpace) := by
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr
  exact integrable_dirac (by simp)

theorem zero_covariance_limit :
    Tendsto (fun δ : ℝ => Covariance.operator
      ((zeroLaw : Measure ZeroSpace).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ZeroSpace →L[ℝ] ZeroSpace)) := by
  have h := Probability.covariance_quadraticTilt_tendsto zeroLaw zero_memLp_two
  have hc : Covariance.operator (zeroLaw : Measure ZeroSpace) = 0 := Subsingleton.elim _ _
  rw [hc] at h
  exact h

end QuadraticCovarianceAudit

#print axioms FunctionalInequalities.Probability.memLp_id_two_quadraticTilt
#print axioms FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto
#print axioms FunctionalInequalities.Probability.covariance_quadraticTilt_tendsto
#print axioms QuadraticCovarianceAudit.atomic_covariance
#print axioms QuadraticCovarianceAudit.atomic_covariance_limit
#print axioms QuadraticCovarianceAudit.zero_covariance_limit

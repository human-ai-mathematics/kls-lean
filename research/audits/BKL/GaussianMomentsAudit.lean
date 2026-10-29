import FunctionalInequalities.Probability.Gaussian.Moments
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation

open FunctionalInequalities.Probability.Gaussian

/-!
# Audit: moments and weak convergence of the Gaussian smoothing (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5. Clients: smoothing the Dirac
mass at `1` with `s = 3` keeps the mean `1`, has raw second moment `7/6` and variance `1/6`, and its
covariance converges as `s → ∞`; the zero-dimensional law converges weakly and has no spurious
second-moment increment.
-/

open MeasureTheory Filter Topology FunctionalInequalities
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace

namespace GaussianMomentsAudit

private theorem dirac_one_memLp : MemLp id 2 (Measure.dirac (1 : ℝ)) := by
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact integrable_dirac (by simp)

/-- The nonzero source mean is preserved; smoothing does not silently center the source. -/
theorem nonzero_mean : (∫ y : ℝ, y ∂(smoothedLaw (Measure.dirac 1) 3)) = 1 := by
  have h := smoothedLaw_mean (Measure.dirac (1 : ℝ)) dirac_one_memLp (by norm_num : (0 : ℝ) < 3)
  simpa using h

/-- Raw second moment is7/6, while true variance is1/6 for this nonzero source. -/
theorem nonzero_raw_second : (∫ y : ℝ, ‖y‖ ^ 2 ∂(smoothedLaw (Measure.dirac 1) 3)) = 7 / 6 := by
  have h := smoothedLaw_norm_sq (Measure.dirac (1 : ℝ)) dirac_one_memLp (by norm_num : (0 : ℝ) < 3)
  norm_num [Module.finrank_self] at h ⊢
  exact h

theorem nonzero_true_variance :
    ProbabilityTheory.variance (fun y : ℝ => ⟪(1 : ℝ), y⟫) (smoothedLaw (Measure.dirac 1) 3) = 1 / 6 := by
  have h := smoothedLaw_variance (Measure.dirac (1 : ℝ)) dirac_one_memLp
    (by norm_num : (0 : ℝ) < 3) (1 : ℝ)
  norm_num at h ⊢
  exact h

/-- The actual true covariance limit applies to this nonzero, non-isotropic source. -/
theorem nonzero_covariance_limit :
    Tendsto (fun s : ℝ => Covariance.operator (smoothedLaw (Measure.dirac (1 : ℝ)) s))
      atTop (𝓝 (Covariance.operator (Measure.dirac (1 : ℝ)))) :=
  smoothedLaw_covariance_operator_tendsto (Measure.dirac (1 : ℝ)) dirac_one_memLp

private theorem zero_dim_density :
    KLS.IsBorellDensity (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))) volume (fun _ => (1 : ℝ)) := by
  refine ⟨measurable_const, fun _ => zero_le_one, upperSemicontinuous_const, ?_, ?_⟩
  · intro x y t ht0 ht1
    simp
  · simpa using (volume_euclideanSpace_eq_dirac (ι := Fin 0))

/-- Actual dimension-zero source-law weak convergence with the density premise discharged. -/
theorem zero_dim_weak :
    Tendsto (fun n : ℕ => smoothedProbabilityLaw
      (⟨Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)), inferInstance⟩ : ProbabilityMeasure _)
      ((n : ℝ) + 1) (by positivity)) atTop
      (𝓝 (⟨Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)), inferInstance⟩ : ProbabilityMeasure _)) :=
  smoothedProbabilityLaw_tendsto zero_dim_density

/-- Actual zero-dimensional second-moment increment has no spurious positive-dimensional term. -/
theorem zero_dim_second {s : ℝ} (hs : 0 < s) :
    (∫ y : EuclideanSpace ℝ (Fin 0), ‖y‖ ^ 2 ∂(smoothedLaw (Measure.dirac 0) s)) = 0 := by
  have h2 : MemLp id 2 (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))) := by
    apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    exact integrable_dirac (by simp)
  have h := smoothedLaw_norm_sq (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))) h2 hs
  norm_num at h
  exact h

end GaussianMomentsAudit

#print axioms FunctionalInequalities.Probability.Gaussian.laplace
#print axioms FunctionalInequalities.Probability.Gaussian.mean_zero
#print axioms FunctionalInequalities.Probability.Gaussian.integral_inner_sq
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_mean
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covariance_operator
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_norm_sq
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw_covariance_operator_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedProbabilityLaw_tendsto
#print axioms GaussianMomentsAudit.nonzero_mean
#print axioms GaussianMomentsAudit.nonzero_raw_second
#print axioms GaussianMomentsAudit.nonzero_true_variance
#print axioms GaussianMomentsAudit.nonzero_covariance_limit
#print axioms GaussianMomentsAudit.zero_dim_weak
#print axioms GaussianMomentsAudit.zero_dim_second

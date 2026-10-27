import FunctionalInequalities.Probability.Gaussian.Moments
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation

open FunctionalInequalities.Probability.Gaussian

/-!
# Audit: the joint regular approximation (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5. Clients: the Gaussian source law
on `ℝ` with covariance one (variance `1`, not a degenerate witness) has a selected diagonal of regular
approximants with all four limits; the zero-dimensional Dirac law has one too. No whitened
convergence or Poincaré limit is asserted. Clients adapted from the Codex bundle
`Gaussian-Quadratic-Diagonal/Clients.lean` (independently accepted, receipt b147e4f4…).
-/

open scoped RealInnerProductSpace
open MeasureTheory Filter Topology FunctionalInequalities
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

namespace RegularApproximationAudit

private noncomputable def μG : ProbabilityMeasure ℝ :=
  ⟨FunctionalInequalities.Probability.Gaussian.law (1 / 2), FunctionalInequalities.Probability.Gaussian.law_probability (by norm_num)⟩

private theorem gaussian_density :
    KLS.IsBorellDensity (μG : Measure ℝ) volume (normalizedKernel (1 / 2)) := by
  have hs : (0 : ℝ) < 1 / 2 := by norm_num
  refine ⟨normalizedKernel_measurable _, fun y => (normalizedKernel_pos hs y).le, ?_, ?_, rfl⟩
  · apply Continuous.upperSemicontinuous
    unfold normalizedKernel kernel
    fun_prop
  · intro x y t ht0 ht1
    exact normalizedKernel_logConcave hs x y ht0 ht1

private theorem gaussian_L2 : MemLp id 2 (μG : Measure ℝ) := FunctionalInequalities.Probability.Gaussian.memLp_two (by norm_num)

/-- The actual positive-dimensional source has nonzero variance, fixed independently of the
selected diagonal. This rules out a vacuous zero-law interpretation of the main client. -/
theorem actual_gaussian_variance_one :
    ProbabilityTheory.variance (fun y : ℝ => ⟪(1 : ℝ), y⟫) (μG : Measure ℝ) = 1 := by
  have h := FunctionalInequalities.Probability.Gaussian.variance_inner (E := ℝ) (by norm_num : (0 : ℝ) < 1 / 2) (1 : ℝ)
  norm_num [μG] at h ⊢
  exact h

/-- A genuine nondegenerate original source yields actual selected regular approximants and
all four limits. The variance is positive: this source is the kernel with covariance one. -/
theorem actual_gaussian_diagonal :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ n : ℕ, KLS.RegularPotential
        (quadraticPotential (normalizedKernel (V := ℝ) (1 / 2)) ((n : ℝ) + 1) (tiltRate (k n)))
        (tiltRate (k n)) (2 * ((n : ℝ) + 1) + tiltRate (k n))) ∧
      (∀ n : ℕ, 0 < 2 * ((n : ℝ) + 1) + tiltRate (k n)) ∧
      Tendsto (fun n => regularSeq gaussian_density n (k n)) atTop (𝓝 μG) ∧
      Tendsto (fun n => ∫ y : ℝ, y ∂(regularSeq gaussian_density n (k n) : Measure ℝ))
        atTop (𝓝 (∫ y : ℝ, y ∂(μG : Measure ℝ))) ∧
      Tendsto (fun n => ∫ y : ℝ, ‖y‖ ^ 2 ∂(regularSeq gaussian_density n (k n) : Measure ℝ))
        atTop (𝓝 (∫ y : ℝ, ‖y‖ ^ 2 ∂(μG : Measure ℝ))) ∧
      Tendsto (fun n => Covariance.operator (regularSeq gaussian_density n (k n) : Measure ℝ))
        atTop (𝓝 (Covariance.operator (μG : Measure ℝ))) :=
  exists_regularSeq_limits gaussian_density gaussian_L2

private noncomputable def μ0 : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)) :=
  ⟨Measure.dirac 0, inferInstance⟩

private theorem zero_density :
    KLS.IsBorellDensity (μ0 : Measure (EuclideanSpace ℝ (Fin 0))) volume (fun _ => (1 : ℝ)) := by
  refine ⟨measurable_const, fun _ => zero_le_one, upperSemicontinuous_const, ?_, ?_⟩
  · intro x y t ht0 ht1
    simp
  · change (volume : Measure (EuclideanSpace ℝ (Fin 0))).withDensity
      (fun _ => ENNReal.ofReal (1 : ℝ)) = Measure.dirac 0
    simpa using (volume_euclideanSpace_eq_dirac (ι := Fin 0))

private theorem zero_L2 : MemLp id 2 (μ0 : Measure (EuclideanSpace ℝ (Fin 0))) := by
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact integrable_dirac (by simp)

/-- A true dimension-zero source still has actual positive parameters and all law/stat limits. -/
theorem zero_dim_diagonal :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => rowLaw μ0 n (k n)) atTop (𝓝 μ0) ∧
      Tendsto (fun n => ∫ y : EuclideanSpace ℝ (Fin 0), y
        ∂(rowLaw μ0 n (k n) : Measure (EuclideanSpace ℝ (Fin 0)))) atTop (𝓝 (∫ y, y ∂(μ0 : Measure (EuclideanSpace ℝ (Fin 0))))) ∧
      Tendsto (fun n => ∫ y : EuclideanSpace ℝ (Fin 0), ‖y‖ ^ 2
        ∂(rowLaw μ0 n (k n) : Measure (EuclideanSpace ℝ (Fin 0)))) atTop (𝓝 (∫ y, ‖y‖ ^ 2 ∂(μ0 : Measure (EuclideanSpace ℝ (Fin 0))))) ∧
      Tendsto (fun n => Covariance.operator (rowLaw μ0 n (k n) : Measure (EuclideanSpace ℝ (Fin 0))))
        atTop (𝓝 (Covariance.operator (μ0 : Measure (EuclideanSpace ℝ (Fin 0))))) :=
  exists_diagonal_limits zero_density zero_L2

end RegularApproximationAudit

#print axioms FunctionalInequalities.Analysis.exists_metric_diagonal
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_joint_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.row_joint_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_diagonal_limits
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_regular_approximation_limits
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_regularSeq_limits
#print axioms RegularApproximationAudit.actual_gaussian_variance_one
#print axioms RegularApproximationAudit.actual_gaussian_diagonal
#print axioms RegularApproximationAudit.zero_dim_diagonal

import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Posterior
import FunctionalInequalities.KLS.LogConcave.Isotropic
import FunctionalInequalities.KLS.LogConcave.Density.Tilted

/-!
# Audit: Gaussian posterior, centering and uniform moments (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5 (regular approximation; moment
inputs for the polynomial growth of the smoothed potential's derivatives). Clients: the standard
Gaussian source on `ℝ` at base point `2`, `s = 3`, direction `1` (variance and trace `≤ 1/6`, fourth
moment with the shared constant), dimension-zero moments, and all moments of isotropic log-concave
laws on `ℝⁿ` through the quantitative Borell bounds. Neither all-order potential growth nor the
regular approximation theorem is asserted.
-/

open MeasureTheory ProbabilityTheory Set FunctionalInequalities
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace

namespace GaussianPosteriorAudit

private noncomputable def W (y : ℝ) : ℝ := (1 / 2 : ℝ) * ‖y‖ ^ 2

private theorem W_integrable : Integrable (fun y : ℝ => Real.exp (-W y)) volume := by
  have h := FunctionalInequalities.Probability.Gaussian.integrable_kernel (V := ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  change Integrable (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * ‖y‖ ^ 2)) volume at h
  convert h using 1
  funext y
  congr 1
  change -((1 / 2 : ℝ) * ‖y‖ ^ 2) = -(1 / 2 : ℝ) * ‖y‖ ^ 2
  ring

/-- The standard Gaussian law on `ℝ` as a probability law. -/
noncomputable def gaussianSource : ProbabilityMeasure ℝ :=
  ⟨volume.tilted (-W), isProbabilityMeasure_tilted W_integrable⟩

private theorem gaussian_source_density :
    KLS.IsBorellDensity (gaussianSource : Measure ℝ) volume
      (fun y => Real.exp (-W y) / ∫ z, Real.exp (-W z) ∂volume) := by
  apply KLS.LogConcave.isBorellDensity_of_eq_tilted (W := W) rfl (by
    change Continuous (fun y : ℝ => (1 / 2 : ℝ) * ‖y‖ ^ 2)
    fun_prop)
  change ConvexOn ℝ univ (fun y : ℝ => (1 / 2 : ℝ) * ‖y‖ ^ 2)
  have hcv : ConvexOn ℝ univ (fun y : ℝ => ‖y‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  exact hcv.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem concrete_gaussian_posterior :
    let hs : (0 : ℝ) < 3 := by norm_num
    let Q := centeredPosteriorLaw (gaussianSource : Measure ℝ) hs 2
    KLS.BorelLogConcave Q ∧ MemLp id 2 (Q : Measure ℝ) ∧
      (∫ y, y ∂(Q : Measure ℝ)) = 0 ∧
      variance (fun y : ℝ => ⟪y, (1 : ℝ)⟫) (Q : Measure ℝ) ≤ 1 / 6 ∧
      (∫ y, ‖y‖ ^ 2 ∂(Q : Measure ℝ)) ≤ 1 / 6 := by
  dsimp only
  let hs : (0 : ℝ) < 3 := by norm_num
  obtain ⟨hlc, h2, hm, hv, htr⟩ := centeredPosteriorLaw_data gaussian_source_density hs 2
  refine ⟨hlc, h2, hm, ?_, ?_⟩
  · have hv1 := hv 1
    norm_num at hv1 ⊢
    exact hv1
  · norm_num [Module.finrank_self] at htr ⊢
    exact htr

theorem concrete_gaussian_fourth_moment :
    let hs : (0 : ℝ) < 3 := by norm_num
    let Q := centeredPosteriorLaw (gaussianSource : Measure ℝ) hs 2
    let R : ℝ := 2 * Real.sqrt (1 / 6 + 1)
    Integrable (fun y : ℝ => ‖y‖ ^ 4) (Q : Measure ℝ) ∧
      (∫ y, ‖y‖ ^ 4 ∂(Q : Measure ℝ)) ≤
        24 / (Real.log 3 / (4 * R)) ^ 4 *
          ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  have h := integral_norm_pow_centeredPosteriorLaw_le gaussian_source_density
    (by norm_num : (0 : ℝ) < 3) (2 : ℝ) 4
  norm_num only [Module.finrank_self, Nat.factorial_succ, Nat.factorial_zero, Nat.cast_ofNat] at h
  convert h using 1
  norm_num

theorem zero_dimension_positive_moment {μ : Measure (EuclideanSpace ℝ (Fin 0))}
    [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin 0)) :
    (∫ y, ‖y‖ ^ 3 ∂(centeredPosteriorLaw μ hs x : Measure (EuclideanSpace ℝ (Fin 0)))) = 0 := by
  have hz : (fun y : EuclideanSpace ℝ (Fin 0) => ‖y‖ ^ 3) = fun _ => (0 : ℝ) := by
    funext y
    rw [Subsingleton.elim y 0]
    simp
  rw [hz, integral_zero]

theorem zero_dimension_order_zero {μ : Measure (EuclideanSpace ℝ (Fin 0))}
    [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin 0)) :
    (∫ y, ‖y‖ ^ 0 ∂(centeredPosteriorLaw μ hs x : Measure (EuclideanSpace ℝ (Fin 0)))) = 1 := by
  simp

/-- Isotropic log-concave laws on `ℝ²` have a fourth moment bounded by a universal constant. -/
theorem isotropic_plane_fourth_moment (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (hlc : KLS.LogConcave ν) (hiso : KLS.Isotropic ν) :
    Integrable (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖ ^ 4) (ν : Measure (EuclideanSpace ℝ (Fin 2))) :=
  (KLS.LogConcave.integral_norm_pow_le_of_isotropic hlc hiso 4).1

end GaussianPosteriorAudit

#print axioms FunctionalInequalities.KLS.BorelLogConcave.integral_exp_norm_le_of_ball
#print axioms FunctionalInequalities.KLS.BorelLogConcave.integral_norm_pow_le_of_ball
#print axioms FunctionalInequalities.Probability.measure_ball_ge_of_integral_norm_sq_le
#print axioms FunctionalInequalities.KLS.BorelLogConcave.integral_norm_pow_le_of_second_moment
#print axioms FunctionalInequalities.KLS.BorelLogConcave.integral_norm_pow_le_of_second_bound
#print axioms FunctionalInequalities.KLS.Isotropic.integral_norm_sq
#print axioms FunctionalInequalities.KLS.LogConcave.integral_norm_pow_le_of_isotropic
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.posteriorLaw_isBorellDensity
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.posteriorLaw_logConcave
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.coe_centeredPosteriorLaw
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.centeredPosteriorLaw_logConcave
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.memLp_two_id_centeredPosteriorLaw
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_id_centeredPosteriorLaw
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.variance_inner_centeredPosteriorLaw
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.variance_inner_centeredPosteriorLaw_le
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_norm_sq_centeredPosteriorLaw_le
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.centeredPosteriorLaw_data
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_norm_pow_centeredPosteriorLaw_le
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integral_exp_norm_centeredPosteriorLaw_le
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.centeredPosteriorRate_pos
#print axioms GaussianPosteriorAudit.concrete_gaussian_posterior
#print axioms GaussianPosteriorAudit.concrete_gaussian_fourth_moment
#print axioms GaussianPosteriorAudit.zero_dimension_positive_moment
#print axioms GaussianPosteriorAudit.zero_dimension_order_zero
#print axioms GaussianPosteriorAudit.isotropic_plane_fourth_moment

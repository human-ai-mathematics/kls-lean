import FunctionalInequalities.KLS.BKL.PosteriorResponse
import FunctionalInequalities.KLS.BKL.PosteriorCovariance
import FunctionalInequalities.Probability.Posterior.Generator
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
import FunctionalInequalities.KLS.LogConcave.Regular
import FunctionalInequalities.KLS.BKL.GaussianTaylor
import FunctionalInequalities.KLS.LogConcave.Line.Poincare

/-!
# Audit: parameter response, generator and log-concavity of the BKL posterior (67)–(68)

Source: Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, the compact stage before (67) and the
deterministic parameter response of (67). Clients compiled against the accepted
`Probability/Posterior/*` owners and `KLS/BKL/PosteriorResponse.lean`: the one-dimensional Gaussian
prior (log-concave, isotropic, unbounded) has coercive posterior response `1/2` in the linear parameter
at `Q = Id`; the rank-zero compact source has response `0` at `c = Q = 0`; for the generator (`Probability/Posterior/Generator.lean`): a noncentered two-point
prior with covariance `3/4` where the three generator terms are `1/2`, `−1`, `1/2` at the inverse rate
`M = 4/3`, the rank-zero source, and the root reviewer's basis-independence and negative-rate
consumers. Client bodies: Codex q_batch bundles `Posterior-Parameter-Calculus` (receipt 35b40b51…) and
`Posterior-Generator-Cancellation` (receipt e9d04efb…), both independently accepted; the two root
reviewer consumers are credited as such. Log-concavity clients (`KLS/BKL/PosteriorDomain.lean`,
bundle `Posterior-LogConcavity`, receipt 4ad0ef6c…): the uniform law on `[0,1]` with `c = 2`, `Q = 3·Id` and
`Q = 0`, a segment law on a line in `ℝ²` (singular, no ambient density), and rank zero. Joint `(c,Q)` regularity
clients (`Probability/Posterior/JointRegularity.lean`, `KLS/BKL/PosteriorDomain.lean` section JointCoefficients;
bundles `Posterior-Joint-Regularity` receipt fcb40842…/0b9bb359… and `Principal-Root-Regularity` receipt
94bf7e52…, both independently accepted): a noncentered two-point prior with a measurable statistic that is
discontinuous and unbounded off the support, the mixed parameter curve `t ↦ (2t, t·Id)` with derivative `1` at
`0`, signed `Q`, the symmetric two-atom isotropic prior (inverse/drift smooth, initial rate `Id`, principal root
locally Lipschitz with initial value `Id`), and rank zero. No stochastic equation, Itô formula or martingale
statement is involved.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set FunctionalInequalities
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff

namespace ActualPosteriorParameterClients

private def μG : ProbabilityMeasure ℝ :=
  ⟨gaussianLaw (1 / 2), gaussianLaw_probability (by norm_num)⟩

private theorem prior_variance_one : variance id (μG : Measure ℝ) = 1 := by
  have h := gaussianLaw_variance (E := ℝ) (by norm_num : (0 : ℝ) < 1 / 2) (1 : ℝ)
  norm_num [μG, Real.inner_apply] at h ⊢
  exact h

theorem actual_gaussian_source : KLS.LogConcave μG ∧ KLS.Isotropic μG := by
  have hG := KLS.regularPotential_half_norm_sq (E := ℝ)
  have hLaw : μG = hG.law := by
    apply ProbabilityMeasure.toMeasure_injective
    change gaussianLaw (V := ℝ) (1 / 2) = (volume : Measure ℝ).tilted (-fun x => ‖x‖ ^ 2 / 2)
    rw [gaussianLaw_eq_tilted (by norm_num)]
    congr 1
    funext x
    simp only [Pi.neg_apply]
    ring
  refine ⟨by rw [hLaw]; exact hG.logConcave_law, ?_⟩
  refine ⟨gaussianLaw_memLp_two (by norm_num), gaussianLaw_mean_zero (by norm_num), ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [Covariance.operator_inner, covarianceBilin_real, prior_variance_one,
    ContinuousLinearMap.id_apply, Real.inner_apply, mul_one]

private theorem posterior_gaussian :
    (μG : Measure ℝ).tilted (Probability.Posterior.quadraticExponent (0 : ℝ) (ContinuousLinearMap.id ℝ ℝ)) = gaussianLaw 1 := by
  have he : Probability.Posterior.quadraticExponent (0 : ℝ) (ContinuousLinearMap.id ℝ ℝ) = fun x => -(1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    funext x
    simp only [Probability.Posterior.quadraticExponent, inner_zero_left, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
    ring
  change (gaussianLaw (V := ℝ) (1 / 2)).tilted _ = _
  rw [he, gaussianLaw_eq_tilted (by norm_num),
    tilted_tilted (integrable_kernel (by norm_num : (0 : ℝ) < 1 / 2)),
    gaussianLaw_eq_tilted (by norm_num : (0 : ℝ) < 1)]
  congr 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- The actual coercive posterior c-response is nonzero 1/2. Its prior is genuinely
isotropic log-concave and unbounded; this does not invoke the compact-prior endpoint. -/
theorem gaussian_coercive_response_half :
    HasDerivAt (fun t : ℝ => ∫ x : ℝ, x
      ∂((μG : Measure ℝ).tilted (Probability.Posterior.quadraticExponent t (ContinuousLinearMap.id ℝ ℝ)))) (1 / 2) 0 := by
  have hQ : ∀ x : ℝ, (1 : ℝ) * ‖x‖ ^ 2 ≤ ⟪(ContinuousLinearMap.id ℝ ℝ) x, x⟫ := by
    intro x
    rw [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, one_mul]
  have hd := Probability.Posterior.expectation_hasDerivAt_quadraticExponent_of_coercive μG (0 : ℝ) 1 (ContinuousLinearMap.id ℝ ℝ) 0
    (a := 1) (by norm_num) hQ (f := id) measurable_id (C := 1) (by norm_num) 1
    (by intro x; simp only [id_eq, pow_one, one_mul]; linarith)
  have hg : Probability.Posterior.quadraticExponent (1 : ℝ) (0 : ℝ →L[ℝ] ℝ) = id := by
    funext x
    simp [Probability.Posterior.quadraticExponent]
  have hcov : covariance id (Probability.Posterior.quadraticExponent (1 : ℝ) (0 : ℝ →L[ℝ] ℝ))
      ((μG : Measure ℝ).tilted (Probability.Posterior.quadraticExponent (0 : ℝ) (ContinuousLinearMap.id ℝ ℝ))) = 1 / 2 := by
    rw [hg, posterior_gaussian]
    change covariance (fun x : ℝ => x) (fun x : ℝ => x) (gaussianLaw 1) = 1 / 2
    rw [covariance_self aemeasurable_id']
    have hv := gaussianLaw_variance (E := ℝ) (by norm_num : (0 : ℝ) < 1) (1 : ℝ)
    norm_num [Real.inner_apply] at hv ⊢
    exact hv
  simpa only [smul_zero, add_zero, smul_eq_mul, mul_one, zero_add, hcov, id_eq] using hd

abbrev E0 := EuclideanSpace ℝ (Fin 0)
private def μ0 : ProbabilityMeasure E0 := ⟨Measure.dirac 0, inferInstance⟩

private theorem zero_compact : IsCompact (μ0 : Measure E0).support :=
  isCompact_univ.of_isClosed_subset (Measure.isClosed_support (μ := (μ0 : Measure E0))) (Set.subset_univ _)

private theorem zero_isotropic : KLS.Isotropic μ0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr
    exact integrable_dirac (by simp)
  · simp [μ0]
  · exact Subsingleton.elim _ _

theorem actual_zero_source : KLS.LogConcave μ0 ∧ KLS.Isotropic μ0 :=
  ⟨KLS.logConcave_dirac 0, zero_isotropic⟩

/-- The actual rank-zero compact source consumes c=Q=0, with true derivative zero. -/
theorem actual_zero_response :
    HasDerivAt (fun t : ℝ => ∫ x : E0, ⟪(0 : E0), x⟫
      ∂((μ0 : Measure E0).tilted (fun x => t * ⟪(0 : E0), x⟫))) 0 0 := by
  simpa only [inner_zero_left] using
    KLS.Isotropic.posterior_linear_response μ0 zero_compact zero_isotropic 0 0
end ActualPosteriorParameterClients

namespace ActualGeneratorBoundary
abbrev E0 := EuclideanSpace ℝ (Fin 0)
private def μ0 : ProbabilityMeasure E0 := ⟨Measure.dirac 0, inferInstance⟩

/-- The actual empty-dimensional source consumes the complete generator endpoint. -/
theorem actual_zero_dim_generator :
    fderiv ℝ (fun y : E0 => posteriorExpectation μ0 y 0 (fun _ => (1 : ℝ))) 0
        ((0 : E0 →L[ℝ] E0) (posteriorMean μ0 0 0)) +
      deriv (fun t : ℝ => posteriorExpectation μ0 0 (0 + t • (0 : E0 →L[ℝ] E0)) (fun _ => (1 : ℝ))) 0 +
      (1 / 2 : ℝ) * (∑ i : Fin 0, bilinearIteratedFDerivTwo ℝ
        (fun y : E0 => posteriorExpectation μ0 y 0 (fun _ => (1 : ℝ))) 0
        ((0 : E0 →L[ℝ] E0) (EuclideanSpace.basisFun (Fin 0) ℝ i))
        (EuclideanSpace.basisFun (Fin 0) ℝ i)) = 0 := by
  have hc : IsCompact (μ0 : Measure E0).support :=
    isCompact_univ.of_isClosed_subset (Measure.isClosed_support (μ := (μ0 : Measure E0))) (Set.subset_univ _)
  exact posteriorExpectation_generator_cancellation μ0 hc (f := fun _ => (1 : ℝ)) measurable_const
    (C := 1) (by norm_num) (by intro x hx; simp) 0 0 0 (EuclideanSpace.basisFun (Fin 0) ℝ)
    (by intro u v; simp)
end ActualGeneratorBoundary

namespace ActualGeneratorClients

private def μ : ProbabilityMeasure ℝ :=
  ⟨ENNReal.ofReal (3 / 4) • Measure.dirac 0 + ENNReal.ofReal (1 / 4) • Measure.dirac 2, by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num⟩

private theorem integral_μ (f : ℝ → ℝ) :
    (∫ x, f x ∂(μ : Measure ℝ)) = (3 / 4 : ℝ) * f 0 + (1 / 4 : ℝ) * f 2 := by
  have h0 : Integrable f (ENNReal.ofReal (3 / 4) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  have h2 : Integrable f (ENNReal.ofReal (1 / 4) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  change (∫ x, f x ∂(ENNReal.ofReal (3 / 4) • Measure.dirac 0 + ENNReal.ofReal (1 / 4) • Measure.dirac 2)) = _
  rw [integral_add_measure h0 h2, integral_smul_measure, integral_smul_measure]
  norm_num

private theorem support_subset : (μ : Measure ℝ).support ⊆ ({(0 : ℝ), 2} : Set ℝ) := by
  apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
  rw [mem_ae_iff]
  change ((ENNReal.ofReal (3 / 4) • Measure.dirac (0 : ℝ) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (2 : ℝ)) ({(0 : ℝ), 2} : Set ℝ)ᶜ) = 0
  simp

private theorem hc : IsCompact (μ : Measure ℝ).support :=
  (Set.toFinite ({(0 : ℝ), 2} : Set ℝ)).isCompact.of_isClosed_subset
    (μ : Measure ℝ).isClosed_support support_subset

private theorem hb : ∀ x ∈ (μ : Measure ℝ).support, ‖id x‖ ≤ (2 : ℝ) := by
  intro x hx
  rcases support_subset hx with h | h
  · subst x
    norm_num
  · simp only [Set.mem_singleton_iff] at h
    subst x
    norm_num

private theorem hzero : quadraticExponent (0 : ℝ) (0 : ℝ →L[ℝ] ℝ) = 0 := by funext x; simp [quadraticExponent]
private theorem h2 (f : ℝ → ℝ) (hf : Continuous f) : MemLp f 2 (μ : Measure ℝ) := by
  have h := memLp_two_tilted_quadraticExponent_of_compact μ hc 0 0 hf
  simpa only [hzero, tilted_zero] using h

private def M : ℝ →L[ℝ] ℝ := (4 / 3 : ℝ) • ContinuousLinearMap.id ℝ ℝ
private def b := (OrthonormalBasis.singleton (Fin 1) ℝ)

private theorem mean_half : posteriorMean μ 0 0 = (1 / 2 : ℝ) := by
  unfold posteriorMean
  rw [hzero, tilted_zero, integral_μ]
  norm_num

private theorem cov_id : covariance id id (μ : Measure ℝ) = (3 / 4 : ℝ) := by
  rw [covariance_eq_sub (h2 id continuous_id) (h2 id continuous_id)]
  simp only [integral_μ]
  norm_num

private theorem cov_square : covariance id (fun x : ℝ => x ^ 2) (μ : Measure ℝ) = (3 / 2 : ℝ) := by
  rw [covariance_eq_sub (h2 id continuous_id) (h2 (fun x : ℝ => x ^ 2) (by fun_prop))]
  simp only [integral_μ]
  norm_num

/-- The model's covariance is `3/4 · Id`, so `M = 4/3` is its inverse. -/
theorem actual_inverse :
    (Covariance.operator (μ : Measure ℝ)).comp M = ContinuousLinearMap.id ℝ ℝ ∧
      M.comp (Covariance.operator (μ : Measure ℝ)) = ContinuousLinearMap.id ℝ ℝ := by
  have hA : Covariance.operator (μ : Measure ℝ) = (3 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    rw [Covariance.operator_inner, covarianceBilin_real]
    have hv : variance id (μ : Measure ℝ) = (3 / 4 : ℝ) := by
      have h := cov_id
      change covariance (fun x : ℝ => x) (fun x : ℝ => x) (μ : Measure ℝ) = 3 / 4 at h
      rwa [covariance_self aemeasurable_id'] at h
    rw [hv]
    simp only [smul_apply, ContinuousLinearMap.id_apply, Real.inner_apply]
    ring
  rw [hA]
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    simp only [M, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
    ring
  · apply ContinuousLinearMap.ext
    intro x
    simp only [M, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
    ring

/-- All three generator terms are nonzero (`1/2`, `−1`, `1/2`) and cancel. -/
theorem actual_three_terms :
    fderiv ℝ (fun y => posteriorExpectation μ y 0 id) 0 (M (posteriorMean μ 0 0)) = (1 / 2 : ℝ) ∧
      deriv (fun t : ℝ => posteriorExpectation μ 0 (t • M) id) 0 = -1 ∧
      (1 / 2 : ℝ) * (∑ i : Fin 1, bilinearIteratedFDerivTwo ℝ
        (fun y => posteriorExpectation μ y 0 id) 0 (M (b i)) (b i)) = (1 / 2 : ℝ) := by
  have hM : ∀ u v : ℝ, ⟪M u, v⟫ = ⟪u, M v⟫ := by
    intro u v
    simp only [M, smul_apply, ContinuousLinearMap.id_apply, Real.inner_apply]
    ring
  have hlin := fderiv_posteriorExpectation_c_apply μ hc measurable_id (by norm_num : (0 : ℝ) ≤ 2) hb 0 0
    (M (posteriorMean μ 0 0))
  rw [hzero, tilted_zero, mean_half] at hlin
  have hlfun : (fun x : ℝ => ⟪M (1 / 2), x⟫) = fun x => (2 / 3 : ℝ) * id x := by
    funext x
    simp only [M, smul_apply, ContinuousLinearMap.id_apply, Real.inner_apply, id_eq]
    ring
  rw [hlfun, covariance_const_mul_right, cov_id] at hlin
  have hcoef : (2 / 3 : ℝ) * (3 / 4) = 1 / 2 := by norm_num
  rw [hcoef] at hlin
  have hq := (posteriorExpectation_hasDerivAt_Q μ hc measurable_id (by norm_num : (0 : ℝ) ≤ 2) hb 0 0 M).deriv
  rw [hzero, tilted_zero] at hq
  have hqfun : (fun x : ℝ => ⟪M x, x⟫) = fun x => (4 / 3 : ℝ) * x ^ 2 := by
    funext x
    simp only [M, smul_apply, ContinuousLinearMap.id_apply, Real.inner_apply]
    ring
  rw [hqfun, covariance_const_mul_right, cov_square] at hq
  norm_num at hq
  have hgen := posteriorExpectation_generator_cancellation μ hc measurable_id (by norm_num : (0 : ℝ) ≤ 2) hb 0 0 M b hM
  simp only [zero_add] at hq hgen
  refine ⟨by simpa only [mean_half] using hlin, hq, ?_⟩
  rw [mean_half, hlin, hq] at hgen
  have hgen' : (1 / 2 : ℝ) + -1 + (1 / 2 : ℝ) *
      (∑ i : Fin 1, bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y 0 id) 0 (M (b i)) (b i)) = 0 := by
    convert! hgen using 1
  linarith only [hgen']
end ActualGeneratorClients

namespace IndependentPosteriorGenerator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Hessian trace is independent of the orthonormal basis (Codex root reviewer). -/
theorem trace_independent (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q M : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (d : OrthonormalBasis κ ℝ E)
    (hM : ∀ u v : E, ⟪M u, v⟫ = ⟪u, M v⟫) :
    (∑ i, bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c (M (b i)) (b i)) =
      ∑ j, bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c (M (d j)) (d j) := by
  rw [sum_bilinearIteratedFDerivTwo_posteriorExpectation_c μ hc hf hC hfb c Q M b hM,
    sum_bilinearIteratedFDerivTwo_posteriorExpectation_c μ hc hf hC hfb c Q M d hM]

/-- The identity holds for the negative symmetric rate `−Id` as well: a calculus consumer, with no claim that
the rate is a diffusion covariance (Codex root reviewer). -/
theorem negative_rate (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) :
    let M := -(ContinuousLinearMap.id ℝ E)
    fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (M (posteriorMean μ c Q)) +
      deriv (fun t : ℝ => posteriorExpectation μ c (Q + t • M) f) 0 +
      (1 / 2 : ℝ) * (∑ i, bilinearIteratedFDerivTwo ℝ
        (fun y => posteriorExpectation μ y Q f) c (M (b i)) (b i)) = 0 := by
  apply posteriorExpectation_generator_cancellation μ hc hf hC hfb c Q _ b
  intro u v
  simp
end IndependentPosteriorGenerator

namespace ActualPosteriorLogConcavity

def uniform : ProbabilityMeasure ℝ := ⟨volume.restrict (Icc (0 : ℝ) 1), by
  constructor
  simp⟩

private def ρ : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (fun _ => 1)

theorem uniform_density : KLS.IsBorellDensity (uniform : Measure ℝ) volume ρ := by
  refine ⟨measurable_const.indicator measurableSet_Icc, ?_,
    isClosed_Icc.upperSemicontinuous_indicator (by norm_num : (0 : ℝ) ≤ 1), ?_, ?_⟩
  · intro x
    exact indicator_nonneg (by intro x hx; norm_num) x
  · intro x y t ht0 ht1
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · by_cases hy : y ∈ Icc (0 : ℝ) 1
      · have hm : t • x + (1 - t) • y ∈ Icc (0 : ℝ) 1 :=
          (convex_Icc (0 : ℝ) 1) hx hy ht0.le (by linarith) (by ring)
        simp only [ρ, indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hm, Real.one_rpow,
          mul_one, le_refl]
      · simp only [ρ, indicator_of_notMem hy, Real.zero_rpow (by linarith : (1 - t) ≠ 0), mul_zero]
        exact indicator_nonneg (by intro z hz; norm_num) _
    · simp only [ρ, indicator_of_notMem hx, Real.zero_rpow ht0.ne', zero_mul]
      exact indicator_nonneg (by intro z hz; norm_num) _
  · have he : (fun x => ENNReal.ofReal (ρ x)) = (Icc (0 : ℝ) 1).indicator 1 := by
      funext x
      by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [ρ, hx]
    rw [he, withDensity_indicator_one measurableSet_Icc]
    rfl

theorem uniform_logConcave : KLS.LogConcave uniform := uniform_density.compactLogConcave

theorem uniform_compact : IsCompact (uniform : Measure ℝ).support := by
  have ha : Icc (0 : ℝ) 1 ∈ ae (uniform : Measure ℝ) := by
    rw [mem_ae_iff]
    simp [uniform]
  exact isCompact_Icc.of_isClosed_subset (uniform : Measure ℝ).isClosed_support
    (Measure.support_subset_of_isClosed isClosed_Icc ha)

private def Q : ℝ →L[ℝ] ℝ := (3 : ℝ) • ContinuousLinearMap.id ℝ ℝ

private theorem Q_selfAdjoint : IsSelfAdjoint Q := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  change ⟪Q u, v⟫ = ⟪u, Q v⟫
  simp only [Q, smul_apply, ContinuousLinearMap.id_apply, Real.inner_apply, smul_eq_mul]
  ring

/-- A genuine non-Gaussian source with density zeros, nonzero c and positive quadratic rate. -/
theorem uniform_nonzero_posterior : KLS.LogConcave (compactPosterior uniform uniform_compact 2 Q) :=
  KLS.compactPosterior_logConcave uniform uniform_compact uniform_logConcave 2 Q Q_selfAdjoint
    (by intro x; simp only [Q, smul_apply, ContinuousLinearMap.id_apply,
      Real.inner_apply, smul_eq_mul]; nlinarith [sq_nonneg x])

/-- The published one-half convention is exercised at an actual nonzero source point. -/
theorem actual_exponent_half : quadraticExponent (2 : ℝ) Q 1 = (1 / 2 : ℝ) := by
  norm_num [quadraticExponent, Q, Real.inner_apply]

/-- The merely semidefinite initialization rate Q=0 is allowed, for any actual linear parameter. -/
theorem uniform_linear_tilt (c : ℝ) :
    KLS.LogConcave (compactPosterior uniform uniform_compact c 0) := by
  apply KLS.compactPosterior_logConcave uniform uniform_compact uniform_logConcave c 0
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro u v
    simp
  · intro x
    simp

abbrev E0 := EuclideanSpace ℝ (Fin 0)
def μ0 : ProbabilityMeasure E0 := ⟨Measure.dirac 0, inferInstance⟩
private theorem μ0_compact : IsCompact (μ0 : Measure E0).support :=
  isCompact_univ.of_isClosed_subset (μ0 : Measure E0).isClosed_support (subset_univ _)

/-- Actual rank0 compact/LC input; nonnegative Q condition and posterior LC are genuinely derived. -/
theorem rank0_posterior (c : E0) (Q0 : E0 →L[ℝ] E0) :
    KLS.LogConcave (compactPosterior μ0 μ0_compact c Q0) := by
  have hLC : KLS.LogConcave μ0 := by
    simpa only [μ0, Probability.ofMeasure] using KLS.logConcave_dirac (0 : E0)
  have hSym : IsSelfAdjoint Q0 := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro u v
    change ⟪Q0 u, v⟫ = ⟪u, Q0 v⟫
    have hu : u = 0 := Subsingleton.elim _ _
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hu, hv]
  have hQ : ∀ x, 0 ≤ ⟪Q0 x, x⟫ := by
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  exact KLS.compactPosterior_logConcave μ0 μ0_compact hLC c Q0 hSym hQ
end ActualPosteriorLogConcavity

namespace ActualPosteriorSingularLogConcavity
open ActualPosteriorLogConcavity
abbrev E := EuclideanSpace ℝ (Fin 2)
private def v : E := EuclideanSpace.single 0 1
private theorem hv : ‖v‖ = 1 := by
  simp [v, EuclideanSpace.single]
private def e : ℝ →ᵃⁱ[ℝ] E := (LinearIsometry.toSpanSingleton ℝ E hv).toAffineIsometry
def μ : ProbabilityMeasure E := uniform.map e.continuous.measurable.aemeasurable

theorem genuine_singular_prior_logConcave : KLS.LogConcave μ :=
  KLS.LogConcave.map_affineIsometry uniform uniform_logConcave μ e rfl

theorem genuine_singular_prior_compact : IsCompact (μ : Measure E).support := by
  have hk : IsCompact (e '' Icc (0 : ℝ) 1) := isCompact_Icc.image e.continuous
  have ha : e '' Icc (0 : ℝ) 1 ∈ ae (μ : Measure E) := by
    rw [mem_ae_iff]
    change ((uniform : Measure ℝ).map e) (e '' Icc (0 : ℝ) 1)ᶜ = 0
    rw [Measure.map_apply e.continuous.measurable hk.isClosed.measurableSet.compl]
    apply measure_mono_null ?_ (by simp [uniform] :
      (uniform : Measure ℝ) (Icc (0 : ℝ) 1)ᶜ = 0)
    intro x hx hxi
    exact hx ⟨x, hxi, rfl⟩
  exact hk.of_isClosed_subset (μ : Measure E).isClosed_support
    (Measure.support_subset_of_isClosed hk.isClosed ha)

private def Q : E →L[ℝ] E := (3 : ℝ) • ContinuousLinearMap.id ℝ E
private theorem hSym : IsSelfAdjoint Q := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u w
  change ⟪Q u, w⟫ = ⟪u, Q w⟫
  simp only [Q, smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left, inner_smul_right]

/-- An actual nontrivial segment law on a lower-dimensional ambient subspace consumes the
source endpoint. No ambient Haar density or full affine support field is supplied. -/
theorem singular_nonzero_posterior :
    KLS.LogConcave (compactPosterior μ genuine_singular_prior_compact (e 2) Q) := by
  apply KLS.compactPosterior_logConcave μ genuine_singular_prior_compact
    genuine_singular_prior_logConcave (e 2) Q hSym
  intro x
  simp only [Q, smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left]
  exact mul_nonneg (by norm_num) (real_inner_self_nonneg)
end ActualPosteriorSingularLogConcavity

#print axioms FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact
#print axioms FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_quadraticExponent_of_coercive
#print axioms FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_quadraticExponent_of_compact
#print axioms FunctionalInequalities.Probability.Posterior.isProbabilityMeasure_tilted_quadraticExponent_of_coercive
#print axioms FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_polynomial
#print axioms FunctionalInequalities.Probability.Posterior.exists_uniform_norm_moments_tilted_quadraticExponent_of_compact
#print axioms FunctionalInequalities.Probability.Posterior.norm_integral_tilted_le_of_compact
#print axioms FunctionalInequalities.KLS.Isotropic.posterior_linear_response
#print axioms FunctionalInequalities.KLS.Isotropic.posterior_response_real
#print axioms FunctionalInequalities.KLS.Isotropic.posterior_response_pos
#print axioms ActualPosteriorParameterClients.actual_gaussian_source
#print axioms ActualPosteriorParameterClients.gaussian_coercive_response_half
#print axioms ActualPosteriorParameterClients.actual_zero_source
#print axioms ActualPosteriorParameterClients.actual_zero_response
#print axioms FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact
#print axioms FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_c
#print axioms FunctionalInequalities.Probability.Posterior.fderiv_posteriorExpectation_c_apply
#print axioms FunctionalInequalities.Probability.Posterior.bilinearIteratedFDerivTwo_posteriorExpectation_c_mean
#print axioms FunctionalInequalities.Probability.Posterior.sum_bilinearIteratedFDerivTwo_posteriorExpectation_c
#print axioms FunctionalInequalities.Probability.Posterior.posteriorExpectation_hasDerivAt_Q
#print axioms FunctionalInequalities.Probability.Posterior.posteriorExpectation_generator_cancellation
#print axioms ActualGeneratorBoundary.actual_zero_dim_generator
#print axioms ActualGeneratorClients.actual_inverse
#print axioms ActualGeneratorClients.actual_three_terms
#print axioms IndependentPosteriorGenerator.trace_independent
#print axioms IndependentPosteriorGenerator.negative_rate
#print axioms FunctionalInequalities.Probability.Posterior.quadraticExponent_concave
#print axioms FunctionalInequalities.KLS.LogConcave.map_affineIsometry
#print axioms FunctionalInequalities.KLS.LogConcave.logConcave_of_concave_tilt
#print axioms FunctionalInequalities.KLS.compactPosterior_logConcave
#print axioms ActualPosteriorLogConcavity.uniform_nonzero_posterior
#print axioms ActualPosteriorLogConcavity.uniform_linear_tilt
#print axioms ActualPosteriorLogConcavity.rank0_posterior
#print axioms ActualPosteriorSingularLogConcavity.singular_nonzero_posterior

namespace ActualJointPosteriorClients

/-- Noncentered compact two-point prior (not isotropic, not asserted log-concave). -/
def μ : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 2, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩

private theorem integral_μ (g : ℝ → ℝ) :
    (∫ x, g x ∂(μ : Measure ℝ)) = (1 / 2 : ℝ) * g 0 + (1 / 2 : ℝ) * g 2 := by
  have h0 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h2 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, g x ∂((1 / 2 : ENNReal) • Measure.dirac 0 +
    (1 / 2 : ENNReal) • Measure.dirac 2)) = _
  rw [integral_add_measure h0 h2, integral_smul_measure, integral_smul_measure]
  norm_num

private theorem support_subset : (μ : Measure ℝ).support ⊆ ({(0 : ℝ), 2} : Set ℝ) := by
  apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
  rw [mem_ae_iff]
  change ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (2 : ℝ)) ({(0 : ℝ), 2} : Set ℝ)ᶜ = 0
  simp

theorem compact_μ : IsCompact (μ : Measure ℝ).support :=
  (Set.toFinite ({(0 : ℝ), 2} : Set ℝ)).isCompact.of_isClosed_subset
    (μ : Measure ℝ).isClosed_support support_subset

/-- Values `0`, `2` on the atoms, cubic elsewhere: discontinuous at `2` and unbounded off the support. -/
def wild (x : ℝ) : ℝ := if x = 0 then 0 else if x = 2 then 2 else x ^ 3
private theorem measurable_wild : Measurable wild := by
  unfold wild
  apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
  exact Measurable.ite (measurableSet_singleton (2 : ℝ)) measurable_const (measurable_id.pow_const 3)
private theorem wild_bound : ∀ x ∈ (μ : Measure ℝ).support, ‖wild x‖ ≤ (2 : ℝ) := by
  intro x hx
  rcases support_subset hx with h | h
  · subst x
    norm_num [wild]
  · simp only [Set.mem_singleton_iff] at h
    subst x
    norm_num [wild]

/-- Joint smoothness for a measurable statistic with wild off-support behaviour. -/
theorem actual_wild_joint :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ →L[ℝ] ℝ) => posteriorExpectation μ p.1 p.2 wild) :=
  contDiff_posteriorExpectation_joint μ compact_μ measurable_wild wild_bound

/-- A mixed `c`/`Q` parameter curve. -/
theorem actual_mixed_curve_smooth :
    ContDiff ℝ ∞ (fun t : ℝ => posteriorExpectation μ (2 * t)
      (t • ContinuousLinearMap.id ℝ ℝ) wild) := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ =>
      (((2 * t), t • ContinuousLinearMap.id ℝ ℝ) : ℝ × (ℝ →L[ℝ] ℝ))) := by fun_prop
  have h := actual_wild_joint.comp hc
  have he : (fun p : ℝ × (ℝ →L[ℝ] ℝ) => posteriorExpectation μ p.1 p.2 wild) ∘
      (fun t : ℝ => (((2 * t), t • ContinuousLinearMap.id ℝ ℝ) : ℝ × (ℝ →L[ℝ] ℝ))) =
      (fun t : ℝ => posteriorExpectation μ (2 * t) (t • ContinuousLinearMap.id ℝ ℝ) wild) := by
    funext t
    rfl
  rw [he] at h
  exact h

private theorem zero_exponent : quadraticExponent (0 : ℝ) (0 : ℝ →L[ℝ] ℝ) = 0 := by
  funext x
  simp [quadraticExponent]

private theorem wild_memLp : MemLp wild 2 (μ : Measure ℝ) := by
  have h := memLp_two_tilted_of_compact μ compact_μ (φ := (0 : ℝ → ℝ)) continuous_const
    measurable_wild wild_bound
  simpa only [tilted_zero] using h

/-- The combined score `2x − ½x²` has covariance `1` with the statistic: dropping the `Q` response or
changing the half coefficient changes this value. -/
theorem actual_mixed_derivative : HasDerivAt (fun t : ℝ => posteriorExpectation μ (2 * t)
    (t • ContinuousLinearMap.id ℝ ℝ) wild) 1 0 := by
  let score : ℝ → ℝ := quadraticExponent 2 (ContinuousLinearMap.id ℝ ℝ)
  have hs : Continuous score := by unfold score quadraticExponent; fun_prop
  have hs2 := memLp_two_tilted_quadraticExponent_of_compact μ compact_μ 0 0 hs
  rw [zero_exponent, tilted_zero] at hs2
  have hcov : covariance wild score (μ : Measure ℝ) = 1 := by
    rw [covariance_eq_sub wild_memLp hs2]
    simp only [integral_μ]
    norm_num [wild, score, quadraticExponent, Real.inner_apply]
  have hd := expectation_hasDerivAt_quadraticExponent_of_compact μ compact_μ
    (0 : ℝ) 2 0 (ContinuousLinearMap.id ℝ ℝ) measurable_wild (by norm_num : (0 : ℝ) ≤ 2) wild_bound
  rw [zero_exponent, tilted_zero, hcov] at hd
  simpa only [posteriorExpectation, zero_add, smul_eq_mul, mul_comm] using hd

/-- Signed `Q` and nonzero mean: local smoothness of mean and covariance. -/
theorem actual_signed_mean_covariance :
    ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ →L[ℝ] ℝ) => posteriorMean μ p.1 p.2)
      (1, -ContinuousLinearMap.id ℝ ℝ) ∧
    ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ →L[ℝ] ℝ) =>
      Covariance.operator (compactPosterior μ compact_μ p.1 p.2 : Measure ℝ))
      (1, -ContinuousLinearMap.id ℝ ℝ) :=
  ⟨(contDiff_posteriorMean_joint μ compact_μ).contDiffAt,
    (contDiff_posteriorCovariance_joint μ compact_μ).contDiffAt⟩

abbrev E0 := EuclideanSpace ℝ (Fin 0)
def μ0 : ProbabilityMeasure E0 := ⟨Measure.dirac 0, inferInstance⟩
private theorem compact_μ0 : IsCompact (μ0 : Measure E0).support :=
  isCompact_univ.of_isClosed_subset (μ0 : Measure E0).isClosed_support (Set.subset_univ _)
private theorem μ0_isotropic : KLS.Isotropic μ0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := compactPosterior_memLp_id_two μ0 compact_μ0 0 0
    rw [compactPosterior_zero] at h
    exact h
  · simp [μ0]
  · apply ContinuousLinearMap.ext
    intro v
    exact Subsingleton.elim _ _

/-- Rank zero: expectation, mean, covariance, inverse and drift, with no positive-dimension premise. -/
theorem actual_rank0_joint :
    ContDiff ℝ ∞ (fun p : E0 × (E0 →L[ℝ] E0) =>
      posteriorExpectation μ0 p.1 p.2 (fun _ => (1 : ℝ))) ∧
    ContDiff ℝ ∞ (fun p : E0 × (E0 →L[ℝ] E0) => posteriorMean μ0 p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : E0 × (E0 →L[ℝ] E0) =>
      Covariance.operator (compactPosterior μ0 compact_μ0 p.1 p.2 : Measure E0)) ∧
    ContDiff ℝ ∞ (fun p : E0 × (E0 →L[ℝ] E0) => Ring.inverse (Covariance.operator
      (compactPosterior μ0 compact_μ0 p.1 p.2 : Measure E0))) ∧
    ContDiff ℝ ∞ (fun p : E0 × (E0 →L[ℝ] E0) => Ring.inverse (Covariance.operator
      (compactPosterior μ0 compact_μ0 p.1 p.2 : Measure E0)) (posteriorMean μ0 p.1 p.2)) := by
  exact ⟨contDiff_posteriorExpectation_joint μ0 compact_μ0 measurable_const (C := 1)
      (by intro x hx; simp),
    contDiff_posteriorMean_joint μ0 compact_μ0, contDiff_posteriorCovariance_joint μ0 compact_μ0,
    KLS.Isotropic.contDiff_ringInverse_covariance_joint μ0 compact_μ0 μ0_isotropic,
    KLS.Isotropic.contDiff_covarianceDrift_joint μ0 compact_μ0 μ0_isotropic⟩

end ActualJointPosteriorClients

namespace ActualJointInverseClients

/-- Symmetric two-atom prior at `±1`: compact and isotropic. -/
def μ : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac (-1) + (1 / 2 : ENNReal) • Measure.dirac 1, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩

private theorem integral_μ (g : ℝ → ℝ) :
    (∫ x, g x ∂(μ : Measure ℝ)) = (1 / 2 : ℝ) * g (-1) + (1 / 2 : ℝ) * g 1 := by
  have h0 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h1 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, g x ∂((1 / 2 : ENNReal) • Measure.dirac (-1) +
    (1 / 2 : ENNReal) • Measure.dirac 1)) = _
  rw [integral_add_measure h0 h1, integral_smul_measure, integral_smul_measure]
  norm_num

theorem compact_μ : IsCompact (μ : Measure ℝ).support := by
  have hsub : (μ : Measure ℝ).support ⊆ ({(-1 : ℝ), 1} : Set ℝ) := by
    apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
    rw [mem_ae_iff]
    change ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) ({(-1 : ℝ), 1} : Set ℝ)ᶜ = 0
    simp
  exact (Set.toFinite ({(-1 : ℝ), 1} : Set ℝ)).isCompact.of_isClosed_subset
    (μ : Measure ℝ).isClosed_support hsub

theorem isotropic_μ : KLS.Isotropic μ := by
  have h2 := compactPosterior_memLp_id_two μ compact_μ 0 0
  rw [compactPosterior_zero] at h2
  apply KLS.isotropic_of_moments μ h2
  · rw [integral_μ]
    norm_num
  · intro u v
    rw [integral_μ]
    simp only [Real.inner_apply]
    ring

/-- Signed `Q`: the rate and the drift are smooth at `(1, −Id)`; isotropy and compactness are derived. -/
theorem actual_signed_inverse_drift :
    ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ →L[ℝ] ℝ) => Ring.inverse (Covariance.operator
      (compactPosterior μ compact_μ p.1 p.2 : Measure ℝ))) (1, -ContinuousLinearMap.id ℝ ℝ) ∧
    ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ →L[ℝ] ℝ) => Ring.inverse (Covariance.operator
      (compactPosterior μ compact_μ p.1 p.2 : Measure ℝ)) (posteriorMean μ p.1 p.2))
      (1, -ContinuousLinearMap.id ℝ ℝ) :=
  ⟨(KLS.Isotropic.contDiff_ringInverse_covariance_joint μ compact_μ isotropic_μ).contDiffAt,
    (KLS.Isotropic.contDiff_covarianceDrift_joint μ compact_μ isotropic_μ).contDiffAt⟩

/-- The rate at the initial pair is the identity. -/
theorem actual_initial_inverse :
    Ring.inverse (Covariance.operator (compactPosterior μ compact_μ 0 0 : Measure ℝ)) =
      ContinuousLinearMap.id ℝ ℝ := by
  rw [compactPosterior_zero, isotropic_μ.covariance_identity]
  exact Ring.inverse_one (ℝ →L[ℝ] ℝ)

/-- The principal diffusion coefficient of (67) is locally Lipschitz for this source prior, including at
negative `Q`; no root or regularity premise. -/
theorem actual_source_locallyLipschitz :
    LocallyLipschitz (fun p : ℝ × (ℝ →L[ℝ] ℝ) => inverseSqrt (Covariance.operator
      (compactPosterior μ compact_μ p.1 p.2 : Measure ℝ))) :=
  KLS.Isotropic.locallyLipschitz_inverseSqrt_covariance_joint μ compact_μ isotropic_μ

/-- The whole coefficient triple of (67) for this source prior. -/
theorem actual_source_coefficients67 :
    LocallyLipschitz (fun p : ℝ × (ℝ →L[ℝ] ℝ) =>
      (inverseSqrt (Covariance.operator (compactPosterior μ compact_μ p.1 p.2 : Measure ℝ)),
       (Ring.inverse (Covariance.operator (compactPosterior μ compact_μ p.1 p.2 : Measure ℝ))
         (posteriorMean μ p.1 p.2),
        Ring.inverse (Covariance.operator (compactPosterior μ compact_μ p.1 p.2 : Measure ℝ))))) :=
  KLS.Isotropic.locallyLipschitz_coefficients67 μ compact_μ isotropic_μ

/-- The initial principal coefficient is the nonzero identity branch. -/
theorem actual_initial_principal :
    inverseSqrt (Covariance.operator (compactPosterior μ compact_μ 0 0 : Measure ℝ)) =
      ContinuousLinearMap.id ℝ ℝ := by
  rw [compactPosterior_zero, isotropic_μ.covariance_identity]
  apply inverseSqrt_unique
  · exact isUnit_one
  · exact ContinuousLinearMap.isPositive_one
  · change (1 : ℝ →L[ℝ] ℝ) * 1 = Ring.inverse (1 : ℝ →L[ℝ] ℝ)
    simp only [Ring.inverse_one, mul_one]

abbrev E0 := EuclideanSpace ℝ (Fin 0)
def μ0 : ProbabilityMeasure E0 := ⟨Measure.dirac 0, inferInstance⟩
private theorem compact_μ0 : IsCompact (μ0 : Measure E0).support :=
  isCompact_univ.of_isClosed_subset (μ0 : Measure E0).isClosed_support (Set.subset_univ _)
private theorem μ0_isotropic : KLS.Isotropic μ0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := compactPosterior_memLp_id_two μ0 compact_μ0 0 0
    rw [compactPosterior_zero] at h
    exact h
  · simp [μ0]
  · apply ContinuousLinearMap.ext
    intro v
    exact Subsingleton.elim _ _

/-- Rank zero: the principal coefficient is locally Lipschitz and identically `0`. -/
theorem actual_rank0_source :
    LocallyLipschitz (fun p : E0 × (E0 →L[ℝ] E0) => inverseSqrt (Covariance.operator
      (compactPosterior μ0 compact_μ0 p.1 p.2 : Measure E0))) ∧
    (∀ p : E0 × (E0 →L[ℝ] E0), inverseSqrt (Covariance.operator
      (compactPosterior μ0 compact_μ0 p.1 p.2 : Measure E0)) = 0) :=
  ⟨KLS.Isotropic.locallyLipschitz_inverseSqrt_covariance_joint μ0 compact_μ0 μ0_isotropic,
    fun _ => Subsingleton.elim _ _⟩

end ActualJointInverseClients

#print axioms FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint
#print axioms FunctionalInequalities.Probability.Posterior.contDiff_posteriorExpectation_joint_of_continuous
#print axioms FunctionalInequalities.Probability.Posterior.contDiff_posteriorMean_joint
#print axioms FunctionalInequalities.Probability.Posterior.contDiff_covariance_pair_joint
#print axioms FunctionalInequalities.Probability.Posterior.contDiff_posteriorCovariance_joint
#print axioms FunctionalInequalities.KLS.Isotropic.contDiff_ringInverse_covariance_joint
#print axioms FunctionalInequalities.KLS.Isotropic.contDiff_covarianceDrift_joint
#print axioms FunctionalInequalities.KLS.Isotropic.locallyLipschitz_inverseSqrt_covariance_joint
#print axioms FunctionalInequalities.KLS.Isotropic.locallyLipschitz_coefficients67
#print axioms ActualJointPosteriorClients.actual_wild_joint
#print axioms ActualJointPosteriorClients.actual_mixed_curve_smooth
#print axioms ActualJointPosteriorClients.actual_mixed_derivative
#print axioms ActualJointPosteriorClients.actual_signed_mean_covariance
#print axioms ActualJointPosteriorClients.actual_rank0_joint
#print axioms ActualJointInverseClients.actual_signed_inverse_drift
#print axioms ActualJointInverseClients.actual_initial_inverse
#print axioms ActualJointInverseClients.actual_source_locallyLipschitz
#print axioms ActualJointInverseClients.actual_source_coefficients67
#print axioms ActualJointInverseClients.actual_initial_principal
#print axioms ActualJointInverseClients.actual_rank0_source

/-! Canonical standardisation (`KLS/BKL/PosteriorDomain.lean` section `CanonicalStandardisation`, Luna unit TW1 with
recorded Claude closing repairs, independently accepted 2026-10-08, receipt `TW1-Independent-20261008/VERIFICATION.json`
6e339248…): the independent Codex reviewer's consumers — the full original contract, the symmetric two-atom prior at `±1`
(compactness and isotropy derived) at an arbitrary tilt and `Q = −Id` with the image law's `L²`, zero mean and identity
covariance extracted, and the rank-zero Dirac law. -/
namespace IndependentCanonicalStandardisation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem original_contract (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    ∃ W : E ≃L[ℝ] E,
      (W : E →L[ℝ] E) = inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure E)) ∧
      KLS.Isotropic (Probability.mapContinuousLinearEquiv
        (Probability.translateLaw (compactPosterior μ hc c Q) (-posteriorMean μ c Q)) W) := by
  exact KLS.Isotropic.exists_inverseSqrt_equiv_isotropic_standardized μ hc hiso c Q

/-- Symmetric two-atom prior at `±1`: compact and isotropic. -/
def μ : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac (-1) + (1 / 2 : ENNReal) • Measure.dirac 1, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩

private theorem integral_μ (g : ℝ → ℝ) :
    (∫ x, g x ∂(μ : Measure ℝ)) = (1 / 2 : ℝ) * g (-1) + (1 / 2 : ℝ) * g 1 := by
  have h0 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h1 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, g x ∂((1 / 2 : ENNReal) • Measure.dirac (-1) +
    (1 / 2 : ENNReal) • Measure.dirac 1)) = _
  rw [integral_add_measure h0 h1, integral_smul_measure, integral_smul_measure]
  norm_num

theorem compact_μ : IsCompact (μ : Measure ℝ).support := by
  have hsub : (μ : Measure ℝ).support ⊆ ({(-1 : ℝ), 1} : Set ℝ) := by
    apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
    rw [mem_ae_iff]
    change ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) ({(-1 : ℝ), 1} : Set ℝ)ᶜ = 0
    simp
  exact (Set.toFinite ({(-1 : ℝ), 1} : Set ℝ)).isCompact.of_isClosed_subset
    (μ : Measure ℝ).isClosed_support hsub

theorem isotropic_μ : KLS.Isotropic μ := by
  have h2 := compactPosterior_memLp_id_two μ compact_μ 0 0
  rw [compactPosterior_zero] at h2
  apply KLS.isotropic_of_moments μ h2
  · rw [integral_μ]
    norm_num
  · intro u v
    rw [integral_μ]
    simp only [Real.inner_apply]
    ring

abbrev E0 := EuclideanSpace ℝ (Fin 0)
def μ0 : ProbabilityMeasure E0 := ⟨Measure.dirac 0, inferInstance⟩
private theorem compact_μ0 : IsCompact (μ0 : Measure E0).support :=
  isCompact_univ.of_isClosed_subset (μ0 : Measure E0).isClosed_support (Set.subset_univ _)
private theorem μ0_isotropic : KLS.Isotropic μ0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := compactPosterior_memLp_id_two μ0 compact_μ0 0 0
    rw [compactPosterior_zero] at h
    exact h
  · simp [μ0]
  · apply ContinuousLinearMap.ext
    intro v
    exact Subsingleton.elim _ _


/-- Actual compact isotropic prior at a nonzero tilt and negative Q; three image fields are conclusions. -/
theorem actual_signed (c : ℝ) :
    ∃ W : ℝ ≃L[ℝ] ℝ,
      (W : ℝ →L[ℝ] ℝ) = inverseSqrt
        (Covariance.operator (compactPosterior μ compact_μ c (-ContinuousLinearMap.id ℝ ℝ) : Measure ℝ)) ∧
      MemLp id 2 (Probability.mapContinuousLinearEquiv
        (Probability.translateLaw (compactPosterior μ compact_μ c (-ContinuousLinearMap.id ℝ ℝ))
          (-posteriorMean μ c (-ContinuousLinearMap.id ℝ ℝ))) W : Measure ℝ) ∧
      (∫ x, x ∂(Probability.mapContinuousLinearEquiv
        (Probability.translateLaw (compactPosterior μ compact_μ c (-ContinuousLinearMap.id ℝ ℝ))
          (-posteriorMean μ c (-ContinuousLinearMap.id ℝ ℝ))) W : Measure ℝ)) = 0 ∧
      Covariance.operator (Probability.mapContinuousLinearEquiv
        (Probability.translateLaw (compactPosterior μ compact_μ c (-ContinuousLinearMap.id ℝ ℝ))
          (-posteriorMean μ c (-ContinuousLinearMap.id ℝ ℝ))) W : Measure ℝ) =
        ContinuousLinearMap.id ℝ ℝ := by
  obtain ⟨W, hW, hη⟩ := KLS.Isotropic.exists_inverseSqrt_equiv_isotropic_standardized
    μ compact_μ isotropic_μ c (-ContinuousLinearMap.id ℝ ℝ)
  exact ⟨W, hW, hη.memLp_two, hη.mean_zero, hη.covariance_identity⟩

/-- The same genuine endpoint applies at rank zero without a dimension restriction. -/
theorem actual_empty :
    ∃ W : E0 ≃L[ℝ] E0,
      (W : E0 →L[ℝ] E0) = inverseSqrt
        (Covariance.operator (compactPosterior μ0 compact_μ0 0 0 : Measure E0)) ∧
      KLS.Isotropic (Probability.mapContinuousLinearEquiv
        (Probability.translateLaw (compactPosterior μ0 compact_μ0 0 0) (-posteriorMean μ0 0 0)) W) :=
  KLS.Isotropic.exists_inverseSqrt_equiv_isotropic_standardized μ0 compact_μ0 μ0_isotropic 0 0

#print axioms original_contract
#print axioms compact_μ
#print axioms isotropic_μ
#print axioms actual_signed
#print axioms actual_empty
#print axioms FunctionalInequalities.KLS.Isotropic.exists_inverseSqrt_equiv_isotropic_standardized

end IndependentCanonicalStandardisation

/-! Covariance radius bound (`KLS/BKL/PosteriorDomain.lean` section `CovarianceRadius`,
`KLS.opNorm_covariance_compactPosterior_le_sq_radius`, Luna unit TU1b round 8 with a recorded linter-only Claude closing
repair, independently accepted 2026-10-08, receipt `TU1b-Independent-20261008/VERIFICATION.json` 41571c1b…): the
independent Codex reviewer's consumers — the full original contract, a Dirac prior at radius `0` (posterior covariance
`0` at every parameter, including a nonzero `c` and an explicitly non-self-adjoint `Q` in `ℝ²`), the sharp `±1` prior
(initial norm `1`, bound `1` at every signed parameter), and rank zero. -/
namespace IndependentCovarianceRadius

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem original_contract (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure E).support ⊆ Metric.closedBall (0 : E) r)
    (c : E) (Q : E →L[ℝ] E) :
    ‖Covariance.operator (compactPosterior μ hc c Q : Measure E)‖ ≤ r ^ 2 := by
  exact KLS.opNorm_covariance_compactPosterior_le_sq_radius μ hc hr hsupp c Q

def deltaZero : ProbabilityMeasure E := ⟨Measure.dirac 0, inferInstance⟩

private theorem delta_support :
    (deltaZero (E := E) : Measure E).support ⊆ ({0} : Set E) := by
  apply Measure.support_subset_of_isClosed isClosed_singleton
  rw [mem_ae_iff]
  simp [deltaZero]

theorem compact_delta : IsCompact (deltaZero (E := E) : Measure E).support := by
  exact isCompact_singleton.of_isClosed_subset (deltaZero (E := E) : Measure E).isClosed_support delta_support

theorem radius_zero_delta :
    (deltaZero (E := E) : Measure E).support ⊆ Metric.closedBall (0 : E) 0 := by
  intro x hx
  have hx0 : x = 0 := Set.mem_singleton_iff.mp (delta_support hx)
  simp [hx0]

/-- A genuine Dirac prior has zero posterior covariance for every finite parameter. -/
theorem delta_actual_norm_zero (c : E) (Q : E →L[ℝ] E) :
    ‖Covariance.operator (compactPosterior (deltaZero (E := E)) (compact_delta (E := E)) c Q : Measure E)‖ = 0 := by
  apply le_antisymm
  · exact le_trans (KLS.opNorm_covariance_compactPosterior_le_sq_radius
      (deltaZero (E := E)) compact_delta (le_refl (0 : ℝ)) radius_zero_delta c Q) (by norm_num)
  · exact norm_nonneg _

theorem delta_actual_covariance_zero (c : E) (Q : E →L[ℝ] E) :
    Covariance.operator (compactPosterior (deltaZero (E := E)) (compact_delta (E := E)) c Q : Measure E) = 0 := by
  exact norm_eq_zero.mp (delta_actual_norm_zero c Q)
end Generic

/-- The normalized symmetric two-atom prior at -1 and 1. -/
def μ : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac (-1) + (1 / 2 : ENNReal) • Measure.dirac 1, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩

private theorem integral_μ (g : ℝ → ℝ) :
    (∫ x, g x ∂(μ : Measure ℝ)) = (1 / 2 : ℝ) * g (-1) + (1 / 2 : ℝ) * g 1 := by
  have h0 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h1 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, g x ∂((1 / 2 : ENNReal) • Measure.dirac (-1) +
    (1 / 2 : ENNReal) • Measure.dirac 1)) = _
  rw [integral_add_measure h0 h1, integral_smul_measure, integral_smul_measure]
  norm_num

private theorem support_μ_atoms : (μ : Measure ℝ).support ⊆ ({(-1 : ℝ), 1} : Set ℝ) := by
  apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
  rw [mem_ae_iff]
  change ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) ({(-1 : ℝ), 1} : Set ℝ)ᶜ = 0
  simp

theorem compact_μ : IsCompact (μ : Measure ℝ).support := by
  exact (Set.toFinite ({(-1 : ℝ), 1} : Set ℝ)).isCompact.of_isClosed_subset
    (μ : Measure ℝ).isClosed_support support_μ_atoms

theorem radius_one_μ : (μ : Measure ℝ).support ⊆ Metric.closedBall (0 : ℝ) 1 := by
  intro x hx
  have hx' := support_μ_atoms hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
  rcases hx' with rfl | rfl <;> norm_num [mem_closedBall_zero_iff]

theorem isotropic_μ : KLS.Isotropic μ := by
  have h2 := compactPosterior_memLp_id_two μ compact_μ 0 0
  rw [compactPosterior_zero] at h2
  apply KLS.isotropic_of_moments μ h2
  · rw [integral_μ]; norm_num
  · intro u v
    rw [integral_μ]
    simp only [Real.inner_apply]
    ring

/-- The initial covariance identity is derived from the actual atomic moments. -/
theorem initial_covariance :
    Covariance.operator (compactPosterior μ compact_μ 0 0 : Measure ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by
  rw [compactPosterior_zero, isotropic_μ.covariance_identity]

theorem initial_norm_sharp :
    ‖Covariance.operator (compactPosterior μ compact_μ 0 0 : Measure ℝ)‖ = 1 := by
  rw [initial_covariance]
  simp

theorem actual_all_signed (c : ℝ) (Q : ℝ →L[ℝ] ℝ) :
    ‖Covariance.operator (compactPosterior μ compact_μ c Q : Measure ℝ)‖ ≤ 1 := by
  simpa using KLS.opNorm_covariance_compactPosterior_le_sq_radius
    μ compact_μ (by norm_num : (0 : ℝ) ≤ 1) radius_one_μ c Q

theorem actual_nonzero_c_negative_Q :
    ‖Covariance.operator (compactPosterior μ compact_μ (1 : ℝ)
      (-ContinuousLinearMap.id ℝ ℝ) : Measure ℝ)‖ ≤ 1 := by
  exact actual_all_signed 1 (-ContinuousLinearMap.id ℝ ℝ)

abbrev E2 := EuclideanSpace ℝ (Fin 2)
def e0 : E2 := WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)]
def e1 : E2 := WithLp.toLp 2 ![(0 : ℝ), (1 : ℝ)]
def nonsymmetricQ : E2 →L[ℝ] E2 := (InnerProductSpace.toDual ℝ E2 e1).smulRight e0

theorem nonsymmetric_witness :
    ⟪nonsymmetricQ e1, e0⟫ = 1 ∧ ⟪e1, nonsymmetricQ e0⟫ = 0 := by
  simp only [nonsymmetricQ, ContinuousLinearMap.smulRight_apply, InnerProductSpace.toDual_apply_apply,
    PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  norm_num [e0, e1]

theorem actually_not_selfAdjoint : ¬ IsSelfAdjoint nonsymmetricQ := by
  intro h
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp h) e1 e0
  have hw := nonsymmetric_witness
  change ⟪nonsymmetricQ e1, e0⟫ = ⟪e1, nonsymmetricQ e0⟫ at hs
  rw [hw.1, hw.2] at hs
  norm_num at hs

/-- This posterior is defined at an explicitly nonsymmetric parameter and nonzero c. -/
theorem actual_nonsymmetric_covariance_zero :
    Covariance.operator (compactPosterior (deltaZero (E := E2) : ProbabilityMeasure E2) compact_delta
      e1 nonsymmetricQ : Measure E2) = 0 := by
  exact delta_actual_covariance_zero e1 nonsymmetricQ

theorem actual_c_nonzero : (e1 : E2) ≠ 0 := by
  intro h
  have h' := congrArg (fun x : E2 => x (1 : Fin 2)) h
  norm_num [e1] at h'

abbrev E0 := EuclideanSpace ℝ (Fin 0)

/-- Every actual probability law in rank zero satisfies the original bound, with arbitrary c,Q. -/
theorem rank_zero_actual (ν : ProbabilityMeasure E0) (c : E0) (Q : E0 →L[ℝ] E0) :
    ∃ hc : IsCompact (ν : Measure E0).support,
      ‖Covariance.operator (compactPosterior ν hc c Q : Measure E0)‖ = 0 := by
  have hc : IsCompact (ν : Measure E0).support :=
    isCompact_univ.of_isClosed_subset (ν : Measure E0).isClosed_support (Set.subset_univ _)
  have hsupp : (ν : Measure E0).support ⊆ Metric.closedBall (0 : E0) 0 := by
    intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  refine ⟨hc, le_antisymm ?_ (norm_nonneg _)⟩
  exact le_trans (KLS.opNorm_covariance_compactPosterior_le_sq_radius
    ν hc (le_refl (0 : ℝ)) hsupp c Q) (by norm_num)

#print axioms original_contract
#print axioms delta_actual_covariance_zero
#print axioms initial_norm_sharp
#print axioms actual_nonzero_c_negative_Q
#print axioms actually_not_selfAdjoint
#print axioms actual_nonsymmetric_covariance_zero
#print axioms rank_zero_actual
#print axioms FunctionalInequalities.KLS.opNorm_covariance_compactPosterior_le_sq_radius

end IndependentCovarianceRadius

/-! Noise bound of (68) (`KLS/BKL/PosteriorDomain.lean` section `NoiseBound`,
`Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_variance` / `_le_sq`, Luna units NB4a/NB4b round 8
in Claude's accepted assembly, independently accepted 2026-10-08, receipt `NB4-Assembly-Independent-20261008/VERIFICATION.json`
f5b20cb8…): the independent Codex reviewer's consumers — the `±1` prior of `ActualJointInverseClients` with the nonconstant
statistic `id` at `c = 1`, `Q = −Id` (variance and uniform bounds), the zero statistic, saturation `‖noise‖² = 1 = Var` at
the initial pair, rank zero, and a four-atom isotropic prior in `ℝ²` with an explicitly signed, non-self-adjoint `Q`. -/
namespace IndependentNoiseBound

abbrev μ := ActualJointInverseClients.μ
abbrev hc := ActualJointInverseClients.compact_μ
abbrev hiso := ActualJointInverseClients.isotropic_μ

theorem prior_support : (μ : Measure ℝ).support ⊆ ({(-1 : ℝ), 1} : Set ℝ) := by
  apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
  rw [mem_ae_iff]
  change ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) ({(-1 : ℝ), 1} : Set ℝ)ᶜ = 0
  simp

theorem id_bound : ∀ x ∈ (μ : Measure ℝ).support, ‖id x‖ ≤ (1 : ℝ) := by
  intro x hx
  rcases prior_support hx with hx | hx
  · subst x
    norm_num
  · simp only [Set.mem_singleton_iff] at hx
    subst x
    norm_num

def noise (f : ℝ → ℝ) (c : ℝ) (Q : ℝ →L[ℝ] ℝ) : ℝ →L[ℝ] ℝ :=
  (fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp
    (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure ℝ)))

/-- Actual nonconstant statistic at c=1, signed Q=-Id; prior is genuinely compact and isotropic. -/
theorem actual_signed_noise :
    ‖noise id 1 (-ContinuousLinearMap.id ℝ ℝ)‖ ^ 2 ≤
      variance id (compactPosterior μ hc 1 (-ContinuousLinearMap.id ℝ ℝ) : Measure ℝ) ∧
      ‖noise id 1 (-ContinuousLinearMap.id ℝ ℝ)‖ ^ 2 ≤ 1 := by
  constructor
  · exact KLS.Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_variance
      μ hc hiso measurable_id (by norm_num : (0 : ℝ) ≤ 1) id_bound 1 (-ContinuousLinearMap.id ℝ ℝ)
  · simpa only [noise, one_pow] using
      KLS.Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_sq
        μ hc hiso measurable_id (by norm_num : (0 : ℝ) ≤ 1) id_bound 1 (-ContinuousLinearMap.id ℝ ℝ)

theorem actual_zero_statistic (c : ℝ) (Q : ℝ →L[ℝ] ℝ) :
    ‖noise (fun _ => (0 : ℝ)) c Q‖ ^ 2 = 0 := by
  have hh : ‖noise (fun _ => (0 : ℝ)) c Q‖ ^ 2 ≤ (0 : ℝ) ^ 2 :=
    KLS.Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_sq
      μ hc hiso measurable_const (by norm_num) (by intro x hx; simp) c Q
  nlinarith [sq_nonneg ‖noise (fun _ => (0 : ℝ)) c Q‖]

theorem prior_variance : variance id (μ : Measure ℝ) = 1 := by
  have he := congrArg (fun T : ℝ →L[ℝ] ℝ => ⟪T (1 : ℝ), (1 : ℝ)⟫) hiso.covariance_identity
  rw [Covariance.operator_inner, covarianceBilin_real] at he
  norm_num at he
  exact he

theorem initial_derivative : fderiv ℝ (fun y => posteriorExpectation μ y 0 id) 0 =
    ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro h
  have hd := fderiv_posteriorExpectation_c_apply μ hc measurable_id
    (by norm_num : (0 : ℝ) ≤ 1) id_bound (0 : ℝ) (0 : ℝ →L[ℝ] ℝ) h
  have he : quadraticExponent (0 : ℝ) (0 : ℝ →L[ℝ] ℝ) = 0 := by
    funext x
    simp [quadraticExponent]
  rw [he, tilted_zero] at hd
  have hv : covariance id id (μ : Measure ℝ) = variance id (μ : Measure ℝ) :=
    covariance_self hiso.memLp_two.aestronglyMeasurable.aemeasurable
  have hl : (fun x : ℝ => ⟪h, x⟫) = fun x => h * id x := by
    funext x
    simp [mul_comm]
  rw [hl, covariance_const_mul_right, hv, prior_variance] at hd
  simpa using hd

/-- The actual initial coefficient saturates the constant-one variance estimate. -/
theorem actual_saturation : ‖noise id 0 0‖ ^ 2 = 1 ∧
    ‖noise id 0 0‖ ^ 2 = variance id (compactPosterior μ hc 0 0 : Measure ℝ) := by
  have hn : noise id 0 0 = ContinuousLinearMap.id ℝ ℝ := by
    unfold noise
    rw [initial_derivative, ActualJointInverseClients.actual_initial_principal]
    simp
  constructor
  · rw [hn, ContinuousLinearMap.norm_id]
    norm_num
  · rw [hn, ContinuousLinearMap.norm_id, compactPosterior_zero, prior_variance]
    norm_num

abbrev E0 := ActualJointInverseClients.E0
abbrev μ0 := ActualJointInverseClients.μ0

theorem compact0 : IsCompact (μ0 : Measure E0).support :=
  isCompact_univ.of_isClosed_subset (μ0 : Measure E0).isClosed_support (Set.subset_univ _)

theorem isotropic0 : KLS.Isotropic μ0 := by
  refine ⟨?_, ?_, ?_⟩
  · have hh := compactPosterior_memLp_id_two μ0 compact0 0 0
    rw [compactPosterior_zero] at hh
    exact hh
  · simp [ActualJointInverseClients.μ0]
  · apply ContinuousLinearMap.ext
    intro v
    exact Subsingleton.elim _ _

theorem actual_rank0_bounds (c : E0) (Q : E0 →L[ℝ] E0) :
    ‖(fderiv ℝ (fun y => posteriorExpectation μ0 y Q (fun _ => (5 : ℝ))) c).comp
        (inverseSqrt (Covariance.operator (compactPosterior μ0 compact0 c Q : Measure E0)))‖ ^ 2 ≤
      variance (fun _ : E0 => (5 : ℝ)) (compactPosterior μ0 compact0 c Q : Measure E0) ∧
    ‖(fderiv ℝ (fun y => posteriorExpectation μ0 y Q (fun _ => (5 : ℝ))) c).comp
        (inverseSqrt (Covariance.operator (compactPosterior μ0 compact0 c Q : Measure E0)))‖ ^ 2 ≤ 25 := by
  constructor
  · exact KLS.Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_variance
      μ0 compact0 isotropic0 measurable_const (by norm_num : (0 : ℝ) ≤ 5)
      (by intro x hx; norm_num) c Q
  · exact (KLS.Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_sq
      μ0 compact0 isotropic0 measurable_const (by norm_num : (0 : ℝ) ≤ 5)
      (by intro x hx; norm_num) c Q).trans (by norm_num : (5 : ℝ) ^ 2 ≤ 25)

theorem actual_rank0_zero (c : E0) (Q : E0 →L[ℝ] E0) :
    ‖(fderiv ℝ (fun y => posteriorExpectation μ0 y Q (fun _ => (5 : ℝ))) c).comp
        (inverseSqrt (Covariance.operator (compactPosterior μ0 compact0 c Q : Measure E0)))‖ ^ 2 = 0 := by
  have hs : inverseSqrt (Covariance.operator
      (compactPosterior μ0 compact0 c Q : Measure E0)) = 0 := Subsingleton.elim _ _
  rw [hs]
  simp

#print axioms prior_support
#print axioms id_bound
#print axioms noise
#print axioms actual_signed_noise
#print axioms actual_zero_statistic
#print axioms prior_variance
#print axioms initial_derivative
#print axioms actual_saturation
#print axioms compact0
#print axioms isotropic0
#print axioms actual_rank0_bounds
#print axioms actual_rank0_zero
end IndependentNoiseBound

namespace IndependentNoiseBoundNonsymmetric
abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a, b]
def μ : ProbabilityMeasure E :=
  ⟨ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 (-1)) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) (-1)), by
      constructor
      simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num⟩

theorem integral_μ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) :
    (∫ x, g x ∂(μ : Measure E)) =
      (1 / 4 : ℝ) • g (point 1 1) + (1 / 4 : ℝ) • g (point 1 (-1)) +
      (1 / 4 : ℝ) • g (point (-1) 1) + (1 / 4 : ℝ) • g (point (-1) (-1)) := by
  have hi (x : E) : Integrable g (ENNReal.ofReal (1 / 4) • Measure.dirac x) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, g x ∂(ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 (-1)) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) (-1)))) = _
  rw [integral_add_measure ((hi _).add_measure (hi _) |>.add_measure (hi _)) (hi _),
    integral_add_measure ((hi _).add_measure (hi _)) (hi _),
    integral_add_measure (hi _) (hi _)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)]

def K : Set E := {point 1 1, point 1 (-1), point (-1) 1, point (-1) (-1)}

theorem support_subset : (μ : Measure E).support ⊆ K := by
  apply Measure.support_subset_of_isClosed
    (isClosed_singleton.union (isClosed_singleton.union (isClosed_singleton.union isClosed_singleton)))
  rw [mem_ae_iff]
  change ((ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 (-1)) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) (-1))) Kᶜ) = 0
  simp [K]

theorem compact_μ : IsCompact (μ : Measure E).support := by
  have hK : K.Finite := by simp [K]
  exact hK.isCompact.of_isClosed_subset (μ : Measure E).isClosed_support support_subset

theorem inner_point (u : E) (a b : ℝ) : ⟪u, point a b⟫ = u 0 * a + u 1 * b := by
  simp [point, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem isotropic_μ : KLS.Isotropic μ := by
  have h2 := compactPosterior_memLp_id_two μ compact_μ 0 0
  rw [compactPosterior_zero] at h2
  apply KLS.isotropic_of_moments μ h2
  · rw [integral_μ]
    ext i
    fin_cases i <;> norm_num [point]
  · intro u v
    rw [integral_μ]
    simp only [smul_eq_mul, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
    norm_num [point]
    ring

def f (x : E) : ℝ := x 0

theorem f_measurable : Measurable f := by
  apply Continuous.measurable
  unfold f
  fun_prop

theorem f_bound : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ (1 : ℝ) := by
  intro x hx
  have hh := support_subset hx
  simp only [K, Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with hh | hh | hh | hh <;> subst x <;> norm_num [f, point]

def e0 : E := point 1 0
def e1 : E := point 0 1
def Q : E →L[ℝ] E := -(1 : E →L[ℝ] E) + (innerSL ℝ e1).smulRight e0

theorem Q_negative_direction : ⟪Q e0, e0⟫ = -1 := by
  have h01 : ⟪e1, e0⟫ = (0 : ℝ) := by
    rw [PiLp.inner_apply]
    norm_num [e0, e1, point, Fin.sum_univ_two]
  have h00 : ⟪e0, e0⟫ = (1 : ℝ) := by
    rw [PiLp.inner_apply]
    norm_num [e0, point, Fin.sum_univ_two]
  have he : Q e0 = -e0 := by simp [Q, h01]
  rw [he, inner_neg_left, h00]

theorem Q_not_selfAdjoint : ¬ IsSelfAdjoint Q := by
  intro hh
  have he := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hh) e1 e0
  norm_num [Q, e0, e1, point, PiLp.inner_apply, Fin.sum_univ_two] at he

/-- Actual four-atom compact isotropic prior; Q is simultaneously signed and nonsymmetric.
The coefficient is the literal principal inverse square root of the actual posterior covariance. -/
theorem actual_nonsymmetric_noise :
    ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) e0).comp
        (inverseSqrt (Covariance.operator (compactPosterior μ compact_μ e0 Q : Measure E)))‖ ^ 2 ≤
      variance f (compactPosterior μ compact_μ e0 Q : Measure E) ∧
    ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) e0).comp
        (inverseSqrt (Covariance.operator (compactPosterior μ compact_μ e0 Q : Measure E)))‖ ^ 2 ≤ 1 := by
  constructor
  · exact KLS.Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_variance
      μ compact_μ isotropic_μ f_measurable (by norm_num : (0 : ℝ) ≤ 1) f_bound e0 Q
  · simpa only [one_pow] using
      KLS.Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_sq
        μ compact_μ isotropic_μ f_measurable (by norm_num : (0 : ℝ) ≤ 1) f_bound e0 Q

#print axioms μ
#print axioms integral_μ
#print axioms support_subset
#print axioms compact_μ
#print axioms inner_point
#print axioms isotropic_μ
#print axioms f_measurable
#print axioms f_bound
#print axioms Q_negative_direction
#print axioms Q_not_selfAdjoint
#print axioms actual_nonsymmetric_noise
end IndependentNoiseBoundNonsymmetric

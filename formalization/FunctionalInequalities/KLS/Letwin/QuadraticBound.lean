import FunctionalInequalities.KLS.Letwin.CompactBound
import FunctionalInequalities.Probability.Conditioning

/-!
# Letwin's constant-eight bound without compact support

Letwin arXiv:2607.24164v1, Theorem 1.2: for every positive dimension, every isotropic
log-concave probability law and every real self-adjoint operator, the quadratic-form variance
is at most eight times the squared Hilbert–Schmidt norm. `letwinQuadraticBound` gives the
operator form; `matrix_variance_le_eight` gives the source normalization `8 tr(M²)` for every
symmetric matrix, including singular and indefinite matrices.

Condition on expanding closed balls, center each law, and whiten its covariance. The means
converge to zero and the covariance operators and their inverse square roots converge to the
identity. Dominated convergence gives all mixed moments of degree at most four for the
standardized laws. The accepted compact bound then passes to the limit. The growing-ball
step does not require a common compact support or an additional moment premise: log-concavity
supplies a positive exponential moment.

This proves the noncompact quadratic bound using the compact counterpart. It does not
construct the full smooth regular approximants of Lemma A.1 or establish Theorem 1.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave
open Suspension

private lemma memLp_four_of_exp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) : MemLp id 4 μ := by
  apply (integrable_norm_rpow_iff (p := 4) continuous_id.aestronglyMeasurable
    (by norm_num) (by norm_num)).mp
  simpa using integrable_norm_pow_of_exp_cond μ hr hexp 4

/-- Letwin arXiv:2607.24164v1, Theorem 1.2: the constant-eight quadratic-form variance bound
for arbitrary isotropic log-concave probability laws, with no compact-support assumption. -/
theorem letwinQuadraticBound {n : ℕ} (hn : 0 < n)
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    (hLC : LogConcave ν) (hiso : Isotropic ν) :
    LetwinQuadraticBound (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff ν).1 hLC).exists_integrable_exp_norm
  let νR : ℕ → Measure E := fun R => (ν : Measure E)[|Metric.closedBall (0 : E) R]
  let Sg : ℕ → E →L[ℝ] E := fun R => Covariance.operator (νR R)
  let T : ℕ → E →L[ℝ] E := fun R => inverseSqrt (Sg R)
  let a : ℕ → E := fun R => ∫ x, x ∂(νR R)
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, νR, id_eq, hiso.mean_zero] using
      Probability.tendsto_integral_cond_closedBall (ν : Measure E)
        (hiso.memLp_two.integrable (by norm_num))
  have hmass : ∀ᶠ R : ℕ in atTop, (ν : Measure E) (Metric.closedBall (0 : E) R) ≠ 0 :=
    eventually_measure_closedBall_ne_zero_cond (ν : Measure E)
  have hcum2 := tendsto_cumulant_cond_closedBall (ν : Measure E) hr hexp 2
  have hSg : Tendsto Sg atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hcum2
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hcum2
    filter_upwards [hmass] with R hR
    have : IsProbabilityMeasure (νR R) := cond_isProbabilityMeasure hR
    have hexpR : Integrable (fun x => Real.exp (r * ‖x‖)) (νR R) :=
      (hexp.restrict (s := Metric.closedBall (0 : E) R)).smul_measure (ENNReal.inv_ne_top.2 hR)
    refine opNorm_le_of_inner_eq fun v w => ?_
    simp only [sub_apply]
    rw [cumulant_two_eq_covariance_of_integrable_exp
        ((ν : Measure E)[|Metric.closedBall (0 : E) R]) hr hexpR v w,
      cumulant_two_eq_covariance_of_integrable_exp (ν : Measure E) hr hexp v w,
      hiso.covariance_identity]
    simp [Sg, νR, inner_sub_left]
  have hpos : ∀ R, (Sg R).IsPositive := fun R =>
    (ContinuousLinearMap.isPositive_iff' _).mpr
      ⟨Covariance.operator_isSelfAdjoint _, fun v => by
        rw [Covariance.operator_inner]; exact covarianceBilin_self_nonneg v⟩
  have hlt : ∀ᶠ R in atTop, ‖Sg R - 1‖ < 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hSg).eventually (gt_mem_nhds one_pos)
  have hunit : ∀ᶠ R in atTop, IsUnit (Sg R) := hlt.mono fun R hR =>
    isUnit_of_inner_self_pos _ fun v hv => inner_self_pos_of_norm_sub_one_lt hR hv
  have hT : Tendsto T atTop (𝓝 1) := tendsto_inverseSqrt_one hSg (Eventually.of_forall hpos) hunit
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hmass.and hunit)
  have happrox (k : ℕ) : ∃ η : ProbabilityMeasure E,
      LogConcave η ∧ Isotropic η ∧ IsCompact (η : Measure E).support ∧
      (η : Measure E) = (νR (k + N)).map (fun x => T (k + N) (x - a (k + N))) := by
    obtain ⟨hm, hu⟩ := hN (k + N) (by omega)
    have : IsProbabilityMeasure (νR (k + N)) := cond_isProbabilityMeasure hm
    let μR : ProbabilityMeasure E := ⟨νR (k + N), inferInstance⟩
    have hLCR : LogConcave μR := hLC.cond (convex_closedBall _ _) Metric.isClosed_closedBall hm
    have hcR : IsCompact (μR : Measure E).support :=
      isCompact_support_cond_closedBall (ν : Measure E) (k + N)
    obtain ⟨η, W, hW, hiso', hLC', hc', hmap⟩ := exists_standardized μR hLCR hcR (hpos _) hu
    refine ⟨η, hLC', hiso', hc', ?_⟩
    change (η : Measure E) = (νR (k + N)).map
      (fun x => (W : E →L[ℝ] E) (x - a (k + N))) at hmap
    rwa [hW] at hmap
  choose η hηLC hηiso hηcompact hηmap using happrox
  have hη4 (k : ℕ) : MemLp id 4 (η k : Measure E) := by
    obtain ⟨s, hs, he⟩ := ((KLS.LogConcave.borel_iff (η k)).1 (hηLC k)).exists_integrable_exp_norm
    exact memLp_four_of_exp _ hs he
  apply letwinQuadraticBound_of_tendsto_moments (fun k => (η k : Measure E)) (ν : Measure E)
    hη4 (memLp_four_of_exp _ hr hexp)
  · intro d _hd v
    have h := Probability.tendsto_integral_prod_inner_affine_cond_closedBall
      (ν : Measure E) d (integrable_norm_pow_of_exp_cond _ hr hexp d) T a hT ha v
    have htail : Tendsto (fun k : ℕ => k + N) atTop atTop :=
      tendsto_add_atTop_nat N
    apply (h.comp htail).congr'
    exact Eventually.of_forall fun k => by
      dsimp only [Function.comp_def]
      rw [hηmap k, integral_map (by fun_prop) (by fun_prop)]
  · intro k
    exact letwinCompactBound n hn (η k) (hηLC k) (hηiso k) (hηcompact k)

/-- Matrix form of Letwin Theorem 1.2, with the source normalization `8 tr(M²)`.
Singular and indefinite symmetric matrices are included. -/
theorem matrix_variance_le_eight {n : ℕ} (hn : 0 < n)
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    (hLC : LogConcave ν) (hiso : Isotropic ν)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    variance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, M i j * x i * x j)
      (ν : Measure (EuclideanSpace ℝ (Fin n))) ≤ 8 * Matrix.trace (M * M) := by
  let E := EuclideanSpace ℝ (Fin n)
  let A : E →L[ℝ] E := (Matrix.toEuclideanLin M).toContinuousLinearMap
  have hsym : A.toLinearMap.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hM)
  have hA : IsSelfAdjoint A := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hsym
  have hcoord (x : E) : (∑ i, ∑ j, M i j * x i * x j) = ⟪A x, x⟫ :=
    Probability.Stein.quadratic_matrix_sum_eq_inner_action M x
  have htrace : LinearMap.trace ℝ E (A.toLinearMap * A.toLinearMap) =
      Matrix.trace (M * M) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
      LinearMap.toMatrix_mul]
    simp [A, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hHS : (∑ i, ∑ j, ⟪A (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E j⟫ ^ 2) =
      Matrix.trace (M * M) :=
    (sum_inner_apply_sq_eq_trace_comp_of_isSymmetric A hsym (stdOrthonormalBasis ℝ E)).trans htrace
  have hb := hLC.letwinQuadraticBound hn hiso A hA
  change (∫ x : E, (⟪A x, x⟫ - ∫ y : E, ⟪A y, y⟫ ∂(ν : Measure E)) ^ 2 ∂(ν : Measure E)) ≤
    8 * ∑ i, ∑ j, ⟪A (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E j⟫ ^ 2 at hb
  rw [hHS] at hb
  have hv : variance (fun x : E => ⟪A x, x⟫) (ν : Measure E) =
      ∫ x : E, (⟪A x, x⟫ - ∫ y : E, ⟪A y, y⟫ ∂(ν : Measure E)) ^ 2 ∂(ν : Measure E) :=
    variance_eq_integral (A.continuous.inner continuous_id).measurable.aemeasurable
  change variance (fun x : E => ∑ i, ∑ j, M i j * x i * x j) (ν : Measure E) ≤ _
  rw [show (fun x : E => ∑ i, ∑ j, M i j * x i * x j) =
    (fun x : E => ⟪A x, x⟫) from funext hcoord, hv]
  exact hb

end FunctionalInequalities.KLS.LogConcave

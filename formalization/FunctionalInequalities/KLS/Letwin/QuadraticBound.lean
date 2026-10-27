import FunctionalInequalities.KLS.Letwin.CompactBound
import FunctionalInequalities.Probability.Conditioning

/-!
# Letwin's constant-eight bound without compact support

Letwin arXiv:2607.24164v1, Theorem 1.2: for every positive dimension, every isotropic
log-concave probability law and every real self-adjoint operator, the quadratic-form variance
is at most eight times the squared Hilbert–Schmidt norm. `letwinQuadraticBound` gives the
operator form; `matrix_variance_le_eight` gives the source normalization `8 tr(M²)` for every
symmetric matrix, including singular and indefinite matrices.

The standardized growing-ball truncations of `Suspension.exists_compact_moment_approximation` (conditioned on
expanding closed balls, centered and covariance-whitened) are compactly supported isotropic log-concave laws whose
mixed moments of degree at most four converge. The accepted compact bound then passes to the limit. The growing-ball
step does not require a common compact support or an additional moment premise: log-concavity supplies a positive
exponential moment.

This proves the noncompact quadratic bound using the compact counterpart. The regular approximants of Lemma A.1
are `exists_regular_approximation` (`KLS/Letwin/Approximation.lean`); Theorem 1.1 is not established here.
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
  simpa using FunctionalInequalities.Probability.integrable_norm_pow_of_exp μ hr hexp 4

/-- Letwin arXiv:2607.24164v1, Theorem 1.2: the constant-eight quadratic-form variance bound
for arbitrary isotropic log-concave probability laws, with no compact-support assumption. -/
theorem letwinQuadraticBound {n : ℕ} (hn : 0 < n)
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    (hLC : LogConcave ν) (hiso : Isotropic ν) :
    LetwinQuadraticBound (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨η, hη, hmom⟩ := Suspension.exists_compact_moment_approximation hLC hiso
  have hmem (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : LogConcave μ) :
      MemLp id 4 (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff μ).1 hμ).exists_integrable_exp_norm
    exact memLp_four_of_exp _ hr hexp
  exact letwinQuadraticBound_of_tendsto_moments (fun k => (η k : Measure (EuclideanSpace ℝ (Fin n))))
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (fun k => hmem (η k) (hη k).1) (hmem ν hLC) hmom
    fun k => letwinCompactBound n hn (η k) (hη k).1 (hη k).2.1 (hη k).2.2

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

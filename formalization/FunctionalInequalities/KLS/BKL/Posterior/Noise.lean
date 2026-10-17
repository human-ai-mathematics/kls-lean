import FunctionalInequalities.Probability.Posterior.CompactDomain
import FunctionalInequalities.KLS.IsotropicSupport
import FunctionalInequalities.Probability.Posterior.Generator
import FunctionalInequalities.KLS.LogConcave.Density.ConcaveTilt
import FunctionalInequalities.Analysis.Operator.InverseSqrt
import FunctionalInequalities.Probability.Posterior.JointRegularity
import FunctionalInequalities.Probability.Transport
import FunctionalInequalities.KLS.LogConcave.Isotropic
import FunctionalInequalities.Probability.IntrinsicTranslation
import FunctionalInequalities.Probability.Covariance.CauchySchwarz
import FunctionalInequalities.Probability.CoordinateThirdMoment
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import FunctionalInequalities.KLS.BKL.Posterior.Covariance

/-!
# Noise estimates and coordinate identities for compact posteriors

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section NoiseBound

open ProbabilityTheory

/-- **Noise functional of (68), variance bound**: `‖D_c(∫ f dμ_{·,Q})(c) ∘ A^{-1/2}‖² ≤ Var_{μ_{c,Q}} f`. -/
theorem Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_variance
    (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (c : E) (Q : E →L[ℝ] E) :
    ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp
        (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure E)))‖ ^ 2 ≤
      variance f (compactPosterior μ hc c Q : Measure E) := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    let ν : Measure E := compactPosterior μ hc c Q
    let A : E →L[ℝ] E := Covariance.operator ν
    let S : E →L[ℝ] E := inverseSqrt A

    have hS : IsSelfAdjoint S := by
      simpa [S, A, ν] using
        (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso c Q).1

    have hsand : S * Covariance.operator ν * S = 1 := by
      simpa [S, A] using
        (Analysis.inverseSqrt_mul_mul_inverseSqrt
          (Covariance.operator ν)
          (Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q)
          (Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q))

    have h2 : MemLp (id : E → E) 2 ν := by
      simpa [ν] using compactPosterior_memLp_id_two μ hc c Q

    have hop :
        ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp S‖
          ≤ Real.sqrt (variance f ν) := by
      apply ContinuousLinearMap.opNorm_le_bound
        ((fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp S)
        (Real.sqrt_nonneg _)
      intro h

      have hX : MemLp f 2 ν := by
        change MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q))
        exact
          memLp_two_tilted_of_compact μ hc
            (φ := quadraticExponent c Q)
            (by
              unfold quadraticExponent
              fun_prop)
            hf hfb

      have hY : MemLp (fun x => ⟪S h, x⟫) 2 ν := by
        change
          MemLp (fun x => ⟪S h, x⟫) 2
            ((μ : Measure E).tilted (quadraticExponent c Q))
        exact
          memLp_two_tilted_quadraticExponent_of_compact μ hc c Q
            (by fun_prop)

      have hcov :
          covariance f (fun x => ⟪S h, x⟫) ν ^ 2
            ≤ variance f ν * variance (fun x => ⟪S h, x⟫) ν :=
        Probability.covariance_sq_le_variance_mul_variance hX hY

      have hvar :
          variance (fun x => ⟪S h, x⟫) ν = ‖h‖ ^ 2 :=
        Covariance.variance_inner_eq_of_sandwich ν h2 S hS hsand h

      have hsq :
          covariance f (fun x => ⟪S h, x⟫) ν ^ 2
            ≤ variance f ν * ‖h‖ ^ 2 := by
        calc
          covariance f (fun x => ⟪S h, x⟫) ν ^ 2
              ≤ variance f ν * variance (fun x => ⟪S h, x⟫) ν := hcov
          _ = variance f ν * ‖h‖ ^ 2 := by rw [hvar]

      have hfd :
          fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (S h)
            = covariance f (fun x => ⟪S h, x⟫) ν := by
        change
          fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (S h)
            = covariance f (fun x => ⟪S h, x⟫)
                ((μ : Measure E).tilted (quadraticExponent c Q))
        exact fderiv_posteriorExpectation_c_apply μ hc hf hC hfb c Q (S h)

      have habs :
          |covariance f (fun x => ⟪S h, x⟫) ν|
            ≤ Real.sqrt (variance f ν) * ‖h‖ := by
        have hv : 0 ≤ variance f ν := variance_nonneg f ν
        have hs : (Real.sqrt (variance f ν)) ^ 2 = variance f ν :=
          Real.sq_sqrt hv
        have hn :
            0 ≤ Real.sqrt (variance f ν) * ‖h‖ :=
          mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
        nlinarith [hsq, hs,
          sq_abs (covariance f (fun x => ⟪S h, x⟫) ν)]

      change
        ‖fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (S h)‖
          ≤ Real.sqrt (variance f ν) * ‖h‖
      rw [hfd, Real.norm_eq_abs]
      exact habs

    have hsq :
        ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp S‖ ^ 2
          ≤ variance f ν := by
      have hv : 0 ≤ variance f ν := variance_nonneg f ν
      have hs : (Real.sqrt (variance f ν)) ^ 2 = variance f ν :=
        Real.sq_sqrt hv
      nlinarith [hop, norm_nonneg
        ((fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp S)]

    simpa [S, A, ν] using hsq


/-- **Noise functional of (68), uniform bound**: `‖D_c(∫ f dμ_{·,Q})(c) ∘ A^{-1/2}‖² ≤ C²` for `f` bounded by `C` on
the prior support (the posterior has the prior's support). -/
theorem Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_sq
    (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (c : E) (Q : E →L[ℝ] E) :
    ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp
        (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure E)))‖ ^ 2 ≤ C ^ 2 := by
    let ν : Measure E := compactPosterior μ hc c Q
    have hbound : ∀ᵐ x ∂ν, ‖f x‖ ≤ C := by
      filter_upwards [Measure.support_mem_ae] with x hx
      apply hfb x
      rw [← compactPosterior_support μ hc c Q]
      exact hx
    have hLp : MemLp f 2 ν := by
      exact MemLp.of_bound hf.aestronglyMeasurable C hbound
    have hsq : ∀ᵐ x ∂ν, f x ^ 2 ≤ C ^ 2 := by
      filter_upwards [hbound] with x hx
      have hx' : |f x| ≤ C := by
        simpa [Real.norm_eq_abs] using hx
      have h₁ : -C ≤ f x := (abs_le.mp hx').1
      have h₂ : f x ≤ C := (abs_le.mp hx').2
      nlinarith
    have hsq_int : (∫ x, f x ^ 2 ∂ν) ≤ C ^ 2 := by
      calc
        (∫ x, f x ^ 2 ∂ν) ≤ ∫ _x, C ^ 2 ∂ν :=
          integral_mono_ae hLp.integrable_sq (integrable_const _) hsq
        _ = C ^ 2 := by simp [ν]
    have hvar : variance f ν ≤ C ^ 2 := by
      calc
        variance f ν =
            (∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 := by
          simpa [Pi.pow_apply] using variance_eq_sub hLp
        _ ≤ C ^ 2 := by
          linarith [hsq_int, sq_nonneg (∫ x, f x ∂ν)]
    exact
      (Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_variance
        μ hc hiso hf hC hfb c Q).trans (by simpa [ν] using hvar)

end NoiseBound
section NoiseEntries

/-- **Principal-root noise entries of (69)**: `(P H_i P) j k = ∫ (σV)_j (σV)_k (σV)_i dν`. -/
theorem Isotropic.operatorMatrix_inverseSqrt_mul_thirdMomentMatrix_mul_apply {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) (hiso : KLS.Isotropic μ)
    (c : EuclideanSpace ℝ (Fin n)) (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (i j k : Fin n) :
    (operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ)
          (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))) *
        (Matrix.of fun j' k' : Fin n =>
          ∫ x, (x - posteriorMean μ c Q) j' * (x - posteriorMean μ c Q) k' *
            ⟪inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
                (EuclideanSpace.basisFun (Fin n) ℝ i), x - posteriorMean μ c Q⟫
            ∂(compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n)))) *
        operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ)
          (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n)))))) j k =
      ∫ x, (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
              (x - posteriorMean μ c Q)) j *
          (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
              (x - posteriorMean μ c Q)) k *
          (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
              (x - posteriorMean μ c Q)) i
        ∂(compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨R, hR⟩ :=
      FunctionalInequalities.Probability.Posterior.compactPosterior_exists_ae_norm_sub_le
        μ hc c Q (posteriorMean μ c Q)
    have hσ :
        IsSelfAdjoint
          (inverseSqrt
            (Covariance.operator
              (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))) :=
      (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso c Q).1
    exact
      FunctionalInequalities.Probability.operatorMatrix_mul_coordinateThirdMoment_mul_apply_of_ae_norm_sub_le
        (ν := (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
        (posteriorMean μ c Q) R hR _ hσ i j k

end NoiseEntries

end FunctionalInequalities.KLS

import FunctionalInequalities.KLS.Target
import FunctionalInequalities.KLS.LogConcave.Poincare
import FunctionalInequalities.Poincare.Convolution
import FunctionalInequalities.Poincare.Gaussian.Multivariate

/-!
# Calling KLS: variance bounds and Gaussian smoothing

Start with `covariance_bound`, then use `Holds.variance_le` for a test function.
`isotropic_bound` removes the covariance factor, including dimension zero.
`gaussian_convolution_bound` adds independent Gaussian noise with covariance `t Id`.
Each existential constant is chosen before the dimension and the law.

The last call supplies the Poincaré input of Kook–Vempala–Zhang, *In-and-Out:
Algorithmic Diffusion for Sampling Convex Bodies*, NeurIPS 2024, Definition 2 and
the Poincaré part of Lemma 11 (Appendix B.2). The normalization is
`Var f ≤ C ∫ ‖∇f‖²`, with Gaussian variance `t` and no factor `1/2`.
Here the frontend is smooth L² tests with integrable squared gradient. This client
does not formalize the sampler, its divergence contraction, or the log-Sobolev part.

Source: https://papers.nips.cc/paper_files/paper/2024/file/c4006ff54a7bbda74c09bad6f7586f5b-Paper-Conference.pdf
-/

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped ContDiff

namespace Examples.KlsApplications

/-- Extract one universal covariance-normalized smooth-test bound from `KLS.kls`.
Log-concavity supplies the finite second moment required by the target theorem. -/
theorem covariance_bound :
    ∃ C : NNReal, ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      KLS.LogConcave μ →
      Poincare.SmoothTest.Holds (μ : Measure (EuclideanSpace ℝ (Fin n)))
        ((C : ℝ) * ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖) := by
  obtain ⟨C, hC⟩ := KLS.kls
  refine ⟨C, ?_⟩
  intro n μ hLC
  let B : NNReal := C * ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖₊
  have hbound : Poincare.SmoothGradient.Ambient.constant μ ≤ (B : ENNReal) := by
    rw [← Poincare.SmoothTest.constant_eq_ambient μ,
      hLC.smoothTest_constant_eq_localSlope]
    simpa only [B, ENNReal.coe_mul, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
      using hC n μ hLC hLC.memLp_id_two
  have hholds := (Poincare.SmoothTest.holds_iff_ambient μ B).mpr
    ((Poincare.SmoothGradient.Ambient.holds_iff_constant_le μ B).mpr hbound)
  exact hholds

/-- Apply the extracted bound to an actual test; retain both L² and finite-energy premises. -/
theorem variance_bound :
    ∃ C : NNReal, ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      KLS.LogConcave μ → ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ f → MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
      Integrable (fun x => ‖gradient f x‖ ^ 2) (μ : Measure (EuclideanSpace ℝ (Fin n))) →
      variance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
        (C : ℝ) * ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖ *
        (∫ x, ‖gradient f x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨C, hC⟩ := covariance_bound
  refine ⟨C, ?_⟩
  intro n μ hLC f hf hf2 henergy
  exact (hC n μ hLC).variance_le ⟨hf, hf2, henergy⟩

/-- Isotropy gives the same dimension-independent bound without a covariance factor. -/
theorem isotropic_bound :
    ∃ C : NNReal, ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      KLS.LogConcave μ → KLS.Isotropic μ →
        Poincare.SmoothTest.Holds (μ : Measure (EuclideanSpace ℝ (Fin n))) (C : ℝ) := by
  obtain ⟨C, hC⟩ := covariance_bound
  refine ⟨C, ?_⟩
  intro n μ hLC hiso
  apply (hC n μ hLC).mono
  calc
    (C : ℝ) * ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖ ≤ (C : ℝ) * 1 := by
      apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
      rw [hiso.covariance_identity]
      exact ContinuousLinearMap.norm_id_le
    _ = (C : ℝ) := mul_one _

/-- The Poincaré input for a Gaussian forward step: `X + sqrt(t) G` has bound `C + t`.
The new variance parameter is nonnegative and includes `t = 0`. -/
theorem gaussian_convolution_bound :
    ∃ C : NNReal, ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      KLS.LogConcave μ → KLS.Isotropic μ → ∀ t : NNReal,
        Poincare.SmoothTest.Holds
          ((μ : Measure (EuclideanSpace ℝ (Fin n))).conv
            ((stdGaussian (EuclideanSpace ℝ (Fin n))).map
            (fun x => Real.sqrt (t : ℝ) • x))) ((C : ℝ) + t) := by
  obtain ⟨C, hC⟩ := isotropic_bound
  refine ⟨C, ?_⟩
  intro n μ hLC hiso t
  have hnoise := Poincare.SmoothTest.holds_stdGaussian_map_smul
    (V := EuclideanSpace ℝ (Fin n)) (Real.sqrt (t : ℝ))
  simpa only [Real.sq_sqrt t.coe_nonneg] using (hC n μ hLC hiso).conv hnoise

end Examples.KlsApplications

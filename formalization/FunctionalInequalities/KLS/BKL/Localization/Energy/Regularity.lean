import FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
import FunctionalInequalities.KLS.BKL.CumulantEnergy.Conjugation
import FunctionalInequalities.Analysis.Tensor.EnergyForm
import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
import FunctionalInequalities.KLS.BKL.Posterior.Covariance
import FunctionalInequalities.KLS.BKL.Posterior.Regularity
import FunctionalInequalities.Probability.Diffusion.Generator

/-!
# Regularity of posterior cumulant energies and their generators

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization


variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

theorem contDiff_cumulantEnergy_posterior (hiso : KLS.Isotropic μ) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (fun q : Param n =>
      cumulantEnergy (compactPosterior μ hc q.1 q.2 :
        Measure (EuclideanSpace ℝ (Fin n))) d u) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let A : Param n → E →L[ℝ] E :=
    fun q => Covariance.operator (compactPosterior μ hc q.1 q.2 : Measure E)
  have hAi : ContDiff ℝ ∞ (fun q => Ring.inverse (A q)) := by
    simpa only [A] using
      KLS.Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso
  have hT : ∀ J : Fin d → Fin n,
      ContDiff ℝ ∞ (fun q : Param n =>
        cumulant (compactPosterior μ hc q.1 q.2 : Measure E) (d + 1)
          (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))) := by
    intro J
    exact contDiff_cumulant_posterior μ hc
      (Nat.one_le_iff_ne_zero.mpr (by omega))
      (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))
  have hEq :
      (fun q : Param n =>
        cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure E) d u) =
      (fun q : Param n =>
        CoordinateTensor.energyForm (A q)
          (fun J => cumulant (compactPosterior μ hc q.1 q.2 : Measure E) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)))) := by
    funext q
    calc
      cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure E) d u =
          CoordinateTensor.energyForm
            ((1 : E →L[ℝ] E) *
              Covariance.operator (compactPosterior μ hc q.1 q.2 : Measure E) *
              (1 : E →L[ℝ] E))
            (fun J => cumulant (compactPosterior μ hc q.1 q.2 : Measure E) (d + 1)
              (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))) := by
        exact cumulantEnergy_eq_energyForm
          (compactPosterior μ hc q.1 q.2 : Measure E)
          (by
            simpa only [A] using
              KLS.Isotropic.compactPosterior_covariance_isPositive μ hc hiso q.1 q.2)
          (by
            simpa only [A] using
              KLS.Isotropic.compactPosterior_covariance_isUnit μ hc hiso q.1 q.2)
          (1 : E →L[ℝ] E) (by simp) (by simp) d u
      _ = CoordinateTensor.energyForm (A q)
          (fun J => cumulant (compactPosterior μ hc q.1 q.2 : Measure E) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))) := by
        simp only [one_mul, mul_one, A]
  rw [hEq]
  unfold CoordinateTensor.energyForm
  apply ContDiff.sum
  intro J hJ
  apply ContDiff.sum
  intro K hK
  apply ContDiff.mul
  · apply ContDiff.mul
    · exact hT J
    · exact hT K
  · apply contDiff_prod
    intro s hs
    exact ContDiff.inner ℝ contDiff_const
      (hAi.clm_apply contDiff_const)

/-- The generator of a `C³` function is continuous (continuous coefficients). -/
theorem continuous_generator_of_contDiff_three (hiso : KLS.Isotropic μ) {F : Param n → ℝ}
    (hF : ContDiff ℝ 3 F) : Continuous (generator μ hc F) := by
  have hdrift : Continuous (drift μ hc) :=
    (locallyLipschitz_drift μ hc hiso).continuous
  have hfirst : Continuous (fun q => fderiv ℝ F q (drift μ hc q)) := by
    have h :=
      hF.continuous_fderiv_apply (by norm_num :
        (3 : WithTop ℕ∞) ≠ 0)
    exact h.comp (continuous_id.prodMk hdrift)
  have hsecond (k : Fin n) :
      Continuous
        (fun q => fderiv ℝ (fderiv ℝ F) q
          (noise μ hc q k) (noise μ hc q k)) := by
    have hnoise : Continuous (fun q => noise μ hc q k) :=
      (locallyLipschitz_noise μ hc hiso k).continuous
    have h :=
      (hF.fderiv_right
        (m := (1 : WithTop ℕ∞))
        (by norm_num :
          (1 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))).continuous_fderiv_apply
        (by norm_num :
          (1 : WithTop ℕ∞) ≠ 0)
    have h' : Continuous
        (fun q => fderiv ℝ (fderiv ℝ F) q (noise μ hc q k)) :=
      h.comp (continuous_id.prodMk hnoise)
    exact h'.clm_apply hnoise
  have hsum :
      Continuous
        (fun q => ∑ k, fderiv ℝ (fderiv ℝ F) q
          (noise μ hc q k) (noise μ hc q k)) := by
    exact continuous_finsetSum Finset.univ (by
      intro k hk
      exact hsecond k)
  unfold generator diffusionGenerator
  exact hfirst.add (continuous_const.mul hsum)

end FunctionalInequalities.KLS.BKL.Localization

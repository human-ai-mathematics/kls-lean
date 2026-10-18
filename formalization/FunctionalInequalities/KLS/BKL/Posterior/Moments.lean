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
import FunctionalInequalities.KLS.BKL.Posterior.Standardization
import FunctionalInequalities.KLS.BKL.Posterior.Covariance

/-!
# Sixth moments of standardized compact posteriors
-/

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section SixthMoment

/-- **Canonical sixth moment of the posterior**: `∫ ‖Cov(μ_{c,Q})^{-1/2} (x − a)‖⁶ dμ_{c,Q} ≤ C₆(n)` with the explicit
isotropic log-concave constant, for every finite self-adjoint PSD `Q` and every `c`. -/
theorem Isotropic.integral_norm_pow_six_inverseSqrt_sub_posteriorMean_le {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) (hiso : KLS.Isotropic μ)
    (hLC : KLS.LogConcave μ) (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hSym : IsSelfAdjoint Q)
    (hQ : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪Q x, x⟫) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
          (x - posteriorMean μ c Q)‖ ^ 6) (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ‖inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
          (x - posteriorMean μ c Q)‖ ^ 6 ∂(compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (Nat.factorial 6 : ℝ) / (Real.log 3 / (4 * (2 * Real.sqrt ((n : ℝ) + 1)))) ^ 6 *
        ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))) := by
    obtain ⟨W, hW, hη⟩ :=
      Isotropic.exists_inverseSqrt_equiv_isotropic_standardized μ hc hiso c Q
    let ν := compactPosterior μ hc c Q
    let a := posteriorMean μ c Q
    let η :=
      Probability.mapContinuousLinearEquiv
        (Probability.translateLaw ν (-a)) W
    have hLCν : KLS.LogConcave ν :=
      compactPosterior_logConcave μ hc hLC c Q hSym hQ
    have hLCη : KLS.LogConcave η := by
      dsimp [η]
      exact (hLCν.translateLaw (-a)).mapContinuousLinearEquiv W
    have hm :=
      KLS.LogConcave.integral_norm_pow_le_of_isotropic hLCη hη 6
    dsimp only at hm
    obtain ⟨hint, hle⟩ := hm
    have hWν :
        (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
          inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))) := by
      simpa [ν] using hW
    have hmap :
        (η : Measure (EuclideanSpace ℝ (Fin n))) =
          (ν : Measure (EuclideanSpace ℝ (Fin n))).map
            (fun x : EuclideanSpace ℝ (Fin n) =>
              inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                (x - a)) := by
      dsimp [η]
      rw [Probability.coe_mapContinuousLinearEquiv,
        Probability.coe_translateLaw]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      change
        (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (-a + x) =
          inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
            (x - a)
      rw [hWν]
      simp only [map_add, map_neg, sub_eq_add_neg]
      abel
    have hmeas :
        Measurable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
              (x - a)) :=
      Measurable.comp
        ((inverseSqrt
            (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))).continuous.measurable)
        (measurable_id.sub measurable_const)
    have hint_map :
        Integrable (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ ^ 6)
          ((ν : Measure (EuclideanSpace ℝ (Fin n))).map
            (fun x : EuclideanSpace ℝ (Fin n) =>
              inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                (x - a))) := by
      rw [← hmap]
      exact hint
    have hint' :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ‖inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                (x - a)‖ ^ 6)
          (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      have h :=
        (integrable_map_measure
          (μ := (ν : Measure (EuclideanSpace ℝ (Fin n))))
          (f := fun x : EuclideanSpace ℝ (Fin n) =>
            inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
              (x - a))
          (g := fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ ^ 6)
          hint_map.aestronglyMeasurable hmeas.aemeasurable).mp hint_map
      simpa [Function.comp_def] using h
    have hle_map := hle
    rw [hmap] at hle_map
    have hI :
        (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ ^ 6
            ∂((ν : Measure (EuclideanSpace ℝ (Fin n))).map
              (fun x : EuclideanSpace ℝ (Fin n) =>
                inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                  (x - a)))) =
          ∫ x : EuclideanSpace ℝ (Fin n),
            ‖inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                (x - a)‖ ^ 6
            ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      exact integral_map hmeas.aemeasurable (by fun_prop)
    rw [hI] at hle_map
    dsimp [ν, a] at hint' hle_map
    exact ⟨hint', hle_map⟩

end SixthMoment

end FunctionalInequalities.KLS

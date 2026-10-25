import FunctionalInequalities.Energy.CovarianceGradient.Isometry
import FunctionalInequalities.Probability.IntrinsicTranslation

/-! # Covariance-gradient relaxation under ambient translation -/

noncomputable section
open MeasureTheory

namespace FunctionalInequalities.Energy.CovarianceGradient.Intrinsic

open Energy.Euclidean Probability

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]


  (μ : ProbabilityMeasure E) (b : E)

omit [CompleteSpace E] in
/-- Translating `μ` in the ambient space: there is a linear isometric equivalence between the two
intrinsic `L²` spaces preserving variance and intertwining the affine covariance relaxations. -/
theorem exists_translateLaw_isometry :
    ∃ e : Lp ℝ 2 (Probability.intrinsicMeasure (Probability.translateLaw μ b) :
        Measure (affineSupport (Probability.translateLaw μ b)).direction) ≃ₗᵢ[ℝ]
        Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (affineSupport μ).direction),
      (∀ f, L2.variance (Probability.intrinsicMeasure μ) (e f) =
        L2.variance (Probability.intrinsicMeasure (Probability.translateLaw μ b)) f) ∧
      ∀ f, energy (Probability.translateLaw μ b) f = energy μ (e f) := by
  rw [energy_eq_relaxation_intrinsicMeasure (Probability.translateLaw μ b), Probability.intrinsicMeasure_translateLaw]
  refine ⟨(L2.Translation.pullbackEquiv _ _).trans (L2.LinearIsometry.pullbackEquiv _ _), fun f ↦ ?_, fun f ↦ ?_⟩
  · rw [LinearIsometryEquiv.trans_apply, L2.LinearIsometry.variance_pullbackEquiv, L2.Translation.variance_pullbackEquiv]
  · rw [LinearIsometryEquiv.trans_apply, Energy.CovarianceGradient.relaxation_translateLaw, Energy.CovarianceGradient.relaxation_mapLinearIsometryEquiv]
    rfl

end FunctionalInequalities.Energy.CovarianceGradient.Intrinsic

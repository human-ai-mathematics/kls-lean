import FunctionalInequalities.KLS.BKL.LetwinApproximation
import FunctionalInequalities.KLS.BKL.Theorem41
noncomputable section
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Analysis.BakryEmery
namespace FunctionalInequalities.KLS.LogConcave.Suspension
theorem codex_same_frozen_statement
    (h : ∀ (n : ℕ), 0 < n → ∀ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ)
      (κ : ℝ), 0 < κ → IsCompact K → Convex ℝ K → (interior K).Nonempty → ContDiff ℝ ∞ W →
      ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) →
      ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        (μ : Measure (EuclideanSpace ℝ (Fin n))) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) →
        KLS.Isotropic μ → LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    LetwinCompactBound := by
  exact letwinCompactBound_of_regularClass h

theorem codex_conjecture_of_regularClass
    (h : ∀ (n : ℕ), 0 < n → ∀ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ)
      (κ : ℝ), 0 < κ → IsCompact K → Convex ℝ K → (interior K).Nonempty → ContDiff ℝ ∞ W →
      ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) →
      ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        (μ : Measure (EuclideanSpace ℝ (Fin n))) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) →
        KLS.Isotropic μ → LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    FunctionalInequalities.KLS.Conjecture := by
  exact FunctionalInequalities.KLS.BKL.Localization.conjecture_of_letwinCompact (letwinCompactBound_of_regularClass h)

#print axioms letwinCompactBound_of_regularClass
#print axioms codex_same_frozen_statement
#print axioms codex_conjecture_of_regularClass
end FunctionalInequalities.KLS.LogConcave.Suspension

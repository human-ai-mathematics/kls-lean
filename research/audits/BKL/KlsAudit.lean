import solutions.ThmBklPoincare
import FunctionalInequalities.KLS.Target
import FunctionalInequalities.KLS.BKL.Poincare
/-!
Independent specification and consumption clients of BKL Theorem 1.1 and of the proved `KLS.kls`.
The source statement and the KLS sentence are handwritten here and matched against the certificate and the
actual unchanged `KLS.Conjecture`.
-/

noncomputable section
open MeasureTheory
namespace KlsAudit

/-- BKL Theorem 1.1, handwritten: one real `C > 0` for every `n ≥ 1` and every isotropic log-concave law. -/
def ExpectedBkl : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ ≤ ENNReal.ofReal C

theorem expectedBkl : ExpectedBkl := by
  obtain ⟨C, hC, h⟩ := Solutions.ThmBklPoincare.certificate
  refine ⟨C, hC, fun n hn μ hLC hiso => ?_⟩
  rw [ENNReal.ofReal_coe_nnreal]
  exact h n hn μ hLC hiso

/-- The KLS sentence, handwritten: one `C : NNReal` before every dimension and law; log-concave with finite
second moment; literature constant at most `C ‖Cov‖`. -/
def ExpectedKls : Prop :=
  ∃ C : NNReal, ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
    FunctionalInequalities.KLS.LogConcave μ →
      MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal) *
          ENNReal.ofReal ‖FunctionalInequalities.Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖

/-- The repository target is literally this sentence (definitional unfolding, no conversion). -/
theorem conjecture_eq_expected : FunctionalInequalities.KLS.Conjecture = ExpectedKls := rfl

/-- The actual `KLS.kls` gives the handwritten sentence. -/
theorem expectedKls : ExpectedKls := FunctionalInequalities.KLS.kls

/-- Consumption at an arbitrary dimension, including `0`, with the same constant for every law. -/
theorem kls_same_constant_every_dimension : ∃ C : NNReal,
    (∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)),
      FunctionalInequalities.KLS.LogConcave μ → MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin 0))) →
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal) *
          ENNReal.ofReal ‖FunctionalInequalities.Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin 0)))‖) ∧
    (∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.LogConcave μ → MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal) *
          ENNReal.ofReal ‖FunctionalInequalities.Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖) := by
  obtain ⟨C, h⟩ := FunctionalInequalities.KLS.kls
  exact ⟨C, h 0, h⟩

#print axioms FunctionalInequalities.KLS.BKL.Localization.exists_isotropicBound
#print axioms FunctionalInequalities.KLS.BKL.Localization.conjecture
#print axioms FunctionalInequalities.KLS.kls
#print axioms expectedBkl
#print axioms conjecture_eq_expected
#print axioms expectedKls
#print axioms kls_same_constant_every_dimension

end KlsAudit

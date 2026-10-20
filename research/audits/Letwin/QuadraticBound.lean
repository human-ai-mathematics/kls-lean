import FunctionalInequalities.KLS.Letwin.QuadraticBound

noncomputable section
open MeasureTheory ProbabilityTheory
open FunctionalInequalities
open scoped RealInnerProductSpace

namespace LetwinQuadraticBoundAudit

/-- The expanded contract has no compact-support, invertibility, positivity or extra moment premise. -/
theorem quadratic_variance {n : ℕ} (hn : 0 < n)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hM : IsSelfAdjoint M) :
    ∫ x, (⟪M x, x⟫ - ∫ y, ⟪M y, y⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2
        ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
      8 * ∑ i, ∑ j, ⟪M (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) i),
        stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) j⟫ ^ 2 :=
  hLC.letwinQuadraticBound hn hiso M hM

theorem matrix_variance {n : ℕ} (hn : 0 < n)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    variance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, M i j * x i * x j)
      (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ 8 * Matrix.trace (M * M) :=
  hLC.matrix_variance_le_eight hn hiso M hM

#print axioms FunctionalInequalities.Probability.tendsto_integral_cond_closedBall_of_dominated
#print axioms FunctionalInequalities.Probability.tendsto_integral_cond_closedBall
#print axioms FunctionalInequalities.Probability.tendsto_integral_prod_inner_affine_cond_closedBall
#print axioms KLS.LogConcave.letwinQuadraticBound
#print axioms KLS.LogConcave.matrix_variance_le_eight
#print axioms quadratic_variance
#print axioms matrix_variance

end LetwinQuadraticBoundAudit

module

public import FunctionalInequalities.KLS.Letwin.HessianTrace

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LetwinHessianTraceAudit
open FunctionalInequalities FunctionalInequalities.Probability.Stein

/-- Letwin Theorem 2.5 with `B = Id`: under the imported moment-map properties,
`E_ν ‖∇²φ‖²_HS ≤ 2n`, the bound behind the Stein-kernel estimate of Lemma 2.7. -/
theorem identity_client {n : ℕ}
    {K U : Set (EuclideanSpace ℝ (Fin n))} {V φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hKb : Bornology.IsBounded K) (hKo : IsOpen K)
    (hU : IsOpen U) (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hiso : KLS.Isotropic μ)
    (hφ : ContDiff ℝ ∞ φ)
    (hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)).map (gradient φ) =
      (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hrange : Set.range (gradient φ) ⊆ K)
    (hPD : ∀ x, (hessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x))
    (hbound : ∃ C : ℝ, ∀ x,
      (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef) :
    (∫ x, (hessianMatrix φ x * hessianMatrix φ x).trace
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ))) ≤ 2 * n := by
  have h := (Probability.MomentMeasure.integral_trace_hessian_quadratic_le hKb hKo hU hKU hV hVc
    μ hiso hφ hnorm hmap hrange hPD hMA hbound 1 (Matrix.isSymm_one)).2
  simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.trace_one, Fintype.card_fin] using h

end LetwinHessianTraceAudit
#print axioms FunctionalInequalities.Probability.MomentMeasure.integral_trace_hessian_quadratic_le
#print axioms LetwinHessianTraceAudit.identity_client

import FunctionalInequalities.KLS.CEK.MomentRegularity

noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.R0WeakRegularityAudit

theorem exact_frozen_statement {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal), ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef  := by
  exact Analysis.exists_regular_moment_potential hn hκ hK hKc hKint hW hstrong μ hμ hiso

theorem derivative_norm_bound {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧ ContDiff ℝ 1 u ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ∀ v : EuclideanSpace ℝ (Fin n),
          ‖Matrix.toEuclideanLin (hessianMatrix u x) v‖ ≤ (16 / κ) * ‖v‖ := by
  obtain ⟨u, L, _, _, _, hmap, hu, hG, hdata⟩ :=
    Analysis.exists_regular_moment_potential hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, hmap, hu, ?_⟩
  filter_upwards [hdata, hG.ae_differentiableAt
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx hxd
  refine ⟨hx.2.1, ?_⟩
  intro v
  rw [hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hu hxd]
  change ‖fderiv ℝ (gradient u) x v‖ ≤ (16 / κ) * ‖v‖
  have hnorm := norm_fderiv_le_of_lipschitz ℝ hG (x₀ := x)
  rw [Real.coe_toNNReal (16 / κ) (by positivity)] at hnorm
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))

#print axioms Analysis.exists_regular_moment_potential
#print axioms exact_frozen_statement
#print axioms derivative_norm_bound

end FunctionalInequalities.R0WeakRegularityAudit

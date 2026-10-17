import FunctionalInequalities.KLS.CEK.MomentRegularity.Potential
import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative
import FunctionalInequalities.Analysis.Lipschitz.Gradient

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein

namespace RegularMomentWeakTensorAudit
namespace Difference
/-- Consume the actual R0 producer and export its source-law global difference input;
no centered-difference bound is assumed. -/
theorem produced_regular_moment_with_second_difference {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2 := by
  obtain ⟨u, L, hconv, hLip, hnorm, hmap, hC1, hG, _hdata⟩ :=
    exists_regular_moment_potential hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, L, hconv, hLip, hnorm, hmap, hC1, hG, ?_⟩
  exact secondDifference_le_of_map_gradient hLip hconv hnorm hK hKc
    (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hκ hstrong (hmap.trans hμ) hC1

/-- The exported4/kappa result still recovers the old16/kappa gradient interface. -/
theorem gradient_bound_from_exported_source_difference {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hC1 : ContDiff ℝ 1 u) :
    LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) := by
  have hsd := secondDifference_le_of_map_gradient hu hconv hnorm hK hKc hV hκ hstrong hmap hC1
  have hLip := lipschitzWith_gradient_of_second_difference_le hconv
    (hC1.differentiable (by norm_num)) (show 0 ≤ 4 / κ by positivity) hsd
  have hconstant : 4 * (4 / κ) = 16 / κ := by ring
  rw [hconstant] at hLip
  exact hLip
end Difference
namespace Exponent
/-- Produce the actual R0 moment exponent, retaining normalization and actual pushforward. -/
theorem produced_regular_moment_with_lipschitz_exponent {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) := by
  obtain ⟨u, L, hconv, hLip, hnorm, hmap, hC1, hG, _hdata⟩ :=
    exists_regular_moment_potential hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨LF, hF⟩ := exists_lipschitzWith_neg_add_comp_gradient hLip hG
    (hW.of_le (WithTop.coe_le_coe.mpr le_top))
  exact ⟨u, L, LF, hconv, hLip, hnorm, hmap, hC1, hG, hF⟩
end Exponent
namespace Tensor
/-- The source-law producer supplies actual normalized potentials and a symmetric local-L2 tensor. -/
theorem produced_symmetric_normalized_tensor {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i) := by
  obtain ⟨u, _L, _LF, T, _hconv, _hLip, hnorm, hmap, hC1, hG, _hF, _hw, _hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, T, hnorm, hmap, hT,
    ae_weak_third_derivative_symm hC1 hG (fun k i j => (hT k i j).1)⟩

/-- Actual source-law tensor derivatives supply the weak test identity and locally integrable densities. -/
theorem produced_normalized_weak_testing {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ k i j, LocallyIntegrable (fun x => T x k i j)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
          (∫ x, hessianMatrix u x i j * fderiv ℝ ψ x
            (EuclideanSpace.basisFun (Fin n) ℝ k)) =
            -∫ x, T x k i j * ψ x := by
  obtain ⟨u, _L, _LF, T, _hconv, _hLip, hnorm, hmap, _hC1, _hG, _hF, _hw, _hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, T, hnorm, hmap, fun k i j => ⟨(hT k i j).1.2.1, (hT k i j).1.2.2⟩⟩

end Tensor
end RegularMomentWeakTensorAudit

#print axioms FunctionalInequalities.Analysis.secondDifference_le_of_map_gradient
#print axioms FunctionalInequalities.Analysis.lipschitzWith_gradient_of_map_gradient
#print axioms FunctionalInequalities.Analysis.exists_lipschitzWith_neg_add_comp_gradient
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_weak_tensor
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_potential
#print axioms RegularMomentWeakTensorAudit.Difference.produced_regular_moment_with_second_difference
#print axioms RegularMomentWeakTensorAudit.Difference.gradient_bound_from_exported_source_difference
#print axioms RegularMomentWeakTensorAudit.Exponent.produced_regular_moment_with_lipschitz_exponent
#print axioms RegularMomentWeakTensorAudit.Tensor.produced_symmetric_normalized_tensor
#print axioms RegularMomentWeakTensorAudit.Tensor.produced_normalized_weak_testing

import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ReversePoincare
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SelfImprovement

/-! Independent clients of the reverse local Poincaré inequality and of Bakry's `L¹`
self-improvement. The law is `ν = m.tilted (-U)` for a smooth convex potential, with unit
weight. The clients instantiate arbitrary `L²` data, bounded data, form-domain data and heat
data `P_ε g`, the time `t = 0`, the zero test, and the two pointwise inequalities. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup
  FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
  FunctionalInequalities.Energy.WeightedGradient
open scoped ContDiff
namespace BakryEmeryReverseSelfImprovementAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **Reverse local Poincaré, arbitrary `L²` data.** -/
theorem reverse_poincare (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 < t) :
    2 * t * ∫ x, φ x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) ≤
      (∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x * (f x) ^ 2 ∂(ν : Measure V)) -
        ∫ x, φ x * (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f x) ^ 2
          ∂(ν : Measure V) :=
  two_mul_integral_mul_weakGamma_le m hν hi hνU hU hconv f hφ hφc hφ0 ht

/-- **`L^∞ → Lip`, bounded data**: `|f| ≤ M` gives `2t ∫ φ |T̄P_t f|² ≤ M² ∫ φ`. -/
theorem bounded_data (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V)) {M : ℝ}
    (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ M)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 < t) :
    2 * t * ∫ x, φ x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) ≤ M ^ 2 * ∫ x, φ x ∂(ν : Measure V) :=
  two_mul_integral_mul_weakGamma_le_of_bounded m hν hi hνU hU hconv f hf hφ hφc hφ0 ht

/-- **Zero test for the reverse inequality**: with `φ = 0` it reads `0 ≤ 0`. -/
theorem reverse_zero_test (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    2 * t * ∫ x, (fun _ : V => (0 : ℝ)) x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) = 0 ∧
    2 * t * ∫ x, (fun _ : V => (0 : ℝ)) x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) ≤
      (∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le
          ((memLp_of_contDiff_hasCompactSupport ν (contDiff_const (c := (0 : ℝ)))
            HasCompactSupport.zero).toLp (fun _ : V => (0 : ℝ))) x * (f x) ^ 2 ∂(ν : Measure V)) -
        ∫ x, (fun _ : V => (0 : ℝ)) x *
          (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f x) ^ 2 ∂(ν : Measure V) :=
  ⟨by simp, two_mul_integral_mul_weakGamma_le m hν hi hνU hU hconv f contDiff_const
    HasCompactSupport.zero (fun _ => le_rfl) ht⟩

/-- **`L¹` self-improvement, form-domain data.** -/
theorem self_improvement (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, φ x * ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
            Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) ≤
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
        ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
          Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) :=
  integral_mul_norm_le m hν hi hνU hU hconv f hφ hφc hφ0 ht

/-- **`L¹` self-improvement, heat data** `f = P_ε g` for arbitrary `g ∈ L²`, `ε > 0`. -/
theorem self_improvement_heat_data (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (g : Lp ℝ 2 (ν : Measure V))
    {ε : ℝ} (hε : 0 < ε)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, φ x * ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi
            ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hε⟩
            ht⟩ : Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) ≤
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
        ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hε⟩ :
            Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) :=
  integral_mul_norm_le m hν hi hνU hU hconv _ hφ hφc hφ0 ht

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- **The pointwise inputs**: improved Bochner and the regularized self-improvement inequality,
for any `C²` convex potential and `C³` function. -/
theorem pointwise_inputs {W f : V → ℝ} (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W)
    (hf : ContDiff ℝ 3 f) {ε : ℝ} (hε : 0 < ε) (x : V) :
    ‖gradient (fun y => ‖gradient f y‖ ^ 2) x‖ ^ 2 ≤ 4 * ‖gradient f x‖ ^ 2 * gammaTwo W f x ∧
      0 ≤ weightedLaplacian W (fun y => √(ε + gamma f f y) - √ε) x -
        gamma f (weightedLaplacian W f) x / √(ε + gamma f f x) :=
  ⟨norm_gradient_norm_gradient_sq_le hW hconv hf x,
    weightedLaplacian_sqrt_sub_div_nonneg hW hconv hf hε x⟩

#print axioms reverse_poincare
#print axioms bounded_data
#print axioms reverse_zero_test
#print axioms self_improvement
#print axioms self_improvement_heat_data
#print axioms pointwise_inputs
#print axioms FunctionalInequalities.Analysis.BakryEmery.laplacian_comp
#print axioms FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_comp
#print axioms FunctionalInequalities.Analysis.BakryEmery.norm_gradient_norm_gradient_sq_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_sqrt_sub_div_nonneg
#print axioms FunctionalInequalities.Analysis.BakryEmery.abs_regularizedNorm_sub_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.norm_regularizedUnit_sub_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.abs_regularizedNorm_sub_sub_inner_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.tendsto_regularizedNorm
#print axioms FunctionalInequalities.Analysis.BakryEmery.tendsto_integral_mul_regularizedNorm
#print axioms FunctionalInequalities.Analysis.BakryEmery.tendsto_integral_mul_inner_regularizedUnit
#print axioms FunctionalInequalities.Analysis.BakryEmery.hasDerivWithinAt_integral_mul_regularizedNorm
#print axioms FunctionalInequalities.Analysis.BakryEmery.tendsto_integral_mul_regularizedNorm_zero
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply_of_pos
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_adjointComp_mul_apply_sub_eq
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.two_mul_integral_mul_weakGamma_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.two_mul_integral_mul_weakGamma_le_of_bounded
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_regularizedNorm_smooth_nonneg
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_regularizedNorm_nonneg
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_mul_regularizedNorm_le_of_pos
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_mul_regularizedNorm_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_mul_norm_le
end BakryEmeryReverseSelfImprovementAudit

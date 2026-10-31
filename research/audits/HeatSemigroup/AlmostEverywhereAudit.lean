module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate.ReversePoincare
public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate.SelfImprovement

/-! Independent clients of a.e. heat estimates. No test-positivity, approximation sequence,
operator-core or regularity assumptions are supplied by these clients. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup
  FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
  FunctionalInequalities.Energy.WeightedGradient
open scoped ContDiff
namespace HeatAlmostEverywhereAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

theorem bounded_gradient (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {M : ℝ} (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ M) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
          Lp V 2 (ν : Measure V)) x‖ ≤ M / Real.sqrt (2 * t) :=
  ae_norm_gradient_le_of_bounded m hν hi hνU hU hconv f hf ht

theorem self_improvement
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
            Lp V 2 (ν : Measure V)) x‖ ≤
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht
        (((Lp.memLp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)).norm).toLp
          (fun y => ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
            Lp V 2 (ν : Measure V)) y‖)) x :=
  ae_norm_gradient_le m hν hi hνU hU hconv f ht

theorem gradient_mass
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
          Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) ≤
      ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) :=
  integral_norm_gradient_le m hν hi hνU hU hconv f ht

theorem time_zero
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f (t := 0) le_rfl⟩ :
            Lp V 2 (ν : Measure V)) x‖ ≤
      operator m (ContinuousLinearMap.id ℝ V) hν hi (t := 0) le_rfl
        (((Lp.memLp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)).norm).toLp
          (fun y => ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
            Lp V 2 (ν : Measure V)) y‖)) x :=
  ae_norm_gradient_le m hν hi hνU hU hconv f (t := 0) le_rfl

end HeatAlmostEverywhereAudit

namespace SmoothTestOrderAudit
open FunctionalInequalities.Analysis.TestFunction

/-- Atoms and zero-dimensional spaces are allowed by the order-separation lemma. -/
theorem zero_dimension (f : EuclideanSpace ℝ (Fin 0) → ℝ)
    (hf : Integrable f (Measure.dirac 0))
    (h : ∀ φ : EuclideanSpace ℝ (Fin 0) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x, φ x * f x ∂Measure.dirac 0) :
    0 ≤ f 0 := by
  have hh := ae_nonneg_of_integral_mul_nonneg hf h
  simpa using hh

/-- The generic comparison supports arbitrary finite Borel measures, including the zero measure. -/
theorem zero_measure (f g : ℝ → ℝ) : ∀ᵐ x ∂(0 : Measure ℝ), f x ≤ g x := by
  apply ae_le_of_integral_mul_le (by simp) (by simp)
  intro φ _ _ _
  simp

end SmoothTestOrderAudit

#print axioms FunctionalInequalities.Analysis.TestFunction.ae_nonneg_of_integral_mul_nonneg
#print axioms FunctionalInequalities.Analysis.TestFunction.ae_le_of_integral_mul_le
#print axioms HeatAlmostEverywhereAudit.bounded_gradient
#print axioms HeatAlmostEverywhereAudit.self_improvement
#print axioms HeatAlmostEverywhereAudit.gradient_mass
#print axioms HeatAlmostEverywhereAudit.time_zero
#print axioms SmoothTestOrderAudit.zero_dimension
#print axioms SmoothTestOrderAudit.zero_measure

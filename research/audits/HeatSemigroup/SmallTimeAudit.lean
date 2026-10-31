module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SmallTime.Perimeter

/-! Independent small-time heat clients, retaining the potential, time and perimeter scope. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup
  FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
  FunctionalInequalities.Energy.WeightedGradient
open scoped ContDiff
namespace HeatSmallTimeAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

theorem form_domain (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |(f : Lp ℝ 2 (ν : Measure V)) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      Real.sqrt (2 * t) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) :=
  integral_abs_sub_operator_le m hν hi hνU hU hconv f ht

theorem l1_contraction (f g : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht g x| ∂(ν : Measure V)) ≤
      ∫ x, |f x - g x| ∂(ν : Measure V) :=
  integral_abs_operator_sub_le m hν hi f g ht

theorem finite_perimeter
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) (D : SmoothDomain V)
    (hP : relativePerimeter ρ (interior (ν : Measure V).support) D ≠ ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |D.carrier.indicator (1 : V → ℝ) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht
        (indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ)) x|
      ∂(ν : Measure V)) ≤
      Real.sqrt (2 * t) * (relativePerimeter ρ (interior (ν : Measure V).support) D).toReal :=
  integral_abs_indicator_sub_operator_le m hν hi hνU hU hconv hρ D hP ht

theorem extended_perimeter (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    (D : SmoothDomain V) {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ x,
        ‖D.carrier.indicator (1 : V → ℝ) x -
            operator m (ContinuousLinearMap.id ℝ V) hν hi ht
              (indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ))
              x‖ₑ ∂(ν : Measure V)) ≤
      ENNReal.ofReal (Real.sqrt (2 * t)) *
        relativePerimeter ρ (interior (ν : Measure V).support) D :=
  lintegral_enorm_indicator_sub_operator_le m hν hi hνU hU hconv hρ D ht

theorem zero_time (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    (D : SmoothDomain V) :
    (∫⁻ x,
        ‖D.carrier.indicator (1 : V → ℝ) x -
            operator m (ContinuousLinearMap.id ℝ V) hν hi (t := 0) le_rfl
              (indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ))
              x‖ₑ ∂(ν : Measure V)) ≤
      ENNReal.ofReal (Real.sqrt (2 * 0)) *
        relativePerimeter ρ (interior (ν : Measure V).support) D :=
  lintegral_enorm_indicator_sub_operator_le m hν hi hνU hU hconv hρ D (t := 0) le_rfl

/-- The form-domain estimate applies after any positive heat time to arbitrary L2 data. -/
theorem heat_initial_data (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    (g : Lp ℝ 2 (ν : Measure V)) {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    let f := operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le g
    (∫ x, |f x - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      Real.sqrt (2 * t) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨f, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩ :
          Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) :=
  integral_abs_sub_operator_le m hν hi hνU hU hconv
    ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩ ht

end HeatSmallTimeAudit

#print axioms FunctionalInequalities.L2.exists_bounded_inner_eq_integral_abs
#print axioms FunctionalInequalities.L2.inner_le_mul_integral_abs
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.inner_sub_operator_le
#print axioms
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_abs_sub_operator_le_of_recovery
#print axioms HeatSmallTimeAudit.form_domain
#print axioms HeatSmallTimeAudit.l1_contraction
#print axioms HeatSmallTimeAudit.finite_perimeter
#print axioms HeatSmallTimeAudit.extended_perimeter
#print axioms HeatSmallTimeAudit.zero_time
#print axioms HeatSmallTimeAudit.heat_initial_data

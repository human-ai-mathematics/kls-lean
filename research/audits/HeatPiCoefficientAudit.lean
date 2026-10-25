import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Perimeter

/-! Independent full-signature clients for pi-coefficient gradient, L1 and perimeter bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line.GaussianProfile
open scoped ContDiff RealInnerProductSpace NNReal
open InnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
namespace HeatPiCoefficientAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
theorem unit_gradient (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
          Lp V 2 (ν : Measure V)) x‖ ≤ 1 / (2 * Real.sqrt (Real.pi * t)) :=
  ae_norm_gradient_le_of_unitInterval m hν hi hνU hU hconv f hf ht

theorem bounded_gradient (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {M : ℝ} (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ M) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
          Lp V 2 (ν : Measure V)) x‖ ≤ M / Real.sqrt (Real.pi * t) :=
  ae_norm_gradient_le_of_bounded_pi m hν hi hνU hU hconv f hf ht

theorem dual (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (g : Lp ℝ 2 (ν : Measure V)) (hg : ∀ᵐ x ∂(ν : Measure V), |g x| ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    ⟪(f : Lp ℝ 2 (ν : Measure V)) - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f, g⟫ ≤
      (2 * Real.sqrt (t / Real.pi)) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) :=
  inner_sub_operator_le_pi m hν hi hνU hU hconv f g hg ht

theorem form (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |(f : Lp ℝ 2 (ν : Measure V)) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      (2 * Real.sqrt (t / Real.pi)) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) :=
  integral_abs_sub_operator_le_pi m hν hi hνU hU hconv f ht

theorem approximation
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) (f : Lp ℝ 2 (ν : Measure V))
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |f x - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      2 * (∫ x, |f x - (u : Lp ℝ 2 (ν : Measure V)) x| ∂(ν : Measure V)) +
      (2 * Real.sqrt (t / Real.pi)) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) :=
  integral_abs_sub_operator_le_of_form_approximation_pi m hν hi hνU hU hconv f u ht

theorem recovery
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) (f : Lp ℝ 2 (ν : Measure V)) {C : ℝ}
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ u :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      (∫ x, |f x - (u : Lp ℝ 2 (ν : Measure V)) x| ∂(ν : Measure V)) < ε ∧
      (∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V)) ≤ C + ε)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |f x - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      (2 * Real.sqrt (t / Real.pi)) * C :=
  integral_abs_sub_operator_le_of_recovery_pi m hν hi hνU hU hconv f hrec ht

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
      (2 * Real.sqrt (t / Real.pi)) * (relativePerimeter ρ (interior (ν : Measure V).support) D).toReal :=
  integral_abs_indicator_sub_operator_le_pi m hν hi hνU hU hconv hρ D hP ht

theorem extended_perimeter
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) (D : SmoothDomain V)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ x, ‖D.carrier.indicator (1 : V → ℝ) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht
        (indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ)) x‖ₑ
      ∂(ν : Measure V)) ≤
      ENNReal.ofReal ((2 * Real.sqrt (t / Real.pi))) * relativePerimeter ρ (interior (ν : Measure V).support) D :=
  lintegral_enorm_indicator_sub_operator_le_pi m hν hi hνU hU hconv hρ D ht

end HeatPiCoefficientAudit

#print axioms HeatPiCoefficientAudit.unit_gradient
#print axioms HeatPiCoefficientAudit.bounded_gradient
#print axioms HeatPiCoefficientAudit.dual
#print axioms HeatPiCoefficientAudit.form
#print axioms HeatPiCoefficientAudit.approximation
#print axioms HeatPiCoefficientAudit.recovery
#print axioms HeatPiCoefficientAudit.finite_perimeter
#print axioms HeatPiCoefficientAudit.extended_perimeter

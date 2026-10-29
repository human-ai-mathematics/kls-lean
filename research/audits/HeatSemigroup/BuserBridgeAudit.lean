import FunctionalInequalities.KLS.LogConcave.SmoothBuser

/-! Independent full-signature clients for the literature form gap, actual heat indicator
correlation, and the pi comparison in the smooth convex tilted model. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set InnerProductSpace
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Energy
open scoped ContDiff

namespace HeatBuserBridgeAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

theorem form_optimum :
    Poincare.L2Energy.constant ν
      (PreEnergy.normSqEnergy
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) =
      Poincare.LocalSlope.Intrinsic.constant ν :=
  hν.closedWeightedOperator_id_constant_eq_literature m hi

theorem form_gap (C : NNReal)
    (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
      (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 :=
  hν.closedWeightedOperator_id_gap_of_literature_le m hi C hC u

theorem heat_decay (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 ≤ t) :
    ‖L2.center ν (operator m (ContinuousLinearMap.id ℝ V) hν hi ht f)‖ ^ 2 ≤
      Real.exp (-2 * t / (C : ℝ)) * ‖L2.center ν f‖ ^ 2 :=
  norm_center_operator_sq_le_exp_of_literature_le m hν hi C hC hLit f ht

theorem indicator_displacement (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    {D : Set V} (hD : MeasurableSet D) {t : ℝ} (ht : 0 ≤ t) :
    2 * (1 - Real.exp (-t / (C : ℝ))) *
      ((ν : Measure V).real D * (1 - (ν : Measure V).real D)) ≤
      ∫ x, |D.indicator (1 : V → ℝ) x -
        operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          (indicatorConstLp 2 hD (measure_ne_top _ _) (1 : ℝ)) x| ∂(ν : Measure V) :=
  two_mul_variance_decay_le_integral_abs_indicator_sub_operator m hν hi C hC hLit hD ht

theorem scalar_pi :
    2 * Real.sqrt (5 / 4 : ℝ) ≤ Real.pi * (1 - Real.exp (-(5 / 4 : ℝ))) :=
  pi_heat_scalar

include hν hi in
theorem smooth_mass_perimeter {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    (D : SmoothDomain V)
    (hP : relativePerimeter ρ (interior (ν : Measure V).support) D ≠ ⊤) :
    min ((ν : Measure V).real D.carrier) (1 - (ν : Measure V).real D.carrier) ≤
      Real.sqrt (Real.pi * (C : ℝ)) *
        (relativePerimeter ρ (interior (ν : Measure V).support) D).toReal :=
  min_mass_le_sqrt_pi_mul_perimeter m hν hi hνU hU hconv C hC hLit hρ D hP

include hν hi in
theorem smooth_cheeger {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    (Isoperimetry.smoothConstant ρ (interior (ν : Measure V).support) ν)⁻¹ ^ 2 ≤
      ENNReal.ofReal (Real.pi * (C : ℝ)) :=
  inv_smoothConstant_sq_le_pi_mul m hν hi hνU hU hconv C hC hLit hρ

include hν hi in
theorem smooth_minkowski {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    (Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2 ≤
      ENNReal.ofReal (Real.pi * (C : ℝ)) :=
  inv_minkowskiConstant_sq_le_pi_mul m hν hi hνU hU hconv C hC hLit hρ

include hν hi in
theorem smooth_minkowski_optimal {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    (Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant ν :=
  inv_minkowskiConstant_sq_le_pi_literature m hν hi hνU hU hconv hρ

theorem affine_smooth_minkowski_optimal {μ : ProbabilityMeasure V}
    (hμ : LogConcave μ)
    {U : (Probability.affineSupport μ).direction → ℝ}
    (hμU : (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) =
      (volume : Measure (Probability.affineSupport μ).direction).tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U) :
    Isoperimetry.inverseScale μ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ :=
  hμ.inverseScale_sq_le_pi_literature_of_intrinsic_smooth_tilt hμU hU hconv

omit [CompleteSpace V] in
theorem affine_zero_dimensional {μ : ProbabilityMeasure V}
    (hdim : Module.finrank ℝ (Probability.affineSupport μ).direction = 0) :
    Isoperimetry.inverseScale μ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ :=
  inverseScale_sq_le_pi_literature_of_finrank_eq_zero hdim

end HeatBuserBridgeAudit

#print axioms HeatBuserBridgeAudit.form_optimum
#print axioms HeatBuserBridgeAudit.form_gap
#print axioms HeatBuserBridgeAudit.heat_decay
#print axioms HeatBuserBridgeAudit.indicator_displacement
#print axioms HeatBuserBridgeAudit.scalar_pi
#print axioms HeatBuserBridgeAudit.smooth_mass_perimeter
#print axioms HeatBuserBridgeAudit.smooth_cheeger
#print axioms HeatBuserBridgeAudit.smooth_minkowski
#print axioms HeatBuserBridgeAudit.smooth_minkowski_optimal
#print axioms HeatBuserBridgeAudit.affine_smooth_minkowski_optimal
#print axioms HeatBuserBridgeAudit.affine_zero_dimensional

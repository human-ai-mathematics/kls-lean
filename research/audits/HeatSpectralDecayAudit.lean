import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Decay

/-! Independent full-signature clients for the actual heat orbit, the explicit form-domain gap,
and the half-time indicator correlation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace

namespace HeatSpectralDecayAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

theorem constant {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    operator m B hν hi ht (L2.const ν c) = L2.const ν c :=
  const_fixed m B hν hi ht c

theorem centering {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (ν : Measure V)) :
    L2.center ν (operator m B hν hi ht f) =
      operator m B hν hi ht (L2.center ν f) :=
  center_operator m B hν hi ht f

theorem positive_domain (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    operator m B hν hi ht.le f ∈
      (adjointComp (hν.closedWeightedOperator m B hi)).domain :=
  mem_adjointComp_domain_of_pos m B hν hi f ht

theorem energy_derivative (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ‖Generated.apply (hν.closedWeightedOperator m B hi)
      (hν.closedWeightedOperator_isClosed m B hi)
      (hν.dense_domain_closedWeightedOperator m B hi) s f‖ ^ 2)
      (-2 * ‖hν.closedWeightedOperator m B hi
        ⟨Generated.apply (hν.closedWeightedOperator m B hi)
          (hν.closedWeightedOperator_isClosed m B hi)
          (hν.dense_domain_closedWeightedOperator m B hi) t f,
          (Generated.mem_adjointComp_domain_apply_of_pos
            (hν.closedWeightedOperator m B hi)
            (hν.closedWeightedOperator_isClosed m B hi)
            (hν.dense_domain_closedWeightedOperator m B hi) f ht).2⟩‖ ^ 2) t :=
  hasDerivAt_norm_sq_of_pos m B hν hi f ht

theorem decay (C : ℝ) (hC : 0 < C)
    (hgap : ∀ u : (hν.closedWeightedOperator m B hi).domain,
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
        C * ‖hν.closedWeightedOperator m B hi u‖ ^ 2)
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 ≤ t) :
    ‖L2.center ν (operator m B hν hi ht f)‖ ^ 2 ≤
      Real.exp (-2 * t / C) * ‖L2.center ν f‖ ^ 2 :=
  norm_center_operator_sq_le_exp m B hν hi C hC hgap f ht

theorem correlation (C : ℝ) (hC : 0 < C)
    (hgap : ∀ u : (hν.closedWeightedOperator m B hi).domain,
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
        C * ‖hν.closedWeightedOperator m B hi u‖ ^ 2)
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 ≤ t) :
    inner ℝ (L2.center ν f) (operator m B hν hi ht (L2.center ν f)) ≤
      Real.exp (-t / C) * ‖L2.center ν f‖ ^ 2 :=
  inner_center_operator_le_exp m B hν hi C hC hgap f ht

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
theorem indicator_variance {D : Set V} (hD : MeasurableSet D) :
    ‖L2.center ν (indicatorConstLp 2 hD (measure_ne_top (ν : Measure V) D) (1 : ℝ))‖ ^ 2 =
      (ν : Measure V).real D * (1 - (ν : Measure V).real D) :=
  L2.norm_center_indicatorConstLp_sq ν hD

theorem indicator_correlation (C : ℝ) (hC : 0 < C)
    (hgap : ∀ u : (hν.closedWeightedOperator m B hi).domain,
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
        C * ‖hν.closedWeightedOperator m B hi u‖ ^ 2)
    {D : Set V} (hD : MeasurableSet D) {t : ℝ} (ht : 0 ≤ t) :
    let χ := indicatorConstLp 2 hD (measure_ne_top (ν : Measure V) D) (1 : ℝ)
    inner ℝ (L2.center ν χ) (operator m B hν hi ht (L2.center ν χ)) ≤
      Real.exp (-t / C) * (ν : Measure V).real D * (1 - (ν : Measure V).real D) :=
  inner_center_indicator_le_exp m B hν hi C hC hgap hD ht

end HeatSpectralDecayAudit

#print axioms HeatSpectralDecayAudit.constant
#print axioms HeatSpectralDecayAudit.centering
#print axioms HeatSpectralDecayAudit.positive_domain
#print axioms HeatSpectralDecayAudit.energy_derivative
#print axioms HeatSpectralDecayAudit.decay
#print axioms HeatSpectralDecayAudit.correlation
#print axioms HeatSpectralDecayAudit.indicator_variance
#print axioms HeatSpectralDecayAudit.indicator_correlation

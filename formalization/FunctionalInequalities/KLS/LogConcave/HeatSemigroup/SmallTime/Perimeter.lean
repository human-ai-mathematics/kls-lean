import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SmallTime.Approximation
import FunctionalInequalities.KLS.Geometry.Perimeter.Recovery

/-! # Small-time heat approximation of smooth domains

The existing relative-perimeter recovery sequence supplies genuine form-domain approximants.
The law still has a smooth convex tilted potential. The new coefficient is 2 sqrt(t/pi), with
a real-valued finite-perimeter theorem and an ENNReal theorem allowing infinite perimeter.
Both include t=0. No general metric-BV identification or nonsmooth-potential passage is claimed.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace
open scoped ContDiff ENNReal
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open Energy Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- Indicator initial data of a smooth domain with finite relative perimeter. The density
`ρ` is a Borell representative of the same law with respect to the canonical volume measure. -/
theorem integral_abs_indicator_sub_operator_le_pi
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) (D : SmoothDomain V)
    (hP : relativePerimeter ρ (interior (ν : Measure V).support) D ≠ ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |D.carrier.indicator (1 : V → ℝ) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht
        (indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ)) x|
      ∂(ν : Measure V)) ≤
      (2 * Real.sqrt (t / Real.pi)) * (relativePerimeter ρ (interior (ν : Measure V).support) D).toReal := by
  let f : Lp ℝ 2 (ν : Measure V) :=
    indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ)
  have hf : f =ᵐ[(ν : Measure V)] D.carrier.indicator (1 : V → ℝ) := indicatorConstLp_coeFn
  obtain ⟨u, hu, hconvL1, hcost⟩ := RelativePerimeter.exists_smooth_recovery_sequence hρ D hP
  have htest : ∀ n, IsTest ν (ContinuousLinearMap.id ℝ V) (u n) := by
    intro n
    obtain ⟨K, hK⟩ := (hu n).2.1
    refine ⟨⟨K, hK⟩, ?_, ?_⟩
    · apply MemLp.of_bound (hu n).1.continuous.aestronglyMeasurable 1
      exact ae_of_all _ fun x => by rw [Real.norm_of_nonneg ((hu n).2.2 x).1]; exact ((hu n).2.2 x).2
    · rw [WeightedGradient.apply_id]
      apply MemLp.of_bound
        (Analysis.BakryEmery.continuous_gradient ((hu n).1.of_le (by decide))).aestronglyMeasurable K
      exact ae_of_all _ (Energy.Euclidean.LipschitzApproximation.norm_gradient_le_of_lipschitz hK)
  let v : ℕ → (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := fun n =>
    ⟨(htest n).memLp.toLp (u n), hν.toLp_mem_closedWeightedOperator_domain_of_isTest m
      (ContinuousLinearMap.id ℝ V) hi (htest n)⟩
  have hv : ∀ n, (v n : Lp ℝ 2 (ν : Measure V)) =ᵐ[(ν : Measure V)] u n :=
    fun n => (htest n).memLp.coeFn_toLp
  have hTv : ∀ n, (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi (v n) :
      Lp V 2 (ν : Measure V)) =ᵐ[(ν : Measure V)] gradient (u n) := by
    intro n
    rw [show hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi (v n) =
      (htest n).memLp_apply.toLp (WeightedGradient.apply (ContinuousLinearMap.id ℝ V) (u n)) from
      hν.closedWeightedOperator_apply_toLp m (ContinuousLinearMap.id ℝ V) hi (htest n)]
    simpa only [WeightedGradient.apply_id] using (htest n).memLp_apply.coeFn_toLp
  have herr : Tendsto (fun n => ∫ x, |f x - (v n : Lp ℝ 2 (ν : Measure V)) x| ∂(ν : Measure V))
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconvL1
    simp only [ENNReal.toReal_zero] at h
    apply h.congr
    intro n
    change (∫⁻ x, ‖u n x - D.carrier.indicator (1 : V → ℝ) x‖ₑ ∂(ν : Measure V)).toReal = _
    have hem : AEStronglyMeasurable
        (fun x => u n x - D.carrier.indicator (1 : V → ℝ) x) (ν : Measure V) :=
      (hu n).1.continuous.aestronglyMeasurable.sub
        (measurable_const.indicator D.isOpen.measurableSet).aestronglyMeasurable
    rw [← integral_norm_eq_lintegral_enorm hem]
    apply integral_congr_ae
    filter_upwards [hf, hv n] with x hfx hvx
    rw [hfx, hvx, Real.norm_eq_abs, abs_sub_comm]
  have hrec : ∀ ε : ℝ, 0 < ε → ∃ w :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      (∫ x, |f x - (w : Lp ℝ 2 (ν : Measure V)) x| ∂(ν : Measure V)) < ε ∧
      (∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi w :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V)) ≤
        (relativePerimeter ρ (interior (ν : Measure V).support) D).toReal + ε := by
    intro ε hε
    have hlt : relativePerimeter ρ (interior (ν : Measure V).support) D <
        ENNReal.ofReal ((relativePerimeter ρ (interior (ν : Measure V).support) D).toReal + ε) :=
      (ENNReal.lt_ofReal_iff_toReal_lt hP).mpr (lt_add_of_pos_right _ hε)
    have hsmall := eventually_lt_of_limsup_lt (hcost.trans_lt hlt)
    obtain ⟨n, hn, hne⟩ := ((herr.eventually (gt_mem_nhds hε)).and hsmall).exists
    refine ⟨v n, hn, ?_⟩
    have hgrad : AEStronglyMeasurable (gradient (u n)) (ν : Measure V) :=
      (Analysis.BakryEmery.continuous_gradient ((hu n).1.of_le (by decide))).aestronglyMeasurable
    rw [integral_congr_ae ((hTv n).mono fun x hx => congrArg norm hx),
      integral_norm_eq_lintegral_enorm hgrad]
    exact (ENNReal.toReal_lt_of_lt_ofReal hne).le
  have h := integral_abs_sub_operator_le_of_recovery_pi m hν hi hνU hU hconv f hrec ht
  convert h using 1
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  rw [hx]

/-- The extended-nonnegative perimeter bound, including infinite perimeter and time zero. -/
theorem lintegral_enorm_indicator_sub_operator_le_pi
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) (D : SmoothDomain V)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ x, ‖D.carrier.indicator (1 : V → ℝ) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht
        (indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ)) x‖ₑ
      ∂(ν : Measure V)) ≤
      ENNReal.ofReal ((2 * Real.sqrt (t / Real.pi))) * relativePerimeter ρ (interior (ν : Measure V).support) D := by
  let f : Lp ℝ 2 (ν : Measure V) :=
    indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ)
  have hf : f =ᵐ[(ν : Measure V)] D.carrier.indicator (1 : V → ℝ) := indicatorConstLp_coeFn
  by_cases ht0 : t = 0
  · subst t
    simp only [HeatSemigroup.zero]
    have hz : (fun x => ‖D.carrier.indicator (1 : V → ℝ) x - f x‖ₑ) =ᵐ[(ν : Measure V)] 0 := by
      filter_upwards [hf] with x hx
      simp [hx]
    rw [lintegral_congr_ae hz]
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hP : relativePerimeter ρ (interior (ν : Measure V).support) D = ⊤
  · rw [hP, ENNReal.mul_top (by
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))]
    exact le_top
  have h := ENNReal.ofReal_le_ofReal
    (integral_abs_indicator_sub_operator_le_pi m hν hi hνU hU hconv hρ D hP ht)
  have hiD : Integrable (D.carrier.indicator (1 : V → ℝ)) (ν : Measure V) :=
    ((Lp.memLp f).integrable one_le_two).congr hf
  have hiP := (Lp.memLp (operator m (ContinuousLinearMap.id ℝ V) hν hi ht f)).integrable one_le_two
  have heq := ofReal_integral_norm_eq_lintegral_enorm (hiD.sub hiP)
  simp only [Pi.sub_apply, Real.norm_eq_abs] at heq
  rw [heq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hP] at h
  exact h


/-- The earlier sqrt(2t) bound follows from the pi-coefficient bound. -/
theorem integral_abs_indicator_sub_operator_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) (D : SmoothDomain V)
    (hP : relativePerimeter ρ (interior (ν : Measure V).support) D ≠ ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |D.carrier.indicator (1 : V → ℝ) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht
        (indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ)) x|
      ∂(ν : Measure V)) ≤
      Real.sqrt (2 * t) * (relativePerimeter ρ (interior (ν : Measure V).support) D).toReal := by
  exact (integral_abs_indicator_sub_operator_le_pi m hν hi hνU hU hconv hρ D hP ht).trans
    (mul_le_mul_of_nonneg_right (two_mul_sqrt_div_pi_le_sqrt_two_mul ht) ENNReal.toReal_nonneg)

/-- The earlier extended-nonnegative bound follows from the pi-coefficient bound. -/
theorem lintegral_enorm_indicator_sub_operator_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) (D : SmoothDomain V)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ x, ‖D.carrier.indicator (1 : V → ℝ) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht
        (indicatorConstLp 2 D.isOpen.measurableSet (measure_ne_top _ _) (1 : ℝ)) x‖ₑ
      ∂(ν : Measure V)) ≤
      ENNReal.ofReal (Real.sqrt (2 * t)) * relativePerimeter ρ (interior (ν : Measure V).support) D := by
  exact (lintegral_enorm_indicator_sub_operator_le_pi m hν hi hνU hU hconv hρ D ht).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (two_mul_sqrt_div_pi_le_sqrt_two_mul ht)) le_rfl)

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup

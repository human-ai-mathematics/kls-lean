import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GaussianProfile
import FunctionalInequalities.L2.Duality

/-! # Small-time L1 approximation by the heat semigroup

The bounded-data gradient estimate gives the dual estimate and then
`integral |f - P_t f| <= 2 sqrt(t/pi) integral |T f|` on the whole form domain.
The earlier sqrt(2t) statements remain available as weaker consequences.
The potential is smooth and convex and the weight is the identity.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Analysis.Semigroup
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open Energy Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem pi_coefficient_le {t : ℝ} (ht : 0 ≤ t) :
    2 * Real.sqrt (t / Real.pi) ≤ Real.sqrt (2 * t) := by
  have h := div_le_div_of_nonneg_left ht (by norm_num : (0 : ℝ) < 2) Real.two_le_pi
  have hs := Real.sq_sqrt (div_nonneg ht Real.pi_pos.le)
  have hs' := Real.sq_sqrt (show 0 ≤ 2 * t by positivity)
  nlinarith [Real.sqrt_nonneg (t / Real.pi), Real.sqrt_nonneg (2 * t)]

/-- The dual small-time bound, with bounded L2 tests and form-domain initial data. -/
theorem inner_sub_operator_le_pi (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (g : Lp ℝ 2 (ν : Measure V)) (hg : ∀ᵐ x ∂(ν : Measure V), |g x| ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    ⟪(f : Lp ℝ 2 (ν : Measure V)) - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f, g⟫ ≤
      (2 * Real.sqrt (t / Real.pi)) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  have hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let C := ∫ x, ‖(T f : Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V)
  let F : ℝ → ℝ := fun s => ⟪(f : Lp ℝ 2 (ν : Measure V)), g - Generated.apply T hT hd s g⟫
  let B : ℝ → ℝ := fun s => (2 * Real.sqrt s / Real.sqrt Real.pi) * C - F s
  have hder : ∀ s (hs : 0 < s), HasDerivAt B
      ((2 * (1 / (2 * Real.sqrt s)) / Real.sqrt Real.pi) * C -
        ⟪(f : Lp ℝ 2 (ν : Measure V)), adjointComp T
          ⟨_, Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hs⟩⟫) s := by
    intro s hs
    have hp := Generated.hasDerivAt_apply_of_pos T hT hd g hs
    have hf := (hasDerivAt_const s (f : Lp ℝ 2 (ν : Measure V))).inner ℝ
      ((hasDerivAt_const s g).sub hp)
    have hb := ((((hasDerivAt_id s).sqrt hs.ne').const_mul 2).div_const (Real.sqrt Real.pi)).mul_const C
    convert hb.sub hf using 1 <;> first | rfl | simp
  have hbound : ∀ s (hs : 0 < s),
      ⟪(f : Lp ℝ 2 (ν : Measure V)), adjointComp T
        ⟨_, Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hs⟩⟫ ≤
        (2 * (1 / (2 * Real.sqrt s)) / Real.sqrt Real.pi) * C := by
    intro s hs
    rw [real_inner_comm, inner_adjointComp_apply T hd]
    rw [L2.inner_def]
    have hgrad := ae_norm_gradient_le_of_bounded_pi m hν hi hνU hU hconv g hg hs
    have hle : (∫ x, ⟪(T ⟨_, (Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hs).2⟩ :
        Lp V 2 (ν : Measure V)) x, (T f : Lp V 2 (ν : Measure V)) x⟫ ∂(ν : Measure V)) ≤
        ∫ x, (1 / Real.sqrt (Real.pi * s)) * ‖(T f : Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) := by
      apply integral_mono_ae (L2.integrable_inner _ _)
        (((Lp.memLp (T f)).norm.integrable one_le_two).const_mul _)
      filter_upwards [hgrad] with x hx
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    rw [integral_const_mul] at hle
    convert hle using 1
    dsimp [C]
    rw [Real.sqrt_mul Real.pi_pos.le]
    field_simp
  have hc : ContinuousOn B (Ici 0) := by
    exact (((Real.continuous_sqrt.const_mul 2).div_const (Real.sqrt Real.pi)).mul
      continuous_const).continuousOn.sub
      (continuousOn_const.inner (continuousOn_const.sub (Generated.continuousOn T hT hd g)))
  have hm : MonotoneOn B (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hc
    · intro s hs
      rw [interior_Ici] at hs
      exact (hder s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hder s hs).deriv]
      exact sub_nonneg.mpr (hbound s hs)
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
  have hzero : B 0 = 0 := by simp [B, F, Generated.zero_time]
  rw [hzero] at h
  have heq : F t = ⟪(f : Lp ℝ 2 (ν : Measure V)) -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht f, g⟫ := by
    simp only [F, inner_sub_right, inner_sub_left]
    rw [symmetric m (ContinuousLinearMap.id ℝ V) hν hi ht]
    rfl
  dsimp [B] at h
  rw [heq] at h
  have hec : 2 * Real.sqrt (t / Real.pi) = 2 * Real.sqrt t / Real.sqrt Real.pi := by
    rw [Real.sqrt_div ht]
    ring
  rw [hec]
  exact sub_nonneg.mp h

/-- Small-time L1 approximation on the whole form domain, including time zero. -/
theorem integral_abs_sub_operator_le_pi (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |(f : Lp ℝ 2 (ν : Measure V)) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      (2 * Real.sqrt (t / Real.pi)) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) := by
  have h := L2.integral_abs_le_of_inner_le
    ((f : Lp ℝ 2 (ν : Measure V)) - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f)
    (fun g hg => inner_sub_operator_le_pi m hν hi hνU hU hconv f g hg ht)
  rwa [integral_congr_ae ((Lp.coeFn_sub _ _).mono fun x hx => congrArg abs hx)] at h

/-- The dual small-time bound, with bounded L2 tests and form-domain initial data. -/
theorem inner_sub_operator_le (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (g : Lp ℝ 2 (ν : Measure V)) (hg : ∀ᵐ x ∂(ν : Measure V), |g x| ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    ⟪(f : Lp ℝ 2 (ν : Measure V)) - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f, g⟫ ≤
      Real.sqrt (2 * t) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) := by
  exact (inner_sub_operator_le_pi m hν hi hνU hU hconv f g hg ht).trans
    (mul_le_mul_of_nonneg_right (pi_coefficient_le ht) (integral_nonneg fun _ ↦ norm_nonneg _))

/-- Small-time L1 approximation on the whole form domain, including time zero. -/
theorem integral_abs_sub_operator_le (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |(f : Lp ℝ 2 (ν : Measure V)) x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      Real.sqrt (2 * t) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) := by
  have h := L2.integral_abs_le_of_inner_le
    ((f : Lp ℝ 2 (ν : Measure V)) - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f)
    (fun g hg => inner_sub_operator_le m hν hi hνU hU hconv f g hg ht)
  rwa [integral_congr_ae ((Lp.coeFn_sub _ _).mono fun x hx => congrArg abs hx)] at h

/-- The existing L2 heat semigroup contracts integral absolute values. No extension of its
 domain to arbitrary L1 functions is used. -/
theorem integral_abs_operator_le (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      ∫ x, |f x| ∂(ν : Measure V) := by
  apply L2.integral_abs_le_of_inner_le
  intro g hg
  rw [symmetric m (ContinuousLinearMap.id ℝ V) hν hi ht]
  exact L2.inner_le_integral_abs f _ (ae_abs_operator_le m (ContinuousLinearMap.id ℝ V)
    hν hi ht g zero_le_one hg)

/-- L1 contraction between any two L2 initial data. -/
theorem integral_abs_operator_sub_le (f g : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x -
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht g x| ∂(ν : Measure V)) ≤
      ∫ x, |f x - g x| ∂(ν : Measure V) := by
  have h := integral_abs_operator_le m hν hi (f - g) ht
  rw [map_sub] at h
  rwa [integral_congr_ae ((Lp.coeFn_sub _ _).mono fun x hx => congrArg abs hx),
    integral_congr_ae ((Lp.coeFn_sub f g).mono fun x hx => congrArg abs hx)] at h

/-- An arbitrary L2 datum may be compared with any form-domain approximation. -/
theorem integral_abs_sub_operator_le_of_form_approximation_pi
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) (f : Lp ℝ 2 (ν : Measure V))
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |f x - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      2 * (∫ x, |f x - (u : Lp ℝ 2 (ν : Measure V)) x| ∂(ν : Measure V)) +
      (2 * Real.sqrt (t / Real.pi)) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) := by
  have h := L2.integral_abs_le_of_inner_le
    (f - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f) (C :=
      2 * (∫ x, |f x - (u : Lp ℝ 2 (ν : Measure V)) x| ∂(ν : Measure V)) +
      (2 * Real.sqrt (t / Real.pi)) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V)) (fun g hg => by
    have hPg := ae_abs_operator_le m (ContinuousLinearMap.id ℝ V) hν hi ht g zero_le_one hg
    have hb : ∀ᵐ x ∂(ν : Measure V),
        |(g - operator m (ContinuousLinearMap.id ℝ V) hν hi ht g : Lp ℝ 2 (ν : Measure V)) x| ≤ 2 := by
      filter_upwards [hg, hPg, Lp.coeFn_sub g
        (operator m (ContinuousLinearMap.id ℝ V) hν hi ht g)] with x hx hy hz
      rw [hz, Pi.sub_apply]
      have he := abs_sub_le (g x) 0 (operator m (ContinuousLinearMap.id ℝ V) hν hi ht g x)
      simp only [sub_zero, zero_sub, abs_neg] at he
      linarith
    have he := L2.inner_le_mul_integral_abs (f - (u : Lp ℝ 2 (ν : Measure V)))
      (g - operator m (ContinuousLinearMap.id ℝ V) hν hi ht g) hb
    rw [integral_congr_ae ((Lp.coeFn_sub f (u : Lp ℝ 2 (ν : Measure V))).mono
      fun x hx => congrArg abs hx)] at he
    simp only [Pi.sub_apply] at he
    have hu := inner_sub_operator_le_pi m hν hi hνU hU hconv u g hg ht
    have hsplit : ⟪f - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f, g⟫ =
        ⟪(u : Lp ℝ 2 (ν : Measure V)) - operator m (ContinuousLinearMap.id ℝ V) hν hi ht u, g⟫ +
        ⟪f - (u : Lp ℝ 2 (ν : Measure V)), g - operator m (ContinuousLinearMap.id ℝ V) hν hi ht g⟫ := by
      simp only [inner_sub_left, inner_sub_right]
      rw [symmetric m (ContinuousLinearMap.id ℝ V) hν hi ht f g,
        symmetric m (ContinuousLinearMap.id ℝ V) hν hi ht u g]
      ring
    rw [hsplit]
    linarith)
  rwa [integral_congr_ae ((Lp.coeFn_sub _ _).mono fun x hx => congrArg abs hx)] at h

/-- An arbitrary L2 datum may be compared with any form-domain approximation. -/
theorem integral_abs_sub_operator_le_of_form_approximation
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) (f : Lp ℝ 2 (ν : Measure V))
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |f x - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      2 * (∫ x, |f x - (u : Lp ℝ 2 (ν : Measure V)) x| ∂(ν : Measure V)) +
      Real.sqrt (2 * t) * ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) := by
  exact (integral_abs_sub_operator_le_of_form_approximation_pi m hν hi hνU hU hconv f u ht).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (pi_coefficient_le ht)
      (integral_nonneg fun _ ↦ norm_nonneg _)))

/-- Transfer to any L2 datum admitting arbitrarily accurate L1 form-domain approximations
with gradient mass at most `C + ε`. This is a recovery criterion, not an assertion that a
particular BV or perimeter notion admits such approximations. -/
theorem integral_abs_sub_operator_le_of_recovery_pi
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) (f : Lp ℝ 2 (ν : Measure V)) {C : ℝ}
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ u :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      (∫ x, |f x - (u : Lp ℝ 2 (ν : Measure V)) x| ∂(ν : Measure V)) < ε ∧
      (∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V)) ≤ C + ε)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |f x - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      (2 * Real.sqrt (t / Real.pi)) * C := by
  apply le_of_forall_gt
  intro b hb
  let k := (2 * Real.sqrt (t / Real.pi))
  have hk : 0 ≤ k := by positivity
  have hden : 0 < 2 + k := by positivity
  have he : 0 < (b - k * C) / (2 + k) := div_pos (sub_pos.mpr hb) hden
  obtain ⟨u, hu, hG⟩ := hrec _ he
  have h := integral_abs_sub_operator_le_of_form_approximation_pi m hν hi hνU hU hconv f u ht
  have hmul := mul_le_mul_of_nonneg_left hG hk
  have heq : (2 + k) * ((b - k * C) / (2 + k)) = b - k * C := by
    field_simp
  dsimp [k] at hu hG hmul heq ⊢
  nlinarith

/-- Transfer to any L2 datum admitting arbitrarily accurate L1 form-domain approximations
with gradient mass at most `C + ε`. This is a recovery criterion, not an assertion that a
particular BV or perimeter notion admits such approximations. -/
theorem integral_abs_sub_operator_le_of_recovery
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ univ U) (f : Lp ℝ 2 (ν : Measure V)) {C : ℝ}
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ u :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      (∫ x, |f x - (u : Lp ℝ 2 (ν : Measure V)) x| ∂(ν : Measure V)) < ε ∧
      (∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V)) ≤ C + ε)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |f x - operator m (ContinuousLinearMap.id ℝ V) hν hi ht f x| ∂(ν : Measure V)) ≤
      Real.sqrt (2 * t) * C := by
  apply le_of_forall_gt
  intro b hb
  let k := Real.sqrt (2 * t)
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hden : 0 < 2 + k := by positivity
  have he : 0 < (b - k * C) / (2 + k) := div_pos (sub_pos.mpr hb) hden
  obtain ⟨u, hu, hG⟩ := hrec _ he
  have h := integral_abs_sub_operator_le_of_form_approximation m hν hi hνU hU hconv f u ht
  have hmul := mul_le_mul_of_nonneg_left hG hk
  have heq : (2 + k) * ((b - k * C) / (2 + k)) = b - k * C := by
    field_simp
  dsimp [k] at hu hG hmul heq ⊢
  nlinarith

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup

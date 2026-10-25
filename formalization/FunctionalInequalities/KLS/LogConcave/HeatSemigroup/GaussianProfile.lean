import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SelfImprovement
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Interpolation
import FunctionalInequalities.Probability.Line.GaussianProfile
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ReversePoincare

/-!
# The shifted Gaussian profile on the generator domain

The globally smooth extension is constructed, not assumed, and then removed using
neighborhood agreement on the a.e. range of the input. The operator identity requires
a square-integrable Gamma field; for positive-time bounded heat data this premise and
range preservation are proved. Strong L2 interpolation derivatives are established
for both shifted and positive unshifted profiles, and the tested square has its exact
derivative. Weighted Cauchy-Schwarz and L1 gradient self-improvement give its interior
quantitative dissipation bound. A fixed continuous interpolation curve gives the
integrated inequality, including both time endpoints, in tested and a.e. forms.
Dominated L2 convergence and linearity remove the epsilon margin, yielding the
Gaussian BGL inequality for all unit-interval data in the smooth convex model.
Its scalar maximum and affine normalization give M/sqrt(pi*t) bounded-data
closed-gradient regularization.
-/
noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line.GaussianProfile
open scoped ContDiff
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- The actual Gaussian-profile chain identity on D(A), with explicit range and epsilon margin. -/
theorem integral_adjointComp_mul_shifted_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {ε C : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) (hC : 0 ≤ C)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hg : ∀ᵐ x ∂(ν : Measure V), (g : Lp ℝ 2 (ν : Measure V)) x ∈ Icc (0 : ℝ) (1 - 2 * ε)) :
    (∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      shifted ε ((g : Lp ℝ 2 (ν : Measure V)) x) ∂(ν : Measure V)) =
    (∫ x, -quantile ((g : Lp ℝ 2 (ν : Measure V)) x + ε) *
      WeakGamma.apply (ψ : Lp ℝ 2 (ν : Measure V))
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x
      ∂(ν : Measure V)) +
    ∫ x, ((ψ : Lp ℝ 2 (ν : Measure V)) x * (profile ((g : Lp ℝ 2 (ν : Measure V)) x + ε))⁻¹) *
      WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x
      ∂(ν : Measure V) := by
  obtain ⟨Φ, hΦ, hΦ0, heq, M, hM, hb⟩ := exists_smooth_shifted_extension hε hε'
  have h := integral_adjointComp_mul_comp_eq m hν hi hνU hU hΦ hΦ0 hM.le hC hb ψ hψb g
  have hval : ∀ᵐ x ∂(ν : Measure V), Φ ((g : Lp ℝ 2 (ν : Measure V)) x) =
      shifted ε ((g : Lp ℝ 2 (ν : Measure V)) x) ∧
      deriv Φ ((g : Lp ℝ 2 (ν : Measure V)) x) = -quantile ((g : Lp ℝ 2 (ν : Measure V)) x + ε) ∧
      deriv (deriv Φ) ((g : Lp ℝ 2 (ν : Measure V)) x) = -(profile ((g : Lp ℝ 2 (ν : Measure V)) x + ε))⁻¹ := by
    filter_upwards [hg] with x hx
    have he := heq _ hx
    exact ⟨he.eq_of_nhds, he.deriv_eq.trans (hasDerivAt_shifted (shifted_argument_mem hε hx)).deriv,
      he.deriv.deriv_eq.trans (hasDerivAt_deriv_shifted (shifted_argument_mem hε hx)).deriv⟩
  have e₁ := integral_congr_ae (hval.mono fun x hx ↦ congrArg
    (fun r ↦ (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x * r) hx.1)
  have e₂ := integral_congr_ae (hval.mono fun x hx ↦ congrArg
    (fun r ↦ r * WeakGamma.apply (ψ : Lp ℝ 2 (ν : Measure V))
      (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x) hx.2.1)
  have e₃ := integral_congr_ae (hval.mono fun x hx ↦ congrArg
    (fun r ↦ ((ψ : Lp ℝ 2 (ν : Measure V)) x * r) *
      WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x) hx.2.2)
  rw [e₁, e₂, e₃] at h
  simpa only [mul_neg, neg_mul, integral_neg, sub_neg_eq_add] using h

/-- The shifted profile belongs to the generator domain when Gamma is in L2.
The formula uses the actual Gaussian profile, with no extension left in the conclusion. -/
theorem exists_shifted_mem_domain (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hg : ∀ᵐ x ∂(ν : Measure V), (g : Lp ℝ 2 (ν : Measure V)) x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    (hΓ : MemLp (WeakGamma.apply
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)) 2 (ν : Measure V)) :
    ∃ u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      (∀ᵐ x ∂(ν : Measure V), (u : Lp ℝ 2 (ν : Measure V)) x = shifted ε ((g : Lp ℝ 2 (ν : Measure V)) x)) ∧
      (∀ᵐ x ∂(ν : Measure V),
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u) x =
        -quantile ((g : Lp ℝ 2 (ν : Measure V)) x + ε) *
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x +
        (profile ((g : Lp ℝ 2 (ν : Measure V)) x + ε))⁻¹ * WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x) := by
  obtain ⟨Φ, hΦ, hΦ0, heq, M, hM, hb⟩ := exists_smooth_shifted_extension hε hε'
  obtain ⟨u, hu, hau⟩ := exists_comp_mem_domain m hν hi hνU hU hΦ hΦ0 hM.le hb g hΓ
  refine ⟨u, ?_, ?_⟩
  · filter_upwards [hu, hg] with x hx hxg
    exact hx.trans (heq _ hxg).eq_of_nhds
  · filter_upwards [hau, hg] with x hx hxg
    have he := heq _ hxg
    have hd := he.deriv_eq.trans (hasDerivAt_shifted (shifted_argument_mem hε hxg)).deriv
    have hdd := he.deriv.deriv_eq.trans (hasDerivAt_deriv_shifted (shifted_argument_mem hε hxg)).deriv
    rw [hx, hd, hdd]
    ring

/-- On positive-time heat data in the epsilon range, the Gaussian composition is
in the generator domain. Both range preservation and Gamma integrability are proved. -/
theorem exists_shifted_operator_mem_domain (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {t : ℝ} (ht : 0 < t) :
    let g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain :=
      ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f,
        mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩
    ∃ u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      (∀ᵐ x ∂(ν : Measure V), (u : Lp ℝ 2 (ν : Measure V)) x = shifted ε ((g : Lp ℝ 2 (ν : Measure V)) x)) ∧
      (∀ᵐ x ∂(ν : Measure V),
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u) x =
        -quantile ((g : Lp ℝ 2 (ν : Measure V)) x + ε) *
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x +
        (profile ((g : Lp ℝ 2 (ν : Measure V)) x + ε))⁻¹ * WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x) := by
  dsimp only
  have hM : 0 ≤ 1 - 2 * ε := by linarith
  have hfb : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ 1 - 2 * ε :=
    hf.mono fun x hx ↦ by rw [abs_of_nonneg hx.1]; exact hx.2
  refine exists_shifted_mem_domain m hν hi hνU (hU.of_le (by decide)) hε hε'
    ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f,
      mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ ?_ ?_
  · filter_upwards [ae_nonneg_operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le
        (hf.mono fun x hx ↦ hx.1),
      ae_abs_operator_le m (ContinuousLinearMap.id ℝ V) hν hi ht.le f hM hfb] with x hx hy
    exact ⟨hx, (le_abs_self _).trans hy⟩
  · exact memLp_weakGamma_of_bounded m hν hi hνU hU hconv f hfb ht

/-- The actual shifted Gaussian profile of a positive-time heat orbit is
L2 differentiable. The curve is identified at every positive time and the derivative
by its a.e. representative. No potential or convexity assumption is added. -/
theorem exists_hasDerivAt_shifted_operator {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {t : ℝ} (ht : 0 < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let F : (adjointComp T).domain :=
      ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi) f ht⟩
    ∃ G : ℝ → Lp ℝ 2 (ν : Measure V), ∃ w : Lp ℝ 2 (ν : Measure V),
      (∀ r : ℝ, 0 < r → ∀ᵐ x ∂(ν : Measure V), G r x = shifted ε (P r f x)) ∧
      (∀ᵐ x ∂(ν : Measure V), w x = quantile (P t f x + ε) * (adjointComp T F) x) ∧
      HasDerivAt G w t := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T hT hd
  let F : (adjointComp T).domain :=
    ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f ht⟩
  obtain ⟨Φ, hΦ, hΦ0, heq, M, hM, hb⟩ := exists_smooth_shifted_extension hε hε'
  have hL : LipschitzWith ⟨M, hM.le⟩ Φ := lipschitzWith_of_nnnorm_deriv_le
    (hΦ.differentiable (by simp)) (fun x ↦ by
      change ‖deriv Φ x‖ ≤ M
      simpa only [Real.norm_eq_abs] using (hb x).2.1)
  have hdΦ := (contDiff_infty_iff_deriv.mp hΦ).2
  have hw : MemLp (fun x ↦ deriv Φ (P t f x) * (-adjointComp T F) x) 2 (ν : Measure V) :=
    L2.memLp_bddSmul (hdΦ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
      (ae_of_all _ fun x ↦ (hb _).2.1) (-adjointComp T F)
  have hfb : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ 1 - 2 * ε :=
    hf.mono fun x hx ↦ by rw [abs_of_nonneg hx.1]; exact hx.2
  have hrange (r : ℝ) (hr : 0 < r) :
      ∀ᵐ x ∂(ν : Measure V), P r f x ∈ Icc (0 : ℝ) (1 - 2 * ε) := by
    filter_upwards [ae_nonneg_operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le
        (hf.mono fun x hx ↦ hx.1),
      ae_abs_operator_le m (ContinuousLinearMap.id ℝ V) hν hi hr.le f
        (show 0 ≤ 1 - 2 * ε by linarith) hfb] with x hx hy
    exact ⟨hx, (le_abs_self _).trans hy⟩
  refine ⟨fun r ↦ hL.compLp hΦ0 (P r f), hw.toLp _, ?_, ?_, ?_⟩
  · intro r hr
    filter_upwards [hL.coeFn_compLp hΦ0 (P r f), hrange r hr] with x hx hy
    exact hx.trans (heq _ hy).eq_of_nhds
  · filter_upwards [hw.coeFn_toLp, hrange t ht, Lp.coeFn_neg (adjointComp T F)] with x hx hy hz
    rw [hx, (heq _ hy).deriv_eq, (hasDerivAt_shifted (shifted_argument_mem hε hy)).deriv, hz]
    simp only [Pi.neg_apply, neg_mul_neg]
    rfl
  · exact L2.hasDerivAt_compLp (hΦ.differentiable (by simp)) hL hΦ0
      (Generated.hasDerivAt_apply_of_pos T hT hd f ht) (hw.toLp _) hw.coeFn_toLp

set_option maxHeartbeats 800000 in
/-- Interior derivative of the actual shifted Gaussian heat interpolation.
Only a C1 potential is required; this is a tested identity, not the squared BGL bound. -/
theorem hasDerivAt_integral_operator_shifted (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {ε C : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) (hC : 0 ≤ C)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let F : (adjointComp T).domain :=
      ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f (sub_pos.mpr hst)⟩
    HasDerivAt (fun r ↦ ∫ x, P r ψ x * shifted ε (P (t - r) f x) ∂(ν : Measure V))
      (-(∫ x, (P s ψ x * (profile (P (t - s) f x + ε))⁻¹) *
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x ∂(ν : Measure V))) s := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T hT hd
  let F : (adjointComp T).domain :=
    ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f (sub_pos.mpr hst)⟩
  obtain ⟨Φ, hΦ, hΦ0, heq, M, hM, hb⟩ := exists_smooth_shifted_extension hε hε'
  have h := hasDerivAt_integral_operator_comp m hν hi hνU hU hΦ hΦ0 hM.le hC hb ψ hψb f hs hst
  have hfb : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ 1 - 2 * ε :=
    hf.mono fun x hx ↦ by rw [abs_of_nonneg hx.1]; exact hx.2
  have hrange (r : ℝ) (hr : r < t) :
      ∀ᵐ x ∂(ν : Measure V), P (t - r) f x ∈ Icc (0 : ℝ) (1 - 2 * ε) := by
    filter_upwards [ae_nonneg_operator m (ContinuousLinearMap.id ℝ V) hν hi (sub_nonneg.mpr hr.le)
        (hf.mono fun x hx ↦ hx.1),
      ae_abs_operator_le m (ContinuousLinearMap.id ℝ V) hν hi (sub_nonneg.mpr hr.le) f
        (show 0 ≤ 1 - 2 * ε by linarith) hfb] with x hx hy
    exact ⟨hx, (le_abs_self _).trans hy⟩
  have hfun : (fun r ↦ ∫ x, P r ψ x * shifted ε (P (t - r) f x) ∂(ν : Measure V)) =ᶠ[𝓝 s]
      (fun r ↦ ∫ x, P r ψ x * Φ (P (t - r) f x) ∂(ν : Measure V)) := by
    filter_upwards [Iio_mem_nhds hst] with r hr
    apply integral_congr_ae
    filter_upwards [hrange r hr] with x hx
    rw [(heq _ hx).eq_of_nhds]
  have hval : (∫ x, (P s ψ x * deriv (deriv Φ) (P (t - s) f x)) *
      WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x ∂(ν : Measure V)) =
      -(∫ x, (P s ψ x * (profile (P (t - s) f x + ε))⁻¹) *
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x ∂(ν : Measure V)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hrange s hst] with x hx
    rw [(heq _ hx).deriv.deriv_eq,
      (hasDerivAt_deriv_shifted (shifted_argument_mem hε hx)).deriv]
    ring
  exact (h.congr_of_eventuallyEq hfun).congr_deriv hval

set_option maxHeartbeats 800000 in
/-- Strong L2 derivative of the shifted Gaussian interpolation. The reciprocal-profile
Gamma field is an actual L2 class, constructed from the generator composition formula. -/
theorem exists_hasDerivAt_operator_shifted (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let F : (adjointComp T).domain :=
      ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f (sub_pos.mpr hst)⟩
    ∃ G : ℝ → Lp ℝ 2 (ν : Measure V), ∃ z : Lp ℝ 2 (ν : Measure V),
      (∀ r : ℝ, r < t → ∀ᵐ x ∂(ν : Measure V), G r x = shifted ε (P (t - r) f x)) ∧
      (∀ᵐ x ∂(ν : Measure V), z x = (profile (P (t - s) f x + ε))⁻¹ *
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x) ∧
      HasDerivAt (fun r ↦ P r (G r)) (-P s z) s := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T hT hd
  let F : (adjointComp T).domain :=
    ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f (sub_pos.mpr hst)⟩
  obtain ⟨H, w, hH, hw, hder⟩ := exists_hasDerivAt_shifted_operator m hν hi hε hε' f hf (sub_pos.mpr hst)
  obtain ⟨u, hu, hau⟩ := exists_shifted_operator_mem_domain m hν hi hνU hU hconv hε hε' f hf (sub_pos.mpr hst)
  let G (r : ℝ) := H (t - r)
  have hG : HasDerivAt G (-w) s := by
    simpa only [Function.comp_def, neg_smul, one_smul] using
      hder.scomp s (h := fun r : ℝ ↦ t - r) ((hasDerivAt_id s).const_sub t)
  have he : G s = (u : Lp ℝ 2 (ν : Measure V)) := by
    apply Lp.ext
    filter_upwards [hH (t - s) (sub_pos.mpr hst), hu] with x hx hy
    exact hx.trans hy.symm
  have hm : G s ∈ (adjointComp T).domain := he ▸ u.2
  let z := adjointComp T u + w
  have hz : ∀ᵐ x ∂(ν : Measure V), z x = (profile (P (t - s) f x + ε))⁻¹ *
      WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x := by
    filter_upwards [Lp.coeFn_add (adjointComp T u) w, hau, hw] with x hx hy hz
    change (adjointComp T u + w : Lp ℝ 2 (ν : Measure V)) x = _
    change (adjointComp T u) x = -quantile (P (t - s) f x + ε) * (adjointComp T F) x +
      (profile (P (t - s) f x + ε))⁻¹ * WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x at hy
    change w x = quantile (P (t - s) f x + ε) * (adjointComp T F) x at hz
    rw [hx, Pi.add_apply, hy, hz]
    ring
  have h := Generated.hasDerivAt_apply_curve_of_mem_domain T hT hd hG hs hm
  have hAu : adjointComp T ⟨G s, hm⟩ = adjointComp T u :=
    congrArg (adjointComp T) (Subtype.ext he)
  have hval : -w - adjointComp T ⟨G s, hm⟩ = -z := by rw [hAu]; dsimp [z]; abel
  refine ⟨G, z, fun r hr ↦ hH (t - r) (sub_pos.mpr hr), hz, ?_⟩
  rw [hval, ← neg_one_smul ℝ z, Generated.map_smul T hT hd hs.le, neg_one_smul] at h
  exact h

set_option maxHeartbeats 800000 in
/-- Adding the heat-invariant constant I(eps) gives the positive, unshifted
profile interpolation with the same strong L2 derivative. -/
theorem exists_hasDerivAt_operator_profile (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let F : (adjointComp T).domain :=
      ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f (sub_pos.mpr hst)⟩
    ∃ G : ℝ → Lp ℝ 2 (ν : Measure V), ∃ z : Lp ℝ 2 (ν : Measure V),
      (∀ r : ℝ, r < t → ∀ᵐ x ∂(ν : Measure V), G r x = profile (P (t - r) f x + ε)) ∧
      (∀ᵐ x ∂(ν : Measure V), z x = (profile (P (t - s) f x + ε))⁻¹ *
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x) ∧
      HasDerivAt (fun r ↦ P r (G r)) (-P s z) s := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T hT hd
  obtain ⟨G, z, hG, hz, hder⟩ := exists_hasDerivAt_operator_shifted m hν hi hνU hU hconv hε hε' f hf hs hst
  let c := L2.const ν (profile ε)
  have hc (r : ℝ) (hr : 0 < r) : P r c = c := by
    have he : c = profile ε • L2.const ν 1 := by
      simp only [c, ← L2.const_smul, mul_one]
    rw [he]
    exact (Generated.map_smul T hT hd hr.le (profile ε) (L2.const ν 1)).trans
      (congrArg (fun v ↦ profile ε • v) (one m (ContinuousLinearMap.id ℝ V) hν hi hr.le))
  refine ⟨fun r ↦ G r + c, z, ?_, hz, ?_⟩
  · intro r hr
    filter_upwards [Lp.coeFn_add (G r) c, hG r hr, L2.const_coeFn ν (profile ε)] with x hx hy hz
    simp only [hx, Pi.add_apply, hy, c, hz, shifted, sub_add_cancel]
  · have h := hder.add_const c
    apply h.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hs] with r hr
    exact (Generated.map_add T hT hd hr.le _ _).trans (congrArg (fun v ↦ P r (G r) + v) (hc r hr))

set_option maxHeartbeats 800000 in
/-- The exact derivative of the tested squared, positive Gaussian interpolation.
The quantitative BGL lower bound on its dissipation is a separate step. -/
theorem exists_hasDerivAt_integral_operator_profile_sq {β : V → ℝ} {C : ℝ}
    (hβ : AEStronglyMeasurable β (ν : Measure V))
    (hC : ∀ᵐ x ∂(ν : Measure V), |β x| ≤ C)
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let F : (adjointComp T).domain :=
      ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f (sub_pos.mpr hst)⟩
    ∃ G : ℝ → Lp ℝ 2 (ν : Measure V), ∃ z : Lp ℝ 2 (ν : Measure V),
      (∀ r : ℝ, r < t → ∀ᵐ x ∂(ν : Measure V), G r x = profile (P (t - r) f x + ε)) ∧
      (∀ᵐ x ∂(ν : Measure V), z x = (profile (P (t - s) f x + ε))⁻¹ *
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x) ∧
      HasDerivAt (fun r ↦ ∫ x, β x * (P r (G r) x) ^ 2 ∂(ν : Measure V))
        (-2 * ∫ x, β x * P s (G s) x * P s z x ∂(ν : Measure V)) s := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
    (hν.dense_domain_closedWeightedOperator m _ hi)
  obtain ⟨G, z, hG, hz, hder⟩ := exists_hasDerivAt_operator_profile m hν hi hνU hU hconv hε hε' f hf hs hst
  have h := L2.hasDerivAt_integral_mul_sq hβ hC hder
  refine ⟨G, z, hG, hz, h.congr_deriv ?_⟩
  have he : (∫ x, β x * P s (G s) x * (-P s z) x ∂(ν : Measure V)) =
      -(∫ x, β x * P s (G s) x * P s z x ∂(ν : Measure V)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg (P s z)] with x hx
    rw [hx, Pi.neg_apply, mul_neg]
  rw [he]
  ring

set_option maxHeartbeats 800000 in
/-- The Gaussian interpolation dissipation dominates the squared closed gradient at
its fixed terminal time. Both weights are actual L2 classes with identified representatives. -/
theorem ae_gradient_sq_le_operator_profile_mul (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let F : (adjointComp T).domain :=
      ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f (sub_pos.mpr hst)⟩
    let H : (adjointComp T).domain :=
      ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f (hs.trans hst)⟩
    ∀ a z : Lp ℝ 2 (ν : Measure V),
      (∀ᵐ x ∂(ν : Measure V), a x = profile (P (t - s) f x + ε)) →
      (∀ᵐ x ∂(ν : Measure V), z x = (profile (P (t - s) f x + ε))⁻¹ *
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x) →
      ∀ᵐ x ∂(ν : Measure V),
        WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ≤ P s a x * P s z x := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T hT hd
  let F : (adjointComp T).domain :=
    ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f (sub_pos.mpr hst)⟩
  let H : (adjointComp T).domain :=
    ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f (hs.trans hst)⟩
  intro a z ha hz
  have hrange : ∀ᵐ x ∂(ν : Measure V), P (t - s) f x ∈ Icc (0 : ℝ) (1 - 2 * ε) := by
    filter_upwards [ae_nonneg_operator m (ContinuousLinearMap.id ℝ V) hν hi
        (sub_pos.mpr hst).le (hf.mono fun x hx ↦ hx.1),
      ae_abs_operator_le m (ContinuousLinearMap.id ℝ V) hν hi (sub_pos.mpr hst).le f
        (show 0 ≤ 1 - 2 * ε by linarith)
        (hf.mono fun x hx ↦ by rw [abs_of_nonneg hx.1]; exact hx.2)] with x hx hy
    exact ⟨hx, (le_abs_self _).trans hy⟩
  have ha0 : ∀ᵐ x ∂(ν : Measure V), 0 ≤ a x :=
    ha.mono fun x hx ↦ hx ▸ profile_nonneg _
  have hz0 : ∀ᵐ x ∂(ν : Measure V), 0 ≤ z x := by
    filter_upwards [hz] with x hx
    rw [hx]
    exact mul_nonneg (inv_nonneg.mpr (profile_nonneg _)) (WeakGamma.self_nonneg _ x)
  have hac : ∀ᵐ x ∂(ν : Measure V), ‖(T ⟨_, F.2.2⟩ : Lp V 2 (ν : Measure V)) x‖ ^ 2 ≤ a x * z x := by
    filter_upwards [ha, hz, hrange] with x hx hy hr
    rw [hx, hy, WeakGamma.self_eq_norm_sq, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt (profile_pos (shifted_argument_mem hε hr))), one_mul]
  have h := ae_sq_norm_gradient_le_mul m hν hi hνU hU hconv ⟨_, F.2.2⟩ a z ha0 hz0 hac hs.le
  have he : P s (P (t - s) f) = P t f := by
    dsimp only [P]
    rw [← Generated.add_time T hT hd hs.le (sub_pos.mpr hst).le, add_sub_cancel]
  have heT : T ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi
      ⟨_, F.2.2⟩ hs.le⟩ = T ⟨_, H.2.2⟩ := congrArg T (Subtype.ext he)
  change ∀ᵐ x ∂(ν : Measure V), WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ≤ _
  change ∀ᵐ x ∂(ν : Measure V),
    ‖(T ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi
      ⟨_, F.2.2⟩ hs.le⟩ : Lp V 2 (ν : Measure V)) x‖ ^ 2 ≤ P s a x * P s z x at h
  rw [heT] at h
  simpa only [WeakGamma.self_eq_norm_sq] using h

set_option maxHeartbeats 800000 in
/-- Interior quantitative differential inequality for the bounded, nonnegative-test
Gaussian square interpolation. Time integration and endpoint limits remain separate. -/
theorem exists_hasDerivAt_integral_operator_profile_sq_le {β : V → ℝ} {C : ℝ}
    (hβ : AEStronglyMeasurable β (ν : Measure V))
    (hC : ∀ᵐ x ∂(ν : Measure V), |β x| ≤ C)
    (hβ0 : ∀ᵐ x ∂(ν : Measure V), 0 ≤ β x)
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let F : (adjointComp T).domain :=
      ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f (sub_pos.mpr hst)⟩
    let H : (adjointComp T).domain :=
      ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f (hs.trans hst)⟩
    ∃ G : ℝ → Lp ℝ 2 (ν : Measure V), ∃ z : Lp ℝ 2 (ν : Measure V),
      (∀ r : ℝ, r < t → ∀ᵐ x ∂(ν : Measure V), G r x = profile (P (t - r) f x + ε)) ∧
      (∀ᵐ x ∂(ν : Measure V), z x = (profile (P (t - s) f x + ε))⁻¹ *
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x) ∧
      HasDerivAt (fun r ↦ ∫ x, β x * (P r (G r) x) ^ 2 ∂(ν : Measure V))
        (-2 * ∫ x, β x * P s (G s) x * P s z x ∂(ν : Measure V)) s ∧
      (-2 * ∫ x, β x * P s (G s) x * P s z x ∂(ν : Measure V)) ≤
        -2 * ∫ x, β x * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ∂(ν : Measure V) := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
    (hν.dense_domain_closedWeightedOperator m _ hi)
  let H : (adjointComp T).domain :=
    ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
      (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
      f (hs.trans hst)⟩
  obtain ⟨G, z, hG, hz, hder⟩ := exists_hasDerivAt_integral_operator_profile_sq
    m hν hi hβ hC hνU hU hconv hε hε' f hf hs hst
  refine ⟨G, z, hG, hz, hder, ?_⟩
  have hpoint := ae_gradient_sq_le_operator_profile_mul m hν hi hνU hU hconv hε hε'
    f hf hs hst (G s) z (hG s hst) hz
  have hi₁ := WeakGamma.integrable_mul hβ hC (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩)
  have hi₂ : Integrable (fun x ↦ β x * P s (G s) x * P s z x) (ν : Measure V) := by
    simpa only [WeakGamma.apply, Real.inner_apply, mul_assoc] using
      WeakGamma.integrable_mul hβ hC (P s (G s)) (P s z)
  have hle := integral_mono_ae hi₁ hi₂ (by
    filter_upwards [hpoint, hβ0] with x hx hb
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hx hb)
  exact mul_le_mul_of_nonpos_left hle (by norm_num)

set_option maxHeartbeats 1200000 in
/-- Integrated Gaussian profile inequality with an explicit epsilon range margin.
Both time endpoints are included; the initial profile is constructed as an L2 class. -/
theorem exists_integral_gradient_sq_le_profile_sub {β : V → ℝ} {C : ℝ}
    (hβ : AEStronglyMeasurable β (ν : Measure V))
    (hC : ∀ᵐ x ∂(ν : Measure V), |β x| ≤ C)
    (hβ0 : ∀ᵐ x ∂(ν : Measure V), 0 ≤ β x)
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {t : ℝ} (ht : 0 < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let H : (adjointComp T).domain :=
      ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f ht⟩
    ∃ g : Lp ℝ 2 (ν : Measure V),
      (∀ᵐ x ∂(ν : Measure V), g x = profile (f x + ε)) ∧
      2 * t * (∫ x, β x * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ∂(ν : Measure V)) ≤
        (∫ x, β x * (profile (P t f x + ε)) ^ 2 ∂(ν : Measure V)) -
          ∫ x, β x * (P t g x) ^ 2 ∂(ν : Measure V) := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T hT hd
  let H : (adjointComp T).domain :=
    ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f ht⟩
  obtain ⟨Φ, hΦ, hΦ0, heq, M, hM, hb⟩ := exists_smooth_shifted_extension hε hε'
  have hL : LipschitzWith ⟨M, hM.le⟩ Φ := lipschitzWith_of_nnnorm_deriv_le
    (hΦ.differentiable (by simp)) (fun x ↦ by
      change ‖deriv Φ x‖ ≤ M
      simpa only [Real.norm_eq_abs] using (hb x).2.1)
  let G (r : ℝ) := hL.compLp hΦ0 (P (t - r) f) + L2.const ν (profile ε)
  let Y (r : ℝ) := P r (G r)
  let Q (r : ℝ) := ∫ x, β x * (Y r x) ^ 2 ∂(ν : Measure V)
  have hrange (r : ℝ) (hr : 0 ≤ r) :
      ∀ᵐ x ∂(ν : Measure V), P r f x ∈ Icc (0 : ℝ) (1 - 2 * ε) := by
    filter_upwards [ae_nonneg_operator m (ContinuousLinearMap.id ℝ V) hν hi hr
        (hf.mono fun x hx ↦ hx.1),
      ae_abs_operator_le m (ContinuousLinearMap.id ℝ V) hν hi hr f
        (show 0 ≤ 1 - 2 * ε by linarith)
        (hf.mono fun x hx ↦ by rw [abs_of_nonneg hx.1]; exact hx.2)] with x hx hy
    exact ⟨hx, (le_abs_self _).trans hy⟩
  have hG (r : ℝ) (hr : r ≤ t) :
      ∀ᵐ x ∂(ν : Measure V), G r x = profile (P (t - r) f x + ε) := by
    filter_upwards [Lp.coeFn_add (hL.compLp hΦ0 (P (t - r) f)) (L2.const ν (profile ε)),
      hL.coeFn_compLp hΦ0 (P (t - r) f), L2.const_coeFn ν (profile ε),
      hrange (t - r) (sub_nonneg.mpr hr)] with x h₁ h₂ h₃ h₄
    change (hL.compLp hΦ0 (P (t - r) f) + L2.const ν (profile ε) : Lp ℝ 2 (ν : Measure V)) x = _
    rw [h₁, Pi.add_apply, h₂, h₃, Function.comp_apply, (heq _ h₄).eq_of_nhds]
    exact sub_add_cancel _ _
  have hGc : ContinuousOn G (Icc 0 t) := by
    have hi : ContinuousOn (fun r ↦ P (t - r) f) (Icc 0 t) :=
      (Generated.continuousOn T hT hd f).comp
        (continuous_const.sub continuous_id).continuousOn (fun r hr ↦ sub_nonneg.mpr hr.2)
    exact ((hL.continuous_compLp hΦ0).comp_continuousOn hi).add continuous_const.continuousOn
  have hYc : ContinuousOn Y (Icc 0 t) :=
    Generated.continuousOn_apply_curve T hT hd (fun _ hr ↦ hr.1) hGc
  have hQc : ContinuousOn Q (Icc 0 t) :=
    (L2.continuous_integral_mul_sq hβ hC).comp_continuousOn hYc
  have hder (s : ℝ) (hs : s ∈ Ioo 0 t) :
      ∃ d : ℝ, HasDerivAt Q d s ∧ d ≤
        -2 * ∫ x, β x * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ∂(ν : Measure V) := by
    obtain ⟨G', z, hG', hz, hd', hbound⟩ := exists_hasDerivAt_integral_operator_profile_sq_le
      m hν hi hβ hC hβ0 hνU hU hconv hε hε' f hf hs.1 hs.2
    refine ⟨_, hd'.congr_of_eventuallyEq ?_, hbound⟩
    filter_upwards [gt_mem_nhds hs.2] with r hr
    have he : G r = G' r := by
      apply Lp.ext
      filter_upwards [hG r hr.le, hG' r hr] with x hx hy
      exact hx.trans hy.symm
    change (∫ x, β x * (P r (G r) x) ^ 2 ∂(ν : Measure V)) = _
    rw [he]
  have hdiff : DifferentiableOn ℝ Q (interior (Icc 0 t)) := by
    rw [interior_Icc]
    intro s hs
    exact (hder s hs).choose_spec.1.differentiableAt.differentiableWithinAt
  have hbound : ∀ s ∈ interior (Icc 0 t), deriv Q s ≤
      -2 * ∫ x, β x * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ∂(ν : Measure V) := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨d, hd, hb⟩ := hder s hs
    rwa [hd.deriv]
  have hi := (convex_Icc (0 : ℝ) t).image_sub_le_mul_sub_of_deriv_le hQc hdiff hbound
    0 ⟨le_rfl, ht.le⟩ t ⟨ht.le, le_rfl⟩ ht.le
  have hzero : Q 0 = ∫ x, β x * (profile (P t f x + ε)) ^ 2 ∂(ν : Measure V) := by
    change (∫ x, β x * (P 0 (G 0) x) ^ 2 ∂(ν : Measure V)) = _
    simp only [P, Generated.zero_time]
    apply integral_congr_ae
    filter_upwards [hG 0 ht.le] with x hx
    simpa only [sub_zero] using congrArg (fun y : ℝ ↦ β x * y ^ 2) hx
  refine ⟨G t, ?_, ?_⟩
  · simpa only [sub_self, P, Generated.zero_time] using hG t le_rfl
  · change 2 * t * _ ≤ _ - Q t
    rw [hzero] at hi
    linarith

set_option maxHeartbeats 1200000 in
/-- The regularized integrated Gaussian inequality holds almost everywhere, with
both profile endpoints and the nonnegative terminal heat-profile square retained. -/
theorem exists_ae_gradient_sq_le_profile_sub
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) (1 - 2 * ε))
    {t : ℝ} (ht : 0 < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let H : (adjointComp T).domain :=
      ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f ht⟩
    ∃ g : Lp ℝ 2 (ν : Measure V),
      (∀ᵐ x ∂(ν : Measure V), g x = profile (f x + ε)) ∧
      ∀ᵐ x ∂(ν : Measure V),
        2 * t * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ≤
          (profile (P t f x + ε)) ^ 2 - (P t g x) ^ 2 := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
    (hν.dense_domain_closedWeightedOperator m _ hi)
  let H : (adjointComp T).domain :=
    ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
      (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi) f ht⟩
  obtain ⟨g, hg, -⟩ := exists_integral_gradient_sq_le_profile_sub m hν hi
    (β := fun _ ↦ 1) aestronglyMeasurable_const (C := 1)
    (ae_of_all _ fun _ ↦ by norm_num) (ae_of_all _ fun _ ↦ zero_le_one)
    hνU hU hconv hε hε' f hf ht
  obtain ⟨u, hu, -⟩ := exists_shifted_operator_mem_domain m hν hi hνU hU hconv hε hε' f hf ht
  let a : Lp ℝ 2 (ν : Measure V) := u + L2.const ν (profile ε)
  have ha : ∀ᵐ x ∂(ν : Measure V), a x = profile (P t f x + ε) := by
    filter_upwards [hu, Lp.coeFn_add (u : Lp ℝ 2 (ν : Measure V)) (L2.const ν (profile ε)),
      L2.const_coeFn ν (profile ε)] with x hx hy hz
    change (u + L2.const ν (profile ε) : Lp ℝ 2 (ν : Measure V)) x = _
    rw [hy, Pi.add_apply, hx, hz]
    exact sub_add_cancel _ _
  have hi₁ : Integrable (fun x ↦ (profile (P t f x + ε)) ^ 2) (ν : Measure V) := by
    apply (Lp.memLp a).integrable_sq.congr
    exact ha.mono fun x hx ↦ congrArg (fun y : ℝ ↦ y ^ 2) hx
  have hi₂ := (Lp.memLp (P t g)).integrable_sq
  refine ⟨g, hg, ?_⟩
  apply Analysis.TestFunction.ae_le_of_integral_mul_le
    ((WeakGamma.integrable (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩)).const_mul (2 * t)) (hi₁.sub hi₂)
  intro β hβ hβc hβ0
  obtain ⟨C, hC⟩ := hβc.exists_bound_of_continuous hβ.continuous
  have hb : ∀ᵐ x ∂(ν : Measure V), |β x| ≤ C :=
    ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hC x
  obtain ⟨g', hg', hbound⟩ := exists_integral_gradient_sq_le_profile_sub m hν hi
    hβ.continuous.aestronglyMeasurable hb (ae_of_all _ hβ0) hνU hU hconv hε hε' f hf ht
  have he : g' = g := by
    apply Lp.ext
    filter_upwards [hg', hg] with x hx hy
    exact hx.trans hy.symm
  rw [he] at hbound
  have hb₁ := hi₁.bdd_mul hβ.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have hb₂ := hi₂.bdd_mul hβ.continuous.aestronglyMeasurable (ae_of_all _ hC)
  calc (∫ x, β x * (2 * t * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x) ∂(ν : Measure V)) =
      2 * t * ∫ x, β x * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ∂(ν : Measure V) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun _ ↦ by ring
    _ ≤ _ := hbound
    _ = ∫ x, β x * ((profile (P t f x + ε)) ^ 2 - (P t g x) ^ 2) ∂(ν : Measure V) := by
      rw [← integral_sub hb₁ hb₂]
      apply integral_congr_ae
      exact ae_of_all _ fun _ ↦ by ring

section ProfileComposition
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

private theorem memLp_profile_affine (f : Lp ℝ 2 (ν : Measure V)) (ε : ℝ) :
    MemLp (fun x ↦ profile ((1 - 2 * ε) * f x + ε)) 2 (ν : Measure V) := by
  apply MemLp.of_bound
    (continuous_profile.comp_aestronglyMeasurable
      (((Lp.aestronglyMeasurable f).const_mul (1 - 2 * ε)).add_const ε))
    (Real.sqrt (2 * Real.pi))⁻¹
  exact ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg _)]; exact profile_le _

private def profileAffine (f : Lp ℝ 2 (ν : Measure V)) (ε : ℝ) : Lp ℝ 2 (ν : Measure V) :=
  (memLp_profile_affine f ε).toLp _

private theorem profileAffine_rep (f : Lp ℝ 2 (ν : Measure V)) (ε : ℝ) :
    ∀ᵐ x ∂(ν : Measure V), profileAffine f ε x = profile ((1 - 2 * ε) * f x + ε) :=
  (memLp_profile_affine f ε).coeFn_toLp

private theorem tendsto_profileAffine (f : Lp ℝ 2 (ν : Measure V)) :
    Tendsto (profileAffine f) (𝓝 0) (𝓝 (profileAffine f 0)) := by
  apply L2.tendsto_toLp_of_dominated (fun ε ↦ memLp_profile_affine f ε)
    (memLp_profile_affine f 0) (memLp_const (p := 2) ((Real.sqrt (2 * Real.pi))⁻¹))
  · exact Eventually.of_forall fun ε ↦ ae_of_all _ fun x ↦ by
      rw [abs_of_nonneg (profile_nonneg _)]; exact profile_le _
  · exact ae_of_all _ fun x ↦ by rw [abs_of_nonneg (profile_nonneg _)]; exact profile_le _
  · exact ae_of_all _ fun x ↦ (continuous_profile.continuousAt.tendsto.comp
      (by
        exact (by fun_prop : Continuous (fun ε : ℝ ↦ (1 - 2 * ε) * f x + ε)).tendsto 0))

end ProfileComposition

set_option maxHeartbeats 1600000 in
/-- Gaussian BGL inequality tested against bounded nonnegative functions, for all
unit-interval L2 data. The epsilon range margin has been removed by L2 convergence. -/
theorem exists_integral_gradient_sq_le_profile {β : V → ℝ} {C : ℝ}
    (hβ : AEStronglyMeasurable β (ν : Measure V))
    (hC : ∀ᵐ x ∂(ν : Measure V), |β x| ≤ C)
    (hβ0 : ∀ᵐ x ∂(ν : Measure V), 0 ≤ β x)
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let H : (adjointComp T).domain :=
      ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi) f ht⟩
    ∃ g : Lp ℝ 2 (ν : Measure V),
      (∀ᵐ x ∂(ν : Measure V), g x = profile (f x)) ∧
      2 * t * (∫ x, β x * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ∂(ν : Measure V)) ≤
        (∫ x, β x * (profile (P t f x)) ^ 2 ∂(ν : Measure V)) -
          ∫ x, β x * (P t g x) ^ 2 ∂(ν : Measure V) := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T hT hd
  let H : (adjointComp T).domain :=
    ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f ht⟩
  let E := ∫ x, β x * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ∂(ν : Measure V)
  let Q (u : Lp ℝ 2 (ν : Measure V)) := ∫ x, β x * (u x) ^ 2 ∂(ν : Measure V)
  have hlim₁ : Tendsto (fun ε : ℝ ↦ (1 - 2 * ε) ^ 2 * (2 * t * E)) (𝓝 0) (𝓝 (2 * t * E)) := by
    simpa using (by fun_prop : Continuous (fun ε : ℝ ↦ (1 - 2 * ε) ^ 2 * (2 * t * E))).tendsto 0
  have hlim₂ : Tendsto (fun ε ↦ Q (profileAffine (P t f) ε) - Q (P t (profileAffine f ε)))
      (𝓝 0) (𝓝 (Q (profileAffine (P t f) 0) - Q (P t (profileAffine f 0)))) :=
    ((L2.continuous_integral_mul_sq hβ hC).continuousAt.tendsto.comp (tendsto_profileAffine (P t f))).sub
      ((L2.continuous_integral_mul_sq hβ hC).continuousAt.tendsto.comp
        ((operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le).continuous.continuousAt.tendsto.comp
          (tendsto_profileAffine f)))
  have hb (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
      (1 - 2 * ε) ^ 2 * (2 * t * E) ≤ Q (profileAffine (P t f) ε) - Q (P t (profileAffine f ε)) := by
    let c := 1 - 2 * ε
    let fε := c • f
    have hc : 0 ≤ c := by dsimp [c]; linarith
    have hfε : ∀ᵐ x ∂(ν : Measure V), fε x ∈ Icc (0 : ℝ) (1 - 2 * ε) := by
      filter_upwards [Lp.coeFn_smul c f, hf] with x hx hy
      change (c • f : Lp ℝ 2 (ν : Measure V)) x ∈ _
      rw [hx, Pi.smul_apply, smul_eq_mul]
      exact ⟨mul_nonneg hc hy.1, (mul_le_mul_of_nonneg_left hy.2 hc).trans_eq (mul_one c)⟩
    obtain ⟨g, hg, hb⟩ := exists_integral_gradient_sq_le_profile_sub
      m hν hi hβ hC hβ0 hνU hU hconv hε hε' fε hfε ht
    let Hε : (adjointComp T).domain :=
      ⟨P t fε, Generated.mem_adjointComp_domain_apply_of_pos T hT hd fε ht⟩
    have heP : P t fε = c • P t f := Generated.map_smul T hT hd ht.le c f
    have heT : T ⟨_, Hε.2.2⟩ = c • T ⟨_, H.2.2⟩ := by
      calc T ⟨_, Hε.2.2⟩ = T (c • (⟨_, H.2.2⟩ : T.domain)) := congrArg T (Subtype.ext heP)
        _ = _ := T.map_smul c _
    have heg : g = profileAffine f ε := by
      apply Lp.ext
      filter_upwards [hg, profileAffine_rep f ε, Lp.coeFn_smul c f] with x hx hy hz
      change g x = _
      change g x = profile ((c • f : Lp ℝ 2 (ν : Measure V)) x + ε) at hx
      simp only [hz, Pi.smul_apply, smul_eq_mul] at hx
      exact hx.trans hy.symm
    have heΓ : (∫ x, β x * WeakGamma.apply (T ⟨_, Hε.2.2⟩) (T ⟨_, Hε.2.2⟩) x ∂(ν : Measure V)) = c ^ 2 * E := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c (T ⟨_, H.2.2⟩)] with x hx
      rw [heT, WeakGamma.self_eq_norm_sq, WeakGamma.self_eq_norm_sq, hx,
        Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have heQ : (∫ x, β x * (profile (P t fε x + ε)) ^ 2 ∂(ν : Measure V)) = Q (profileAffine (P t f) ε) := by
      apply integral_congr_ae
      filter_upwards [profileAffine_rep (P t f) ε, Lp.coeFn_smul c (P t f)] with x hx hy
      rw [heP, hy, Pi.smul_apply, smul_eq_mul, hx]
    change 2 * t * (∫ x, β x * WeakGamma.apply (T ⟨_, Hε.2.2⟩) (T ⟨_, Hε.2.2⟩) x ∂(ν : Measure V)) ≤ _ at hb
    rw [heΓ, heQ, heg] at hb
    convert hb using 1
    ring
  have hle : 2 * t * E ≤ Q (profileAffine (P t f) 0) - Q (P t (profileAffine f 0)) := by
    apply le_of_tendsto_of_tendsto (b := 𝓝[>] (0 : ℝ)) (hlim₁.mono_left nhdsWithin_le_nhds)
      (hlim₂.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds]
      with ε hε hε'
    exact hb ε hε hε'
  refine ⟨profileAffine f 0, ?_, ?_⟩
  · simpa only [mul_zero, sub_zero, one_mul, add_zero] using profileAffine_rep f 0
  · have he : Q (profileAffine (P t f) 0) = ∫ x, β x * (profile (P t f x)) ^ 2 ∂(ν : Measure V) := by
      apply integral_congr_ae
      filter_upwards [profileAffine_rep (P t f) 0] with x hx
      simp only [mul_zero, sub_zero, one_mul, add_zero] at hx
      rw [hx]
    rwa [he] at hle

set_option maxHeartbeats 1600000 in
/-- The Gaussian BGL inequality for unit-interval data in the smooth convex model.
The initial Gaussian profile is an actual L2 class; no epsilon margin remains. -/
theorem exists_ae_gradient_sq_le_profile
    (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let H : (adjointComp T).domain :=
      ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f ht⟩
    ∃ g : Lp ℝ 2 (ν : Measure V),
      (∀ᵐ x ∂(ν : Measure V), g x = profile (f x)) ∧
      ∀ᵐ x ∂(ν : Measure V),
        2 * t * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ≤
          (profile (P t f x)) ^ 2 - (P t g x) ^ 2 := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
    (hν.dense_domain_closedWeightedOperator m _ hi)
  let H : (adjointComp T).domain :=
    ⟨P t f, Generated.mem_adjointComp_domain_apply_of_pos T
      (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi) f ht⟩
  obtain ⟨g, hg, -⟩ := exists_integral_gradient_sq_le_profile m hν hi
    (β := fun _ ↦ 1) aestronglyMeasurable_const (C := 1)
    (ae_of_all _ fun _ ↦ by norm_num) (ae_of_all _ fun _ ↦ zero_le_one)
    hνU hU hconv f hf ht
  have hi₁ : Integrable (fun x ↦ (profile (P t f x)) ^ 2) (ν : Measure V) := by
    simpa only [mul_zero, sub_zero, one_mul, add_zero] using
      (memLp_profile_affine (P t f) 0).integrable_sq
  have hi₂ := (Lp.memLp (P t g)).integrable_sq
  refine ⟨g, hg, ?_⟩
  apply Analysis.TestFunction.ae_le_of_integral_mul_le
    ((WeakGamma.integrable (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩)).const_mul (2 * t)) (hi₁.sub hi₂)
  intro β hβ hβc hβ0
  obtain ⟨C, hC⟩ := hβc.exists_bound_of_continuous hβ.continuous
  have hb : ∀ᵐ x ∂(ν : Measure V), |β x| ≤ C :=
    ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hC x
  obtain ⟨g', hg', hbound⟩ := exists_integral_gradient_sq_le_profile m hν hi
    hβ.continuous.aestronglyMeasurable hb (ae_of_all _ hβ0) hνU hU hconv f hf ht
  have he : g' = g := by
    apply Lp.ext
    filter_upwards [hg', hg] with x hx hy
    exact hx.trans hy.symm
  rw [he] at hbound
  have hb₁ := hi₁.bdd_mul hβ.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have hb₂ := hi₂.bdd_mul hβ.continuous.aestronglyMeasurable (ae_of_all _ hC)
  calc (∫ x, β x * (2 * t * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x) ∂(ν : Measure V)) =
      2 * t * ∫ x, β x * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ∂(ν : Measure V) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun _ ↦ by ring
    _ ≤ _ := hbound
    _ = ∫ x, β x * ((profile (P t f x)) ^ 2 - (P t g x) ^ 2) ∂(ν : Measure V) := by
      rw [← integral_sub hb₁ hb₂]
      apply integral_congr_ae
      exact ae_of_all _ fun _ ↦ by ring
/-- The Gaussian profile bound gives the improved unit-interval gradient coefficient. -/
theorem ae_norm_gradient_le_of_unitInterval (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    (hf : ∀ᵐ x ∂(ν : Measure V), f x ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
          Lp V 2 (ν : Measure V)) x‖ ≤ 1 / (2 * Real.sqrt (Real.pi * t)) := by
  obtain ⟨g, _, hg⟩ := exists_ae_gradient_sq_le_profile m hν hi hνU hU hconv f hf ht
  have hs : 0 < Real.sqrt (Real.pi * t) := Real.sqrt_pos.mpr (mul_pos Real.pi_pos ht)
  have hs₂ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (mul_nonneg Real.pi_pos.le ht.le)
  have hsq₂ := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  filter_upwards [hg] with x hx
  rw [WeakGamma.self_eq_norm_sq] at hx
  change 2 * t * ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
      Lp V 2 (ν : Measure V)) x‖ ^ 2 ≤
    profile (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f x) ^ 2 -
      (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g x) ^ 2 at hx
  have hb := pow_le_pow_left₀ (profile_nonneg (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f x)) (profile_le _) 2
  have hh : 2 * t * ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
        Lp V 2 (ν : Measure V)) x‖ ^ 2 ≤ (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 := by
    nlinarith [sq_nonneg (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g x)]
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg (Real.sqrt (2 * Real.pi)))
  rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs₂.ne'), hsq₂] at hm
  apply (le_div_iff₀ (show 0 < 2 * Real.sqrt (Real.pi * t) by positivity)).mpr
  have hn := norm_nonneg ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
      Lp V 2 (ν : Measure V)) x)
  have hp : (‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
        Lp V 2 (ν : Measure V)) x‖ * (2 * Real.sqrt (Real.pi * t))) ^ 2 ≤ 1 := by
    rw [mul_pow, mul_pow, hsq]
    nlinarith [hm]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- Gaussian BGL improves bounded-data gradient regularization to M/sqrt(pi*t).
The zero bound is included, and no form-domain assumption on the initial datum is needed. -/
theorem ae_norm_gradient_le_of_bounded_pi (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {M : ℝ} (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ M) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
          Lp V 2 (ν : Measure V)) x‖ ≤ M / Real.sqrt (Real.pi * t) := by
  have hM : 0 ≤ M := by obtain ⟨x, hx⟩ := hf.exists; exact (abs_nonneg _).trans hx
  by_cases hM0 : M = 0
  · simpa only [hM0, zero_div] using ae_norm_gradient_le_of_bounded m hν hi hνU hU hconv f hf ht
  have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le
  let c : ℝ := (2 * M)⁻¹
  let e : T.domain := ⟨L2.const ν 1, one_mem_domain_closedWeightedOperator m _ hν hi⟩
  let F : T.domain := ⟨P f, mem_closedWeightedOperator_domain_of_pos m _ hν hi f ht⟩
  let q : Lp ℝ 2 (ν : Measure V) := c • f + (1 / 2 : ℝ) • L2.const ν 1
  have hc : 0 < c := inv_pos.mpr (mul_pos (by norm_num) hMp)
  have hcM : c * M = 1 / 2 := by dsimp [c]; field_simp
  have hq : ∀ᵐ x ∂(ν : Measure V), q x ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hf, Lp.coeFn_add (c • f) ((1 / 2 : ℝ) • L2.const ν 1),
      Lp.coeFn_smul c f, Lp.coeFn_smul (1 / 2 : ℝ) (L2.const ν 1), L2.const_coeFn ν 1]
      with x hx h₁ h₂ h₃ h₄
    change (c • f + (1 / 2 : ℝ) • L2.const ν 1 : Lp ℝ 2 (ν : Measure V)) x ∈ _
    rw [h₁, Pi.add_apply, h₂, h₃, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h₄]
    have hl := mul_le_mul_of_nonneg_left (_root_.abs_le.mp hx).1 hc.le
    have hr := mul_le_mul_of_nonneg_left (_root_.abs_le.mp hx).2 hc.le
    constructor <;> nlinarith
  have heP : P q = c • P f + (1 / 2 : ℝ) • L2.const ν 1 := by
    simp only [q, map_add, map_smul]
    rw [show P (L2.const ν 1) = L2.const ν 1 from one m _ hν hi ht.le]
  have heT : T ⟨P q, mem_closedWeightedOperator_domain_of_pos m _ hν hi q ht⟩ = c • T F := by
    calc T ⟨P q, _⟩ = T (c • F + (1 / 2 : ℝ) • e) := congrArg T (Subtype.ext heP)
      _ = c • T F := by
        rw [T.map_add, T.map_smul, T.map_smul,
          show T e = 0 from closedWeightedOperator_one_eq_zero m _ hν hi, smul_zero, add_zero]
  have hs : 0 < Real.sqrt (Real.pi * t) := Real.sqrt_pos.mpr (mul_pos Real.pi_pos ht)
  filter_upwards [ae_norm_gradient_le_of_unitInterval m hν hi hνU hU hconv q hq ht,
    Lp.coeFn_smul c (T F)] with x hx hy
  change ‖(T ⟨P q, _⟩ : Lp V 2 (ν : Measure V)) x‖ ≤ _ at hx
  rw [heT, hy, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc.le] at hx
  apply (le_div_iff₀ hs).mpr
  have hh := mul_le_mul_of_nonneg_left
    ((le_div_iff₀ (show 0 < 2 * Real.sqrt (Real.pi * t) by positivity)).mp hx) hM
  change ‖(T F : Lp V 2 (ν : Measure V)) x‖ * Real.sqrt (Real.pi * t) ≤ M
  nlinarith [hcM]

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup

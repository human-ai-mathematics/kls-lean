import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ChainRule
import FunctionalInequalities.L2.Composition

/-!
# Interior time differentiation of tested nonlinear heat interpolation

The derivative of `int P_s psi Phi(P_(t-s) f)` is
`int P_s psi Phi''(P_(t-s) f) Gamma(T P_(t-s) f)` for `0 < s < t`.
Nonlinear differentiation is in L2 and the generator terms cancel by the tested
chain rule. No pointwise differentiable representative is assumed. This is not
the squared BGL estimate or its endpoint passage.
-/
noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace NNReal
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

set_option maxHeartbeats 800000 in
/-- The interior derivative of the tested nonlinear heat interpolation for arbitrary
L2 data and a bounded generator-domain test. A C1 potential suffices. -/
theorem hasDerivAt_integral_operator_comp (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ r, |Φ r| ≤ M ∧ |deriv Φ r| ≤ M ∧ |deriv (deriv Φ) r| ≤ M)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (f : Lp ℝ 2 (ν : Measure V)) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let P := Generated.apply T (hν.closedWeightedOperator_isClosed m _ hi)
      (hν.dense_domain_closedWeightedOperator m _ hi)
    let F : (adjointComp T).domain :=
      ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T
        (hν.closedWeightedOperator_isClosed m _ hi) (hν.dense_domain_closedWeightedOperator m _ hi)
        f (sub_pos.mpr hst)⟩
    HasDerivAt (fun r ↦ ∫ x, P r ψ x * Φ (P (t - r) f x) ∂(ν : Measure V))
      (∫ x, (P s ψ x * deriv (deriv Φ) (P (t - s) f x)) *
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x ∂(ν : Measure V)) s := by
  dsimp only
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let P := Generated.apply T hT hd
  let F : (adjointComp T).domain :=
    ⟨P (t - s) f, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f (sub_pos.mpr hst)⟩
  let Ψ : (adjointComp T).domain :=
    ⟨P s ψ, Generated.preserves_domain T hT hd ψ hs.le⟩
  have hL : LipschitzWith ⟨M, hM⟩ Φ := lipschitzWith_of_nnnorm_deriv_le
    (hΦ.differentiable (by simp)) (fun x ↦ by
      change ‖deriv Φ x‖ ≤ M
      simpa only [Real.norm_eq_abs] using (hbound x).2.1)
  have hdΦ := (contDiff_infty_iff_deriv.mp hΦ).2
  have hw : MemLp (fun x ↦ deriv Φ (P (t - s) f x) * (adjointComp T F) x) 2 (ν : Measure V) :=
    L2.memLp_bddSmul (hdΦ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
      (ae_of_all _ fun x ↦ (hbound _).2.1) (adjointComp T F)
  let w := hw.toLp _
  have hF : HasDerivAt (fun r ↦ P (t - r) f) (adjointComp T F) s := by
    have h := (Generated.hasDerivAt_apply_of_pos T hT hd f (sub_pos.mpr hst)).scomp s
      (h := fun r : ℝ ↦ t - r) ((hasDerivAt_id s).const_sub t)
    simpa only [Function.comp_def, neg_smul, one_smul, neg_neg] using h
  have hu := L2.hasDerivAt_compLp (hΦ.differentiable (by simp)) hL hΦ0 hF w hw.coeFn_toLp
  have hΨ := Generated.hasDerivAt_apply T hT hd ψ hs
  have hder := hΨ.inner (𝕜 := ℝ) hu
  have hψbound : ∀ᵐ x ∂(ν : Measure V), |(Ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C :=
    ae_abs_operator_le m (ContinuousLinearMap.id ℝ V) hν hi hs.le _ hC hψb
  have hc := integral_adjointComp_mul_comp_eq m hν hi hνU hU hΦ hΦ0 hM hC hbound Ψ hψbound F
  have e₁ : ⟪-adjointComp T Ψ, hL.compLp hΦ0 (P (t - s) f)⟫ =
      -(∫ x, (adjointComp T Ψ) x * Φ (P (t - s) f x) ∂(ν : Measure V)) := by
    rw [inner_neg_left, MeasureTheory.L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [hL.coeFn_compLp hΦ0 (P (t - s) f)] with x hx
    simp only [hx, Function.comp_def, Real.inner_apply]
  have e₂ : ⟪P s ψ, w⟫ = ∫ x, deriv Φ (P (t - s) f x) *
      WeakGamma.apply (Ψ : Lp ℝ 2 (ν : Measure V)) (adjointComp T F) x ∂(ν : Measure V) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with x hx
    simp only [w, hx, WeakGamma.apply, Real.inner_apply]
    dsimp [Ψ]
    ring
  have heq (r : ℝ) : ⟪P r ψ, hL.compLp hΦ0 (P (t - r) f)⟫ =
      ∫ x, P r ψ x * Φ (P (t - r) f x) ∂(ν : Measure V) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hL.coeFn_compLp hΦ0 (P (t - r) f)] with x hx
    simp only [hx, Function.comp_def, Real.inner_apply]
  have hval : ⟪P s ψ, w⟫ + ⟪-adjointComp T Ψ, hL.compLp hΦ0 (P (t - s) f)⟫ =
      ∫ x, (P s ψ x * deriv (deriv Φ) (P (t - s) f x)) *
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x ∂(ν : Measure V) := by
    rw [e₁, e₂]
    change (∫ x, (adjointComp T Ψ) x * Φ (P (t - s) f x) ∂(ν : Measure V)) = _ at hc
    linarith [hc]
  rw [show (fun r ↦ ⟪P r ψ, hL.compLp hΦ0 (P (t - r) f)⟫) =
    (fun r ↦ ∫ x, P r ψ x * Φ (P (t - r) f x) ∂(ν : Measure V)) from funext heq,
    hval] at hder
  exact hder

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup

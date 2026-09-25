import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GaussianProfile

/-! Independent full-signature clients for nonlinear L2 differentiation and heat interpolation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line.GaussianProfile
open scoped ContDiff RealInnerProductSpace NNReal
namespace HeatCompositionDerivativeAudit
section Generic
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
theorem affine {Φ : ℝ → ℝ} {C : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith C Φ) (h0 : Φ 0 = 0)
    (u v w : Lp ℝ 2 μ) (hw : ∀ᵐ x ∂μ, w x = deriv Φ (u x) * v x) :
    HasDerivAt (fun s : ℝ ↦ hL.compLp h0 (u + s • v)) w 0 :=
  L2.hasDerivAt_compLp_affine hΦ hL h0 u v w hw

theorem curve {Φ : ℝ → ℝ} {C : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith C Φ) (h0 : Φ 0 = 0)
    {F : ℝ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ} {t : ℝ} (hF : HasDerivAt F v t)
    (w : Lp ℝ 2 μ) (hw : ∀ᵐ x ∂μ, w x = deriv Φ (F t x) * v x) :
    HasDerivAt (fun s ↦ hL.compLp h0 (F s)) w t :=
  L2.hasDerivAt_compLp hΦ hL h0 hF w hw

end Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
theorem interpolation (hνU : (ν : Measure V) = m.tilted (-U))
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
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x ∂(ν : Measure V)) s :=
  hasDerivAt_integral_operator_comp m hν hi hνU hU hΦ hΦ0 hM hC hbound ψ hψb f hs hst

theorem gaussian_l2 {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
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
      HasDerivAt G w t :=
  exists_hasDerivAt_shifted_operator m hν hi hε hε' f hf ht

theorem gaussian_interpolation (hνU : (ν : Measure V) = m.tilted (-U))
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
        WeakGamma.apply (T ⟨_, F.2.2⟩) (T ⟨_, F.2.2⟩) x ∂(ν : Measure V))) s :=
  hasDerivAt_integral_operator_shifted m hν hi hνU hU hε hε' hC ψ hψb f hf hs hst

end HeatCompositionDerivativeAudit

#print axioms HeatCompositionDerivativeAudit.affine
#print axioms HeatCompositionDerivativeAudit.curve
#print axioms HeatCompositionDerivativeAudit.interpolation
#print axioms HeatCompositionDerivativeAudit.gaussian_l2
#print axioms HeatCompositionDerivativeAudit.gaussian_interpolation

import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GaussianProfile

/-! Independent full-signature clients for weighted heat Cauchy-Schwarz and dissipation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line.GaussianProfile
open scoped ContDiff RealInnerProductSpace NNReal
namespace HeatWeightedCauchyAudit
section Generic
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
theorem positive (P : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ)
    (hP : ∀ f, 0 ≤ f → 0 ≤ P f) (a b c : Lp ℝ 2 μ)
    (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (h : ∀ᵐ x ∂μ, b x ^ 2 ≤ a x * c x) :
    ∀ᵐ x ∂μ, (P b) x ^ 2 ≤ (P a) x * (P c) x :=
  L2.ae_sq_le_mul_of_positive P hP a b c ha hc h

end Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
theorem weighted
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (a c : Lp ℝ 2 (ν : Measure V))
    (ha : ∀ᵐ x ∂(ν : Measure V), 0 ≤ a x)
    (hc : ∀ᵐ x ∂(ν : Measure V), 0 ≤ c x)
    (hac : ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ^ 2 ≤ a x * c x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
            Lp V 2 (ν : Measure V)) x‖ ^ 2 ≤
        operator m (ContinuousLinearMap.id ℝ V) hν hi ht a x *
          operator m (ContinuousLinearMap.id ℝ V) hν hi ht c x :=
  ae_sq_norm_gradient_le_mul m hν hi hνU hU hconv f a c ha hc hac ht

theorem gaussian (hνU : (ν : Measure V) = m.tilted (-U))
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
        WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ≤ P s a x * P s z x :=
  ae_gradient_sq_le_operator_profile_mul m hν hi hνU hU hconv hε hε' f hf hs hst

theorem differential {β : V → ℝ} {C : ℝ}
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
        -2 * ∫ x, β x * WeakGamma.apply (T ⟨_, H.2.2⟩) (T ⟨_, H.2.2⟩) x ∂(ν : Measure V) :=
  exists_hasDerivAt_integral_operator_profile_sq_le m hν hi hβ hC hβ0 hνU hU hconv hε hε' f hf hs hst

end HeatWeightedCauchyAudit

#print axioms HeatWeightedCauchyAudit.positive
#print axioms HeatWeightedCauchyAudit.weighted
#print axioms HeatWeightedCauchyAudit.gaussian
#print axioms HeatWeightedCauchyAudit.differential

import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate.GaussianProfile

/-! Independent full-signature clients for Gaussian endpoint continuity and epsilon removal. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line.GaussianProfile
open scoped ContDiff RealInnerProductSpace NNReal
namespace HeatProfileLimitAudit
theorem profile_continuous : Continuous profile := continuous_profile

section Generic
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
theorem dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → ℝ} {f b : α → ℝ} (hF : ∀ i, MemLp (F i) 2 μ) (hf : MemLp f 2 μ)
    (hb : MemLp b 2 μ) (hFb : ∀ᶠ i in l, ∀ᵐ x ∂μ, |F i x| ≤ b x)
    (hfb : ∀ᵐ x ∂μ, |f x| ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Tendsto (fun i ↦ (hF i).toLp (F i)) l (𝓝 (hf.toLp f)) :=
  L2.tendsto_toLp_of_dominated hF hf hb hFb hfb hlim
end Generic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
theorem integrated {β : V → ℝ} {C : ℝ}
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
          ∫ x, β x * (P t g x) ^ 2 ∂(ν : Measure V) :=
  exists_integral_gradient_sq_le_profile m hν hi hβ hC hβ0 hνU hU hconv f hf ht

theorem pointwise     (hνU : (ν : Measure V) = m.tilted (-U))
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
          (profile (P t f x)) ^ 2 - (P t g x) ^ 2 :=
  exists_ae_gradient_sq_le_profile m hν hi hνU hU hconv f hf ht

end HeatProfileLimitAudit

#print axioms HeatProfileLimitAudit.profile_continuous
#print axioms HeatProfileLimitAudit.dominated
#print axioms HeatProfileLimitAudit.integrated
#print axioms HeatProfileLimitAudit.pointwise

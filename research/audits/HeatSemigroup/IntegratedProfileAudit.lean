import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate.GaussianProfile

/-! Independent full-signature clients for continuity and integrated Gaussian interpolation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line.GaussianProfile
open scoped ContDiff RealInnerProductSpace NNReal
namespace HeatIntegratedProfileAudit
section Hilbert
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
theorem varying_continuity {S : Set ℝ} (hS : S ⊆ Set.Ici 0)
    {F : ℝ → H₀} (hF : ContinuousOn F S) :
    ContinuousOn (fun s ↦ Generated.apply T hT hd s (F s)) S :=
  Generated.continuousOn_apply_curve T hT hd hS hF
end Hilbert

section Generic
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
theorem quadratic_continuity {β : α → ℝ} {C : ℝ}
    (hβ : AEStronglyMeasurable β μ) (hC : ∀ᵐ x ∂μ, |β x| ≤ C) :
    Continuous (fun f : Lp ℝ 2 μ ↦ ∫ x, β x * (f x) ^ 2 ∂μ) :=
  L2.continuous_integral_mul_sq hβ hC
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
          ∫ x, β x * (P t g x) ^ 2 ∂(ν : Measure V) :=
  exists_integral_gradient_sq_le_profile_sub m hν hi hβ hC hβ0 hνU hU hconv hε hε' f hf ht

theorem pointwise
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
          (profile (P t f x + ε)) ^ 2 - (P t g x) ^ 2 :=
  exists_ae_gradient_sq_le_profile_sub m hν hi hνU hU hconv hε hε' f hf ht

end HeatIntegratedProfileAudit

#print axioms HeatIntegratedProfileAudit.varying_continuity
#print axioms HeatIntegratedProfileAudit.quadratic_continuity
#print axioms HeatIntegratedProfileAudit.integrated
#print axioms HeatIntegratedProfileAudit.pointwise

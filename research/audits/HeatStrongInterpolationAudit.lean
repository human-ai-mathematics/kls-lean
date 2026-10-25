import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GaussianProfile

/-! Independent full-signature clients for strong Gaussian interpolation and its square. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter Topology Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line.GaussianProfile
open scoped ContDiff RealInnerProductSpace NNReal
namespace HeatStrongInterpolationAudit
section Hilbert
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
theorem varying {F : ℝ → H₀} {v : H₀} {t : ℝ}
    (hF : HasDerivAt F v t) (ht : 0 < t) :
    HasDerivAt (fun s ↦ Generated.apply T hT hd s (F s))
      (Generated.apply T hT hd t v - adjointComp T
        ⟨Generated.apply T hT hd t (F t), Generated.mem_adjointComp_domain_apply_of_pos T hT hd (F t) ht⟩) t :=
  Generated.hasDerivAt_apply_curve T hT hd hF ht

theorem domain {F : ℝ → H₀} {v : H₀} {t : ℝ}
    (hF : HasDerivAt F v t) (ht : 0 < t) (hmem : F t ∈ (adjointComp T).domain) :
    HasDerivAt (fun s ↦ Generated.apply T hT hd s (F s))
      (Generated.apply T hT hd t (v - adjointComp T ⟨F t, hmem⟩)) t :=
  Generated.hasDerivAt_apply_curve_of_mem_domain T hT hd hF ht hmem

end Hilbert
section Generic
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
theorem quadratic {β : α → ℝ} {C : ℝ}
    (hβ : AEStronglyMeasurable β μ) (hC : ∀ᵐ x ∂μ, |β x| ≤ C)
    {F : ℝ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ} {t : ℝ} (hF : HasDerivAt F v t) :
    HasDerivAt (fun s ↦ ∫ x, β x * (F s x) ^ 2 ∂μ)
      (2 * ∫ x, β x * F t x * v x ∂μ) t :=
  L2.hasDerivAt_integral_mul_sq hβ hC hF

end Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
theorem shifted (hνU : (ν : Measure V) = m.tilted (-U))
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
      HasDerivAt (fun r ↦ P r (G r)) (-P s z) s :=
  exists_hasDerivAt_operator_shifted m hν hi hνU hU hconv hε hε' f hf hs hst

theorem unshifted (hνU : (ν : Measure V) = m.tilted (-U))
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
      HasDerivAt (fun r ↦ P r (G r)) (-P s z) s :=
  exists_hasDerivAt_operator_profile m hν hi hνU hU hconv hε hε' f hf hs hst

theorem square {β : V → ℝ} {C : ℝ}
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
        (-2 * ∫ x, β x * P s (G s) x * P s z x ∂(ν : Measure V)) s :=
  exists_hasDerivAt_integral_operator_profile_sq m hν hi hβ hC hνU hU hconv hε hε' f hf hs hst

end HeatStrongInterpolationAudit

#print axioms HeatStrongInterpolationAudit.varying
#print axioms HeatStrongInterpolationAudit.domain
#print axioms HeatStrongInterpolationAudit.quadratic
#print axioms HeatStrongInterpolationAudit.shifted
#print axioms HeatStrongInterpolationAudit.unshifted
#print axioms HeatStrongInterpolationAudit.square

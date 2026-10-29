import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate.GaussianProfile

/-! Independent full-signature clients for generator composition and positive-time Gaussian data. -/
set_option maxHeartbeats 800000
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line.GaussianProfile
open Energy.WeightedGradient
open scoped ContDiff RealInnerProductSpace LinearPMap
namespace HeatCompositionDomainAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

theorem recognition
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (u v : Lp ℝ 2 (ν : Measure V))
    (h : ∀ (q : V → ℝ) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q),
      ⟪v, (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q⟫ =
      ⟪u, adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hq hqc⟩⟫) :
    ∃ hu : u ∈ (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨u, hu⟩ = v :=
  exists_mem_domain_apply_eq_of_smooth_pairings m hν hi hνU hU u v h

theorem composition (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ r, |Φ r| ≤ M ∧ |deriv Φ r| ≤ M ∧ |deriv (deriv Φ) r| ≤ M)
    (g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hΓ : MemLp (WeakGamma.apply
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)) 2 (ν : Measure V)) :
    ∃ u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      (∀ᵐ x ∂(ν : Measure V), (u : Lp ℝ 2 (ν : Measure V)) x = Φ ((g : Lp ℝ 2 (ν : Measure V)) x)) ∧
      (∀ᵐ x ∂(ν : Measure V),
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u) x =
        deriv Φ ((g : Lp ℝ 2 (ν : Measure V)) x) *
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x -
        deriv (deriv Φ) ((g : Lp ℝ 2 (ν : Measure V)) x) * WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x) :=
  exists_comp_mem_domain m hν hi hνU hU hΦ hΦ0 hM hbound g hΓ

theorem heat_gamma (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {M : ℝ} (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ M) {t : ℝ} (ht : 0 < t) :
    MemLp (WeakGamma.apply
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩))
      2 (ν : Measure V) :=
  memLp_weakGamma_of_bounded m hν hi hνU hU hconv f hf ht

theorem gaussian_domain (hνU : (ν : Measure V) = m.tilted (-U))
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
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x) :=
  exists_shifted_mem_domain m hν hi hνU hU hε hε' g hg hΓ

theorem heat_gaussian_domain (hνU : (ν : Measure V) = m.tilted (-U))
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
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x) :=
  exists_shifted_operator_mem_domain m hν hi hνU hU hconv hε hε' f hf ht

end HeatCompositionDomainAudit

#print axioms HeatCompositionDomainAudit.recognition
#print axioms HeatCompositionDomainAudit.composition
#print axioms HeatCompositionDomainAudit.heat_gamma
#print axioms HeatCompositionDomainAudit.gaussian_domain
#print axioms HeatCompositionDomainAudit.heat_gaussian_domain

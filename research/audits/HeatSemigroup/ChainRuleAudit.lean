module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate.GaussianProfile

/-! Independent clients for the operator-domain and actual Gaussian-profile identities. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line.GaussianProfile
open scoped ContDiff
namespace HeatChainRuleAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

theorem pairings {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {M C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ r, |Φ r| ≤ M ∧ |deriv Φ r| ≤ M ∧ |deriv (deriv Φ) r| ≤ M)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    Integrable
        (fun x ↦
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
            Φ ((g : Lp ℝ 2 (ν : Measure V)) x))
        (ν : Measure V) ∧
      Integrable
          (fun x ↦
            deriv Φ ((g : Lp ℝ 2 (ν : Measure V)) x) *
              WeakGamma.apply (ψ : Lp ℝ 2 (ν : Measure V))
                (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x)
          (ν : Measure V) ∧
        Integrable
          (fun x ↦
            ((ψ : Lp ℝ 2 (ν : Measure V)) x *
                deriv (deriv Φ) ((g : Lp ℝ 2 (ν : Measure V)) x)) *
              WeakGamma.apply
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x)
          (ν : Measure V) :=
  integrable_chain_pairings m hν hi hΦ hC hbound ψ hψb g

theorem domain_chain (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ r, |Φ r| ≤ M ∧ |deriv Φ r| ≤ M ∧ |deriv (deriv Φ) r| ≤ M)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    (∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      Φ ((g : Lp ℝ 2 (ν : Measure V)) x) ∂(ν : Measure V)) =
    (∫ x, deriv Φ ((g : Lp ℝ 2 (ν : Measure V)) x) *
      WeakGamma.apply (ψ : Lp ℝ 2 (ν : Measure V))
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x
      ∂(ν : Measure V)) -
    ∫ x, ((ψ : Lp ℝ 2 (ν : Measure V)) x * deriv (deriv Φ) ((g : Lp ℝ 2 (ν : Measure V)) x)) *
      WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x
      ∂(ν : Measure V) :=
  integral_adjointComp_mul_comp_eq m hν hi hνU hU hΦ hΦ0 hM hC hbound ψ hψb g

theorem gaussian_chain (hνU : (ν : Measure V) = m.tilted (-U))
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
      ∂(ν : Measure V) :=
  integral_adjointComp_mul_shifted_eq m hν hi hνU hU hε hε' hC ψ hψb g hg

#print axioms pairings
#print axioms domain_chain
#print axioms gaussian_chain
#print axioms WeakGamma.tendsto_integral_mul_of_ae
end HeatChainRuleAudit

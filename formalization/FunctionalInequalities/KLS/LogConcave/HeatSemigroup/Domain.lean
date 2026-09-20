import FunctionalInequalities.Analysis.Semigroup.Generated.Domain
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic

/-! # Heat semigroup domain interfaces
All results require inputs in `D(T̄†T̄)` and allow arbitrary weights `B`.
The gradient supplied here is the closed weighted operator, not a classical representative.
-/
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Semigroup
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- Generator-domain inputs remain in the generator domain, including at time zero. -/
theorem preserves_domain
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t) :
    HeatSemigroup.operator m B hν hi ht f ∈ (adjointComp (hν.closedWeightedOperator m B hi)).domain :=
  Generated.preserves_domain _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht

/-- The nonnegative generator commutes with heat evolution on its domain. -/
theorem generator_comm
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t) :
    adjointComp (hν.closedWeightedOperator m B hi)
      ⟨HeatSemigroup.operator m B hν hi ht f, preserves_domain m B hν hi f ht⟩ =
      HeatSemigroup.operator m B hν hi ht (adjointComp (hν.closedWeightedOperator m B hi) f) :=
  Generated.generator_comm _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht

/-- Generator-domain inputs have a closed weighted gradient after heat evolution. -/
theorem mem_closedWeightedOperator_domain
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t) :
    HeatSemigroup.operator m B hν hi ht f ∈ (hν.closedWeightedOperator m B hi).domain :=
  mem_domain_of_mem_adjointComp_domain _
    ⟨_, preserves_domain m B hν hi f ht⟩

/-- The right time derivative is `-A(P_t f)`, equal to `-P_t(Af)` by commutation. -/
theorem right_derivative
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, ∀ hh : 0 < h, h < δ →
      ‖h⁻¹ • (HeatSemigroup.operator m B hν hi (add_nonneg ht hh.le) f -
        HeatSemigroup.operator m B hν hi ht f) + adjointComp (hν.closedWeightedOperator m B hi)
          ⟨HeatSemigroup.operator m B hν hi ht f, preserves_domain m B hν hi f ht⟩‖ < ε :=
  Generated.right_derivative _
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht hε

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup

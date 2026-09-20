import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic

/-!
# Closed weighted gradient for a full-dimensional log-concave law

The closure is closed and densely defined for every bounded linear weight `B`.
This interface has no dependency on semigroup generation. The domain, core and zero-dimensional
scope are inherited unchanged from the closable weighted-gradient construction.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.KLS.LogConcave

open Energy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section FullDimensional

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)

/-- The closed weighted gradient `T̄`: the closure of `g ↦ B ∘ ∇g` on `L²(ν)`. -/
abbrev closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  (hν.weightedOperator m B hi).closure

/-- `T̄` is closed. -/
theorem closedWeightedOperator_isClosed (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (hν.closedWeightedOperator m B hi).IsClosed :=
  (hν.weightedOperator_isClosable m B hi).closure_isClosed

/-- `T̄` is densely defined: its domain contains the dense domain of `T`. -/
theorem dense_domain_closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Dense ((hν.closedWeightedOperator m B hi).domain : Set (Lp ℝ 2 (ν : Measure V))) :=
  (hν.dense_domain_weightedOperator m B hi).mono fun _ hx =>
    (LinearPMap.le_closure (hν.weightedOperator m B hi)).1 hx

end FullDimensional

end FunctionalInequalities.KLS.LogConcave

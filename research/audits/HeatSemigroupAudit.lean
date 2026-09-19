import FunctionalInequalities.KLS.LogConcave.HeatSemigroup

/-!
# Axiom audit for the heat semigroup of a log-concave law

`KLS/LogConcave/HeatSemigroup.lean` specialises the abstract semigroup construction
(`Analysis/Semigroup/`, route `S1`–`S8`) to the closed weighted gradient of a full-dimensional
log-concave law, and to the intrinsic law of an arbitrary one. There is no route-statement file for
this step — every theorem is a one-line transfer — so this client only records that each public
declaration depends on the standard axioms alone, and exhibits the two boundary uses: `t = 0` and
the transfer of the contraction bound to the intrinsic semigroup.

Out of scope: the Markov property, Bakry–Émery calculus, heat estimates, Buser's inequality.
-/

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS.LogConcave

namespace HeatSemigroupAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : KLS.LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- Boundary case `t = 0`: the heat semigroup is the identity. -/
theorem boundary_t_zero (f : Lp ℝ 2 (ν : Measure V)) : hν.heatSemigroup m B hi le_rfl f = f :=
  hν.heatSemigroup_zero_apply m B hi f

/-- The contraction bound transfers to the intrinsic semigroup of an arbitrary log-concave law. -/
theorem intrinsic_contraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E} (m : Measure (Probability.affineSupport μ).direction)
    [m.IsAddHaarMeasure] (B : (Probability.affineSupport μ).direction →L[ℝ]
      (Probability.affineSupport μ).direction) (hμ : KLS.LogConcave μ) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)) :
    ‖hμ.intrinsicHeatSemigroup m B ht f‖ ≤ ‖f‖ :=
  hμ.intrinsicMeasure.norm_heatSemigroup_apply_le m B hμ.interior_intrinsic_support_nonempty ht f

end HeatSemigroupAudit

/-! ### Axiom reports -/

#print axioms FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_isClosed
#print axioms FunctionalInequalities.KLS.LogConcave.dense_domain_closedWeightedOperator
#print axioms FunctionalInequalities.KLS.LogConcave.heatSemigroup
#print axioms FunctionalInequalities.KLS.LogConcave.norm_heatSemigroup_apply_le
#print axioms FunctionalInequalities.KLS.LogConcave.inner_heatSemigroup_left
#print axioms FunctionalInequalities.KLS.LogConcave.heatSemigroup_zero_apply
#print axioms FunctionalInequalities.KLS.LogConcave.heatSemigroup_add_apply
#print axioms FunctionalInequalities.KLS.LogConcave.continuousOn_heatSemigroup
#print axioms FunctionalInequalities.KLS.LogConcave.heatSemigroup_generator
#print axioms FunctionalInequalities.KLS.LogConcave.inner_adjointComp_self_eq
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicHeatSemigroup
#print axioms HeatSemigroupAudit.boundary_t_zero
#print axioms HeatSemigroupAudit.intrinsic_contraction

import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic

/-!
# Axiom audit for the heat semigroup of a log-concave law

`KLS/LogConcave/HeatSemigroup/Basic.lean` specialises the abstract semigroup construction
(`Analysis/Semigroup/`, `S1`–`S8` of `research/audits/Semigroup/GenerationRouteStatements.lean`)
to the closed weighted gradient of a full-dimensional log-concave law, and to the intrinsic law of
an arbitrary one. There is no route-statement file for
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
theorem boundary_t_zero (f : Lp ℝ 2 (ν : Measure V)) : FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m B hν hi le_rfl f = f :=
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup.zero m B hν hi f

/-- The contraction bound transfers to the intrinsic semigroup of an arbitrary log-concave law. -/
theorem intrinsic_contraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E} (m : Measure (Probability.affineSupport μ).direction)
    [m.IsAddHaarMeasure] (B : (Probability.affineSupport μ).direction →L[ℝ]
      (Probability.affineSupport μ).direction) (hμ : KLS.LogConcave μ) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)) :
    ‖FunctionalInequalities.KLS.LogConcave.HeatSemigroup.intrinsic m B hμ ht f‖ ≤ ‖f‖ :=
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup.norm_apply_le m B hμ.intrinsicMeasure hμ.interior_intrinsic_support_nonempty ht f

end HeatSemigroupAudit

/-! ### Axiom reports -/

#print axioms FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_isClosed
#print axioms FunctionalInequalities.KLS.LogConcave.dense_domain_closedWeightedOperator
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.norm_apply_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.symmetric
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.zero
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.add
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.continuousOn
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.generator_limit
#print axioms FunctionalInequalities.KLS.LogConcave.inner_adjointComp_self_eq
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.intrinsic
#print axioms HeatSemigroupAudit.boundary_t_zero
#print axioms HeatSemigroupAudit.intrinsic_contraction

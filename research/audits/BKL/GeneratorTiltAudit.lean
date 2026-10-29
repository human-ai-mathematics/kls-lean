import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Tilt

/-!
# Audit: the tilt identity (48) and Lemma 3.6 on the generator domain (BKL)

The obligations `O4` and `O5` of `research/audits/BKL/OperatorRouteStatements.lean` (operator route
to Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 3.1) are restated **verbatim** and proved from
the library. For `ν = m.tilted (-U)` with `U ∈ C¹` and all exponential moments, `T̄` the closed
unit-weight gradient, `A = T̄†T̄` and `F ∈ D(A)`, with the representatives of the `L²` classes:

* `o4`: the tilt identity (48), `F_{A F}(z) = ⟪z, F_{T̄ F}(z)⟫` for every `z`
  (`KLS.LogConcave.tiltAverage_adjointComp_eq`);
* `o5`: Lemma 3.6, `T_{d+1}(A F) = S_{d+1} T_d(T̄ F)` for every `d`
  (`KLS.LogConcave.taylorTensor_adjointComp_eq`).

Not audited here: the weak Hessian (`O3` of `OperatorRouteStatements.lean`), the iterates and
Theorem 3.1 itself.
-/

noncomputable section

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

namespace BKLGeneratorTiltAudit

/-- `O4` of `OperatorRouteStatements.lean`, verbatim. -/
theorem o4 : (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → ContDiff ℝ 1 U →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
      (z : V),
      tiltAverage (ν : Measure V)
          (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) z =
        ⟪z, tiltAverage (ν : Measure V)
          (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) z⟫) := by
  intro V _ _ _ _ _ _ _ ν m _ hν hi U hνU hU hexp F z
  exact KLS.LogConcave.tiltAverage_adjointComp_eq m hν hi hνU hU hexp F z

/-- `O5` of `OperatorRouteStatements.lean`, verbatim. -/
theorem o5 : (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → ContDiff ℝ 1 U →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
      (d : ℕ),
      taylorTensor (ν : Measure V)
          (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F))
          (d + 1) =
        symmetrizeML (appendInner (taylorTensor (ν : Measure V)
          (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) d))) := by
  intro V _ _ _ _ _ _ _ ν m _ hν hi U hνU hU hexp F d
  exact KLS.LogConcave.taylorTensor_adjointComp_eq m hν hi hνU hU hexp F d

end BKLGeneratorTiltAudit

#print axioms BKLGeneratorTiltAudit.o4
#print axioms BKLGeneratorTiltAudit.o5
#print axioms FunctionalInequalities.KLS.LogConcave.tiltAverage_adjointComp_eq
#print axioms FunctionalInequalities.KLS.LogConcave.taylorTensor_adjointComp_eq

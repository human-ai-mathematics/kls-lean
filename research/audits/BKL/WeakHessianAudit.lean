module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Hessian

/-!
# Audit: the weak Hessian on `D(A)` and the curvature form of BKL (16)

The two `O3` propositions of `research/audits/BKL/OperatorRouteStatements.lean` (operator route
to Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 3.1), restated verbatim and discharged by the
library theorems of `KLS/LogConcave/HeatSemigroup/Generator/Hessian.lean`:

* `o3_mem_domain`: for `ν = m.tilted (-U)` log-concave with `U` of temperate growth and all
  exponential moments, and `F ∈ D(A)`, each `∂ᵢ F = ⟪eᵢ, T̄ F⟫` lies in `D(T̄)`
  (`compLp_innerSL_mem_closedWeightedOperator_domain`);
* `o3_symm_and_bochner`: the weak Hessian `⟪eⱼ, T̄ ∂ᵢ F⟫` is symmetric
  (`compLp_innerSL_closedWeightedOperator_comm`), and under `∇²U ≥ ρ`,
  `Σᵢ ‖T̄ ∂ᵢ F‖² + ρ ‖T̄ F‖² ≤ ‖A F‖²` (`sum_norm_sq_closedWeightedOperator_add_le`).

These are supporting results of the operator route; they do not state or prove Theorem 3.1, and
they do not establish Lemma 2.1 on the class `𝒜`.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

namespace BKLWeakHessianAudit

/-- `O3` of `OperatorRouteStatements.lean`, first proposition: the weak first derivatives of
`F ∈ D(A)` lie in `D(T̄)`. -/
theorem o3_mem_domain :
    (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain),
      ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :=
  fun m _ hν hi _ hνU hUt hexp F i =>
    KLS.LogConcave.compLp_innerSL_mem_closedWeightedOperator_domain m hν hi hνU hUt hexp F i

/-- `O3` of `OperatorRouteStatements.lean`, second proposition: symmetry of the weak Hessian and
the curvature form of (16). -/
theorem o3_symm_and_bochner :
    (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {ρ : ℝ}, (∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) →
    ∀ (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
      (hD : ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      (∀ i j, (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩) =
        (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD j⟩)) ∧
      ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩‖ ^ 2 +
          ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩‖ ^ 2 ≤
        ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F‖ ^ 2) :=
  fun m _ hν hi _ hνU hUt hexp _ hH F hD =>
    ⟨KLS.LogConcave.compLp_innerSL_closedWeightedOperator_comm m hν hi hνU hUt hexp F hD,
      KLS.LogConcave.sum_norm_sq_closedWeightedOperator_add_le m hν hi hνU hUt hexp hH F hD⟩

end BKLWeakHessianAudit

#print axioms BKLWeakHessianAudit.o3_mem_domain
#print axioms BKLWeakHessianAudit.o3_symm_and_bochner
#print axioms FunctionalInequalities.KLS.LogConcave.compLp_innerSL_mem_closedWeightedOperator_domain
#print axioms FunctionalInequalities.KLS.LogConcave.compLp_innerSL_closedWeightedOperator_comm
#print axioms FunctionalInequalities.KLS.LogConcave.sum_norm_sq_closedWeightedOperator_add_le

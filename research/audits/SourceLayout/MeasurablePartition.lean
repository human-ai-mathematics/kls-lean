module

public import FunctionalInequalities.Analysis.MeasurableCover
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Lean
meta import Lean

@[expose] public section

open FunctionalInequalities.Analysis Set

namespace SourceLayout

/-- An unbounded measurable set can be partitioned under the unit-ball cover without a measure. -/
theorem partition_unit_balls {S : Set ℝ} (hS : MeasurableSet S) (hne : S.Nonempty) :
    ∃ (σ : ℕ → (univ : Set ℝ)) (P : ℕ → Set ℝ),
      (∀ n, MeasurableSet (P n)) ∧ Pairwise (Function.onFun Disjoint P) ∧
      (⋃ n, P n) = S ∧ ∀ n, P n ⊆ Metric.ball (σ n : ℝ) 1 :=
  exists_measurable_partition_subordinate hS (subset_univ _) hne
    (fun z => Metric.ball (z : ℝ) 1) (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.mem_ball_self zero_lt_one) (fun _ => subset_univ _)

#print axioms partition_unit_balls

run_cmd do
  let env ← Lean.getEnv
  for n in [`FunctionalInequalities.Analysis.coarea_of_contDiff,
      `FunctionalInequalities.Analysis.exists_vector_coarea_neighborhood] do
    if env.contains n then throwError "A coarea application leaked into the cover owner: {n}"

end SourceLayout

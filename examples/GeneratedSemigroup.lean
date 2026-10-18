import FunctionalInequalities.Analysis.Semigroup.Generated.Laws

/-! Bounded-operator calls for a closed densely defined operator on real Hilbert spaces. -/
noncomputable section
namespace Examples.GeneratedSemigroup
open FunctionalInequalities.Analysis.Semigroup

section Hilbert
variable {H₀ H₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

example {t : ℝ} (ht : 0 ≤ t) : ‖Generated.operator T hT hd ht‖ ≤ 1 := by
  exact Generated.norm_operator_le_one T hT hd ht

example {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    Generated.operator T hT hd (add_nonneg ht hu) =
      (Generated.operator T hT hd ht).comp (Generated.operator T hT hd hu) := by
  exact Generated.operator_add_time T hT hd ht hu
end Hilbert

-- The zero operator has full dense domain and a closed graph, in every real Hilbert space.
section ZeroOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem zero_closed : (0 : H →ₗ.[ℝ] H).IsClosed := by
  change IsClosed (((0 : H →ₗ.[ℝ] H).graph : Set (H × H)))
  have hgraph : (((0 : H →ₗ.[ℝ] H).graph : Set (H × H))) = {p | p.2 = 0} := by
    ext p
    simp [LinearPMap.mem_graph_iff, LinearPMap.zero_domain, LinearPMap.zero_apply, eq_comm]
  rw [hgraph]
  exact isClosed_eq continuous_snd continuous_const

private theorem zero_dense : Dense ((0 : H →ₗ.[ℝ] H).domain : Set H) := by
  simpa only [LinearPMap.zero_domain, Submodule.top_coe] using (dense_univ : Dense (Set.univ : Set H))

example [CompleteSpace H] (f : H) :
    Generated.operator (0 : H →ₗ.[ℝ] H) zero_closed zero_dense (t := 0) le_rfl f = f := by
  rw [Generated.operator_apply]
  exact Generated.zero_time _ _ _ f
end ZeroOperator
end Examples.GeneratedSemigroup

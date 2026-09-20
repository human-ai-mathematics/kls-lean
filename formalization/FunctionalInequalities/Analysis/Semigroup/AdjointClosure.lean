import FunctionalInequalities.Analysis.Semigroup.AdjointComp
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Weak identities pass to the closure, and into the adjoint

Let `T : H₀ →ₗ.[ℝ] H₁` be a closable operator between real Hilbert spaces. If two fixed vectors
`w : H₀` and `v : H₁` satisfy the weak identity `⟪w, x⟫ = ⟪v, T x⟫` for every `x ∈ D(T)`, the same
identity holds for every `x ∈ D(T̄)` with `T̄ x` in place of `T x`: the set of pairs `(x, y)` with
`⟪w, x⟫ = ⟪v, y⟫` is closed and contains the graph of `T`, hence its closure, which is the graph
of `T̄` (`LinearPMap.IsClosable.graph_closure_eq_closure_graph`).

Consequently `v ∈ D(T̄†)` and, when `D(T̄)` is dense, `T̄† v = w`
(`LinearPMap.mem_adjoint_domain_of_exists`, `LinearPMap.adjoint_apply_eq`). Combined with
`adjointComp` this is the tool that puts a vector `x ∈ D(T̄)` into `D(T̄†T̄)` and computes
`T̄†T̄ x` from a weak identity verified on the unclosed domain only.

Pure Hilbert-space material: no measure, no differential operator, no semigroup.
-/

noncomputable section

open scoped LinearPMap RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]

/-- A weak identity `⟪w, x⟫ = ⟪v, T x⟫` valid on the domain of a closable operator `T` persists on
the domain of its closure. -/
theorem inner_eq_inner_closure_apply {T : H₀ →ₗ.[ℝ] H₁} (hT : T.IsClosable) {w : H₀} {v : H₁}
    (h : ∀ x : T.domain, ⟪w, (x : H₀)⟫ = ⟪v, T x⟫) (x : T.closure.domain) :
    ⟪w, (x : H₀)⟫ = ⟪v, T.closure x⟫ := by
  have hmem : ((x : H₀), T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hT.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  have hclosed : IsClosed {p : H₀ × H₁ | ⟪w, p.1⟫ = ⟪v, p.2⟫} :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
  have hsub : (T.graph : Set (H₀ × H₁)) ⊆ {p : H₀ × H₁ | ⟪w, p.1⟫ = ⟪v, p.2⟫} := by
    intro p hp
    obtain ⟨y, rfl⟩ := T.mem_graph_iff'.mp hp
    exact h y
  have hcl := closure_minimal hsub hclosed
  rw [← Submodule.topologicalClosure_coe] at hcl
  exact hcl hmem

variable [CompleteSpace H₀]

/-- If `⟪w, x⟫ = ⟪v, T x⟫` for every `x ∈ D(T)` and `T` is closable, then `v ∈ D(T̄†)`. -/
theorem mem_adjoint_domain_closure_of_forall {T : H₀ →ₗ.[ℝ] H₁} (hT : T.IsClosable) {w : H₀}
    {v : H₁} (h : ∀ x : T.domain, ⟪w, (x : H₀)⟫ = ⟪v, T x⟫) : v ∈ T.closure†.domain :=
  LinearPMap.mem_adjoint_domain_of_exists v ⟨w, inner_eq_inner_closure_apply hT h⟩

/-- If `⟪w, x⟫ = ⟪v, T x⟫` for every `x ∈ D(T)`, `T` is closable and `D(T̄)` is dense, then
`T̄† v = w`. -/
theorem adjoint_closure_apply_eq_of_forall {T : H₀ →ₗ.[ℝ] H₁} (hT : T.IsClosable)
    (hd : Dense (T.closure.domain : Set H₀)) {w : H₀} {v : H₁}
    (h : ∀ x : T.domain, ⟪w, (x : H₀)⟫ = ⟪v, T x⟫) :
    T.closure† ⟨v, mem_adjoint_domain_closure_of_forall hT h⟩ = w :=
  LinearPMap.adjoint_apply_eq hd _ (inner_eq_inner_closure_apply hT h)

end FunctionalInequalities.Analysis.Semigroup

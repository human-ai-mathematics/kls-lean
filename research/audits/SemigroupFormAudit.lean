import FunctionalInequalities.Analysis.Semigroup.Resolvent.Form
import FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic

/-!
# Scope audit for `S1`–`S4` of the semigroup-generation route

The obligations `S1`, `S2`, `S3` and `S4` of
`research/audits/SemigroupGenerationRouteStatements.lean` are restated here **verbatim** — the
propositions are copied character for character from that route snapshot — and discharged from the
new hole-free modules `Analysis/Semigroup/Resolvent/Form.lean` and `Analysis/Semigroup/Resolvent/Basic.lean`. A renamed binder, a reordered hypothesis or a
weakened conclusion would fail to elaborate here.

`S2` is discharged from a **strictly stronger** module lemma: the route assumed `0 < s`, but
`Analysis.Semigroup.min_one_mul_graphNormSq_le` holds for every real `s`, so the audit supplies the
route's hypothesis and discards it. That is recorded rather than silently absorbed.

`S3` is likewise discharged from a stronger lemma: the route assumed `Dense (T.domain)`, which is
needed for neither half, so the audit supplies it and discards it.

Out of scope, deliberately absent: `S5`–`S8` (the
Yosida approximation, strong convergence, the semigroup laws and the generator), and every later
gap of `thm:logconcave-cheeger-poincare-comparison` — the Markov property, Bakry–Émery
`Γ`-calculus, small-time heat estimates and localization. **Nothing here is Buser's inequality or
any step of it beyond the form estimates.**

Two boundary cases follow the route items: the zero operator, where the graph norm is the ambient
norm, and the datum `f = 0`, where the weak resolvent equation forces the solution to vanish in
norm.

The axiom reports at the end cover every public declaration of the new module and every theorem of
this client.
-/

noncomputable section

open InnerProductSpace FunctionalInequalities

open scoped RealInnerProductSpace

namespace SemigroupFormAudit

/-! ### `S1` — the form domain is a Hilbert space -/

/-- `S1`, restated verbatim and discharged. -/
theorem route_S1 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
      [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
      (T : H₀ →ₗ.[ℝ] H₁), T.IsClosed → CompleteSpace T.graph := by
  intro H₀ H₁ _ _ _ _ _ _ T hT
  exact Analysis.Semigroup.completeSpace_graph T hT

/-! ### `S2` — the shifted form is bounded and coercive on the form domain -/

/-- `S2`, restated verbatim and discharged. The route's `0 < s` is accepted and unused. -/
theorem route_S2 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
      [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
      (T : H₀ →ₗ.[ℝ] H₁) {s : ℝ}, 0 < s → ∀ u : T.domain,
        min 1 s * (‖(u : H₀)‖ ^ 2 + ‖T u‖ ^ 2) ≤ ‖(u : H₀)‖ ^ 2 + s * ‖T u‖ ^ 2 := by
  intro H₀ H₁ _ _ _ _ _ _ T s _ u
  exact Analysis.Semigroup.min_one_mul_graphNormSq_le T s u

/-! ### `S4` — the resolvent is a self-adjoint contraction -/

/-- `S4`, restated verbatim and discharged. -/
theorem route_S4 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
      [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
      (T : H₀ →ₗ.[ℝ] H₁) {s : ℝ}, 0 < s → ∀ (f : H₀) (u : T.domain),
        (∀ v : T.domain, ⟪(u : H₀), (v : H₀)⟫ + s * ⟪T u, T v⟫ = ⟪f, (v : H₀)⟫) →
          ‖(u : H₀)‖ ≤ ‖f‖ ∧ 0 ≤ ⟪(u : H₀), f⟫ := by
  intro H₀ H₁ _ _ _ _ _ _ T s hs f u hu
  exact ⟨Analysis.Semigroup.norm_le_of_weakResolvent hs hu,
    Analysis.Semigroup.inner_nonneg_of_weakResolvent hs hu⟩

section InnerProduct

variable {H₀ H₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-! ### Boundary cases -/

/-- The zero operator: the graph norm collapses to the ambient norm, so `S2` there is the
elementary bound `min 1 s * ‖u‖² ≤ ‖u‖²`. -/
theorem boundary_zero_operator
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] (s : ℝ)
    (u : (0 : H₀ →ₗ.[ℝ] H₁).domain) :
    min 1 s * (‖(u : H₀)‖ ^ 2 + ‖(0 : H₀ →ₗ.[ℝ] H₁) u‖ ^ 2)
      ≤ ‖(u : H₀)‖ ^ 2 + s * ‖(0 : H₀ →ₗ.[ℝ] H₁) u‖ ^ 2 :=
  Analysis.Semigroup.min_one_mul_graphNormSq_le _ s u

/-- Zero datum: the weak resolvent equation with `f = 0` forces the solution to have zero norm,
which is uniqueness of the resolvent at `0` in norm. -/
theorem boundary_zero_datum
    [CompleteSpace H₀] [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    {T : H₀ →ₗ.[ℝ] H₁} {s : ℝ} (hs : 0 < s) {u : T.domain}
    (hu : Analysis.Semigroup.WeakResolvent T s 0 u) :
    ‖(u : H₀)‖ = 0 :=
  le_antisymm (by simpa using Analysis.Semigroup.norm_le_of_weakResolvent hs hu) (norm_nonneg _)

end InnerProduct

/-! ### `S3` — existence and uniqueness of the resolvent -/

/-- `S3`, restated verbatim and discharged. The route's `Dense (T.domain)` is accepted and unused:
uniqueness needs neither closedness nor density, and existence needs only closedness. -/
theorem route_S3 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
      [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
      (T : H₀ →ₗ.[ℝ] H₁), T.IsClosed → Dense (T.domain : Set H₀) → ∀ {s : ℝ}, 0 < s →
        ∀ f : H₀, ∃! u : T.domain,
          ∀ v : T.domain, ⟪(u : H₀), (v : H₀)⟫ + s * ⟪T u, T v⟫ = ⟪f, (v : H₀)⟫ := by
  intro H₀ H₁ _ _ _ _ _ _ T hT _ s hs f
  exact Analysis.Semigroup.existsUnique_weakResolvent T hT hs f

/-- The ambient Hilbert space the existence proof runs in: the rescaled graph of a closed operator,
inside the `L²` product, is complete. -/
theorem scaledGraph_complete :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
      [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
      (T : H₀ →ₗ.[ℝ] H₁) (s : ℝ), T.IsClosed →
        CompleteSpace (Analysis.Semigroup.scaledGraphL2 T s) := by
  intro H₀ H₁ _ _ _ _ _ _ T s hT
  exact Analysis.Semigroup.completeSpace_scaledGraphL2 T s hT

/-! ### Beyond the route: the resolvent as a bounded operator

Not a route obligation — the route's `S4` speaks of solutions, not of a bundled operator — but the
object `S5`–`S8` are built from. Linearity comes from uniqueness (`S3`), the norm bound and
nonnegativity from `S4`, self-adjointness from symmetry of the form. -/

/-- `J_s` is a self-adjoint nonnegative contraction. -/
theorem resolvent_operator_properties {H₀ H₁ : Type*} [NormedAddCommGroup H₀]
    [InnerProductSpace ℝ H₀] [CompleteSpace H₀] [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [CompleteSpace H₁] (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) :
    (∀ f, ‖Analysis.Semigroup.resolventCLM T hT hs f‖ ≤ ‖f‖) ∧
    (∀ f g, ⟪Analysis.Semigroup.resolventCLM T hT hs f, g⟫
      = ⟪f, Analysis.Semigroup.resolventCLM T hT hs g⟫) ∧
    (∀ f, 0 ≤ ⟪Analysis.Semigroup.resolventCLM T hT hs f, f⟫) :=
  ⟨Analysis.Semigroup.norm_resolventCLM_le T hT hs,
   Analysis.Semigroup.resolventCLM_symm T hT hs,
   Analysis.Semigroup.resolventCLM_nonneg T hT hs⟩

end SemigroupFormAudit

#print axioms FunctionalInequalities.Analysis.Semigroup.completeSpace_graph
#print axioms FunctionalInequalities.Analysis.Semigroup.min_one_mul_graphNormSq_le
#print axioms FunctionalInequalities.Analysis.Semigroup.graphNormSq_eq_inner_of_weakResolvent
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_le_of_weakResolvent
#print axioms FunctionalInequalities.Analysis.Semigroup.inner_nonneg_of_weakResolvent

#print axioms SemigroupFormAudit.route_S1
#print axioms SemigroupFormAudit.route_S2
#print axioms SemigroupFormAudit.route_S4
#print axioms SemigroupFormAudit.boundary_zero_operator
#print axioms SemigroupFormAudit.boundary_zero_datum

#print axioms FunctionalInequalities.Analysis.Semigroup.weakResolvent_unique
#print axioms FunctionalInequalities.Analysis.Semigroup.isClosed_graphL2
#print axioms FunctionalInequalities.Analysis.Semigroup.completeSpace_graphL2
#print axioms FunctionalInequalities.Analysis.Semigroup.exists_weakResolvent
#print axioms FunctionalInequalities.Analysis.Semigroup.existsUnique_weakResolvent
#print axioms FunctionalInequalities.Analysis.Semigroup.completeSpace_scaledGraphL2
#print axioms SemigroupFormAudit.route_S3
#print axioms SemigroupFormAudit.scaledGraph_complete

#print axioms FunctionalInequalities.Analysis.Semigroup.resolventCLM
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_resolventCLM_le
#print axioms FunctionalInequalities.Analysis.Semigroup.resolventCLM_symm
#print axioms FunctionalInequalities.Analysis.Semigroup.resolventCLM_nonneg
#print axioms SemigroupFormAudit.resolvent_operator_properties

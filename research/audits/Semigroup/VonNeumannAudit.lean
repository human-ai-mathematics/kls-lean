import FunctionalInequalities.Analysis.Semigroup.VonNeumann

/-!
# Scope audit for `V1`–`V5` of `VonNeumannRouteStatements.lean`

The five obligations of Part A of `research/audits/Semigroup/VonNeumannRouteStatements.lean` are restated
here **verbatim** — each proposition is copied character for character from that route file —
and discharged from the hole-free module `Analysis/Semigroup/VonNeumann.lean`. A renamed
binder, a reordered hypothesis or a weakened conclusion would fail to elaborate here.

Three of the five are discharged from **strictly stronger** module statements, recorded rather
than silently absorbed, as for `0 < s`, density and self-adjointness in the audits of
`GenerationRouteStatements.lean` (`FormAudit.lean`, `ExponentialContractionAudit.lean`):

* The form identity (`inner_adjointComp_apply`) uses neither `CompleteSpace H₁` nor closedness of
  `T`; the audit supplies the instance the route statement carries and the module ignores it.
* The domain half of the resolvent inversion (`mem_adjointComp_domain_resolventDomain`) needs no
  density of `D(T)`; only the identification of the value of `T†` does.
* Density of `D(T†T)` (`dense_adjointComp_domain`) is proved directly rather than from
  self-adjointness, because `LinearPMap.IsFormalAdjoint.le_adjoint` — the step from symmetry to
  `T†T ≤ (T†T)†` — already needs `D(T†T)` dense. The route's order (self-adjointness, then density
  via `IsSelfAdjoint.dense_domain`) is therefore reversed; the verbatim statements are unaffected.

Out of scope, deliberately absent: Part B of the route (`R1`–`R3` of
`VonNeumannRouteStatements.lean`, the resolvent limits, audited in `ResolventLimitAudit.lean`),
`S6`–`S8` of `GenerationRouteStatements.lean` (the Yosida exponentials, their strong convergence
and the semigroup), and every later step of
`thm:logconcave-cheeger-poincare-comparison` — the Markov property, Bakry–Émery `Γ`-calculus,
small-time heat estimates and localization. **Nothing here is Buser's inequality or any step of
it**, and nothing here mentions a measure, log-concavity or any KLS quantity.

The axiom reports at the end cover every public declaration of the new module and every theorem of
this client.
-/

noncomputable section

open InnerProductSpace FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace LinearPMap

namespace VonNeumannAudit

/-! ### `T†T` acts through the form -/

/-- `V1` of `VonNeumannRouteStatements.lean`, restated verbatim and discharged. The route's
`CompleteSpace H₁` instance is taken and unused by the module lemma. -/
theorem route_V1 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁), Dense (T.domain : Set H₀) →
      ∀ (x : (adjointComp T).domain) (y : T.domain),
        ⟪adjointComp T x, (y : H₀)⟫ = ⟪T ⟨(x : H₀), x.2.2⟩, T y⟫ := by
  intro H₀ H₁ _ _ _ _ _ _ T hd x y
  exact inner_adjointComp_apply T hd x y

/-! ### The resolvent inverts `1 + s T†T` -/

/-- `V2` of `VonNeumannRouteStatements.lean`, restated verbatim and discharged. -/
theorem route_V2 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) → ∀ {s : ℝ} (hs : 0 < s),
      ∀ f : H₀, ∃ hu : resolventCLM T hT hs f ∈ (adjointComp T).domain,
        resolventCLM T hT hs f + s • adjointComp T ⟨resolventCLM T hT hs f, hu⟩ = f := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd s hs f
  exact resolvent_add_smul_adjointComp T hT hd hs f

/-- The domain half of the resolvent inversion without density: the module's own strengthening. -/
theorem route_V2_domain_of_not_dense :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), ∀ {s : ℝ} (hs : 0 < s),
      ∀ f : H₀, resolventCLM T hT hs f ∈ (adjointComp T).domain := by
  intro H₀ H₁ _ _ _ _ _ _ T hT s hs f
  exact mem_adjointComp_domain_resolventDomain T hT hs f

/-! ### `T†T` is self-adjoint (von Neumann) -/

/-- `V3` of `VonNeumannRouteStatements.lean`, restated verbatim and discharged. -/
theorem route_V3 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁), T.IsClosed → Dense (T.domain : Set H₀) →
      IsSelfAdjoint (adjointComp T) := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd
  exact isSelfAdjoint_adjointComp T hT hd

/-! ### `D(T†T)` is dense -/

/-- `V4` of `VonNeumannRouteStatements.lean`, restated verbatim and discharged. -/
theorem route_V4 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁), T.IsClosed → Dense (T.domain : Set H₀) →
      Dense ((adjointComp T).domain : Set H₀) := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd
  exact dense_adjointComp_domain T hT hd

/-! ### The Yosida approximation on `D(T†T)` -/

/-- `V5` of `VonNeumannRouteStatements.lean`, restated verbatim and discharged. -/
theorem route_V5 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) → ∀ {s : ℝ} (hs : 0 < s),
      ∀ f : (adjointComp T).domain,
        (f : H₀) - resolventCLM T hT hs f = s • resolventCLM T hT hs (adjointComp T f) := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd s hs f
  exact sub_resolvent_eq_smul T hT hd hs f

section InnerProduct

variable {H₀ H₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀] [NormedAddCommGroup H₁]
  [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-! ### Consistency checks

Self-adjointness of `T†T` and density of its domain are consistent with Mathlib: a self-adjoint
`LinearPMap` has dense domain, so self-adjointness re-derives density, and a self-adjoint
`LinearPMap` is closed, so `T†T` is closed. -/

/-- Density of `D(T†T)` re-derived from self-adjointness through Mathlib's
`IsSelfAdjoint.dense_domain`, confirming that the two route items agree even though the module
proves them in the opposite order. -/
theorem dense_of_route_V3
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) :
    Dense ((adjointComp T).domain : Set H₀) :=
  (isSelfAdjoint_adjointComp T hT hd).dense_domain

/-- `T†T` is closed, by self-adjointness and Mathlib's `IsSelfAdjoint.isClosed`. -/
theorem isClosed_of_route_V3
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) :
    (adjointComp T).IsClosed :=
  (isSelfAdjoint_adjointComp T hT hd).isClosed

end InnerProduct

end VonNeumannAudit

/-! ### Axiom reports -/

#print axioms FunctionalInequalities.Analysis.Semigroup.inner_adjointComp
#print axioms FunctionalInequalities.Analysis.Semigroup.inner_adjointComp_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.adjointComp_isFormalAdjoint
#print axioms FunctionalInequalities.Analysis.Semigroup.mem_adjointComp_domain_resolventDomain
#print axioms FunctionalInequalities.Analysis.Semigroup.adjointComp_resolventDomain
#print axioms FunctionalInequalities.Analysis.Semigroup.resolvent_add_smul_adjointComp
#print axioms FunctionalInequalities.Analysis.Semigroup.exists_add_adjointComp
#print axioms FunctionalInequalities.Analysis.Semigroup.dense_adjointComp_domain
#print axioms FunctionalInequalities.Analysis.Semigroup.isSelfAdjoint_adjointComp
#print axioms FunctionalInequalities.Analysis.Semigroup.sub_resolvent_eq_smul
#print axioms VonNeumannAudit.route_V1
#print axioms VonNeumannAudit.route_V2
#print axioms VonNeumannAudit.route_V2_domain_of_not_dense
#print axioms VonNeumannAudit.route_V3
#print axioms VonNeumannAudit.route_V4
#print axioms VonNeumannAudit.route_V5
#print axioms VonNeumannAudit.dense_of_route_V3
#print axioms VonNeumannAudit.isClosed_of_route_V3

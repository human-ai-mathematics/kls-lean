import FunctionalInequalities.Analysis.Semigroup.Resolvent.Limit

/-!
# Scope audit for `R1`–`R3` of the von Neumann route

The obligations `R1`, `R2` and `R3` — Part B, "resolvent limits" — of
`research/audits/VonNeumannRouteStatements.lean` are restated here **verbatim**: the propositions
are copied character for character from that route snapshot and discharged from the new hole-free
module `FunctionalInequalities/Analysis/Semigroup/Resolvent/Limit.lean`. A renamed binder, a
reordered hypothesis or a weakened conclusion would fail to elaborate here.

`R1` is discharged from a **strictly stronger** module lemma: the route asks for
`‖J_s f - f‖ ^ 2 ≤ s ‖T f‖ ^ 2`, while `Analysis.Semigroup.norm_resolventCLM_sub_sq_le_quarter`
gives the sharp `s ‖T f‖ ^ 2 / 4`. That is recorded rather than silently absorbed. No route
hypothesis of `R1`–`R3` is dropped: closedness enters through `resolventCLM`, completeness of both
spaces is needed for `resolventCLM` to exist, and `R2` genuinely uses density of the domain.

Out of scope, deliberately absent: **all of Part A**, `V1`–`V5`, which is owned by another session
— nothing here or in the audited module mentions `LinearPMap.adjoint`, `T†`, `adjointComp` or
`adjointCompDomain`, and the module does not import `Analysis/Semigroup/AdjointComp.lean`. Also
absent: `S6`–`S8` of the semigroup-generation route (the Yosida exponentials, the semigroup laws,
the generator), the Markov property, Bakry–Émery `Γ`-calculus, small-time heat estimates, and
**every step of Buser's inequality**. `thm:logconcave-cheeger-poincare-comparison` gains no
progress marker from this client.

The axiom reports at the end cover every public declaration of the new module and every theorem of
this client.
-/

noncomputable section

open InnerProductSpace FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

namespace ResolventLimitAudit

/-! ### `R1` — quantitative convergence on `D(T)` -/

/-- `R1`, restated verbatim and discharged. The module lemma behind it is sharper by a factor
`4`. -/
theorem route_R1 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : T.domain),
      ‖resolventCLM T hT hs f - f‖ ^ 2 ≤ s * ‖T f‖ ^ 2 := by
  intro H₀ H₁ _ _ _ _ _ _ T hT s hs f
  exact norm_resolventCLM_sub_sq_le T hT hs f

/-! ### `R2` — strong convergence `J_s → 1` as `s ↓ 0` -/

/-- `R2`, restated verbatim and discharged. -/
theorem route_R2 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) → ∀ (f : H₀) {ε : ℝ}, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖resolventCLM T hT hs f - f‖ < ε := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hD f ε hε
  exact exists_delta_norm_resolventCLM_sub_lt T hT hD f hε

/-! ### `R3` — the resolvents commute -/

/-- `R3`, restated verbatim and discharged. -/
theorem route_R3 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s) (hr : 0 < r),
      (resolventCLM T hT hs).comp (resolventCLM T hT hr) =
        (resolventCLM T hT hr).comp (resolventCLM T hT hs) := by
  intro H₀ H₁ _ _ _ _ _ _ T hT s r hs hr
  exact resolventCLM_comp_comm T hT hs hr

end ResolventLimitAudit

#print axioms FunctionalInequalities.Analysis.Semigroup.norm_resolventCLM_sub_sq_eq
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_resolventCLM_sub_sq_le_quarter
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_resolventCLM_sub_sq_le
#print axioms FunctionalInequalities.Analysis.Semigroup.exists_delta_norm_resolventCLM_sub_lt
#print axioms FunctionalInequalities.Analysis.Semigroup.resolventDomain_identity
#print axioms FunctionalInequalities.Analysis.Semigroup.resolventCLM_comp_comm

#print axioms ResolventLimitAudit.route_R1
#print axioms ResolventLimitAudit.route_R2
#print axioms ResolventLimitAudit.route_R3

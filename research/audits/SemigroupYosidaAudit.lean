import FunctionalInequalities.Analysis.Semigroup.Exponential.Contraction

/-!
# Scope audit for `S5` of the semigroup-generation route

The obligation `S5` of `research/audits/SemigroupGenerationRouteStatements.lean` is restated here
**verbatim** — the proposition is copied character for character from that route snapshot — and
discharged from the new hole-free module `Analysis/Semigroup/Exponential/Contraction.lean`. A renamed binder, a
reordered hypothesis or a weakened conclusion would fail to elaborate here.

`S5` is discharged from a **strictly stronger** module lemma: the route assumed `L` self-adjoint,
`∀ f g, ⟪L f, g⟫ = ⟪f, L g⟫`, but `Analysis.Semigroup.norm_exp_neg_smul_apply_le` needs only
nonnegativity `∀ f, 0 ≤ ⟪L f, f⟫`, so the audit supplies the route's hypothesis and discards it.
That is recorded rather than silently absorbed, as for `0 < s` in `S2` and density in `S3`.

Out of scope, deliberately absent: `S6`–`S8` (strong convergence of the Yosida exponentials, the
semigroup laws and the generator), and every later gap of
`thm:logconcave-cheeger-poincare-comparison` — the Markov property, Bakry–Émery `Γ`-calculus,
small-time heat estimates and localization. **Nothing here is Buser's inequality or any step of
it.**

Two boundary cases follow the route item: `t = 0`, where the exponential is the identity and the
bound is an equality, and `L = 0`, where every exponential is the identity.

The axiom reports at the end cover every public declaration of the new module and every theorem of
this client.
-/

noncomputable section

open InnerProductSpace FunctionalInequalities

open scoped RealInnerProductSpace

namespace SemigroupYosidaAudit

/-! ### `S5` — the Yosida approximation exponentiates to a contraction -/

/-- `S5`, restated verbatim and discharged. The route's self-adjointness hypothesis is accepted
and unused. -/
theorem route_S5 :
    ∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (L : H₀ →L[ℝ] H₀), (∀ f, 0 ≤ ⟪L f, f⟫) → (∀ f g, ⟪L f, g⟫ = ⟪f, L g⟫) →
      ∀ t : ℝ, 0 ≤ t → ∀ f : H₀, ‖NormedSpace.exp (-t • L) f‖ ≤ ‖f‖ := by
  intro H₀ _ _ _ L hL _ t ht f
  exact Analysis.Semigroup.norm_exp_neg_smul_apply_le L hL ht f

/-- `S5` without the self-adjointness hypothesis: the module's own strengthening. -/
theorem route_S5_of_nonneg :
    ∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (L : H₀ →L[ℝ] H₀), (∀ f, 0 ≤ ⟪L f, f⟫) →
      ∀ t : ℝ, 0 ≤ t → ∀ f : H₀, ‖NormedSpace.exp (-t • L) f‖ ≤ ‖f‖ := by
  intro H₀ _ _ _ L hL t ht f
  exact Analysis.Semigroup.norm_exp_neg_smul_apply_le L hL ht f

section InnerProduct

variable {H₀ : Type*}
variable [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-! ### Boundary cases -/

/-- At `t = 0` the exponential is the identity, so the contraction bound is an equality. -/
theorem boundary_t_zero
    [CompleteSpace H₀] (L : H₀ →L[ℝ] H₀) (f : H₀) :
    ‖NormedSpace.exp (-(0 : ℝ) • L) f‖ = ‖f‖ := by
  simp

/-- For `L = 0` every exponential is the identity, and the hypothesis of the module lemma holds
trivially, so both routes give the same equality. -/
theorem boundary_L_zero
    [CompleteSpace H₀] (t : ℝ) (ht : 0 ≤ t) (f : H₀) :
    ‖NormedSpace.exp (-t • (0 : H₀ →L[ℝ] H₀)) f‖ ≤ ‖f‖ :=
  Analysis.Semigroup.norm_exp_neg_smul_apply_le 0 (fun f => by simp) ht f

end InnerProduct

end SemigroupYosidaAudit

/-! ### Axiom reports -/

#print axioms FunctionalInequalities.Analysis.Semigroup.hasDerivAt_exp_smul_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.antitone_normSq_exp_smul_neg
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_exp_neg_smul_apply_le
#print axioms FunctionalInequalities.Analysis.Semigroup.route_S5
#print axioms SemigroupYosidaAudit.route_S5
#print axioms SemigroupYosidaAudit.route_S5_of_nonneg
#print axioms SemigroupYosidaAudit.boundary_t_zero
#print axioms SemigroupYosidaAudit.boundary_L_zero

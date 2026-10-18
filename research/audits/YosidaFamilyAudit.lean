import FunctionalInequalities.Analysis.Semigroup.Exponential.Counterexample
import FunctionalInequalities.Analysis.Semigroup.Yosida.Laws

/-!
# Scope audit for `Y0`–`Y5` of the Yosida-limit route

The six obligations of Part A of `research/audits/YosidaLimitRouteStatements.lean` are restated
here **verbatim** — each proposition is copied character for character from that route contract —
and discharged from `Analysis/Semigroup/Yosida/Laws.lean` and
`Analysis/Semigroup/Exponential/Counterexample.lean`. A renamed
binder, a reordered hypothesis or a weakened conclusion would fail to elaborate here.

`Y0` is the negative item: it records that the abstract `S6` of
`research/audits/SemigroupGenerationRouteStatements.lean` — strong convergence of
`exp (-t • L s) f` for a family assumed only nonnegative and commuting — **is false**. The route
file records the abstract contract; `Y0` makes the need for the corrected Cauchy hypothesis explicit.

Unlike `S2`, `S3`, `S5`, `V1` and `V2`, none of `Y0`–`Y5` is discharged from a strictly stronger
module statement: no route hypothesis turned out to be superfluous. In particular the density
hypothesis of `Y4` is genuinely used, because `Y4` divides `V5` by `s` and `V5` identifies a value
of Mathlib's `LinearPMap.adjoint`, which is junk on a non-dense domain.

Out of scope, deliberately absent: Part B of the route (`Y6`, the mean-value bound for two
commuting nonnegative exponentials; `Y7`, the corrected abstract `S6` with a Cauchy hypothesis on
a dense set; `Y8`, `S6` for the Yosida approximation), `S7` and `S8`
of the semigroup-generation route, and the Markov property, Bakry–Émery `Γ`-calculus,
small-time heat estimates and localization. **Nothing here is Buser's inequality or any step of
it**, and nothing here mentions a measure, log-concavity or any KLS quantity.

The axiom reports at the end cover every public declaration of the source modules and every theorem of
this client.
-/

noncomputable section

open Filter Topology InnerProductSpace FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

namespace YosidaFamilyAudit

/-! ### `Y0` — the abstract `S6` is false -/

/-- `Y0`, restated verbatim and discharged. -/
theorem route_Y0 :
    ¬ (∀ (L : ℝ → ℝ →L[ℝ] ℝ),
      (∀ s : ℝ, 0 < s → ∀ f, 0 ≤ ⟪L s f, f⟫) →
      (∀ s r : ℝ, 0 < s → 0 < r → (L s).comp (L r) = (L r).comp (L s)) →
      (∀ f : ℝ, ∀ t : ℝ, 0 ≤ t →
        ∃ g : ℝ, Tendsto (fun s : ℝ => NormedSpace.exp (-t • L s) f) (𝓝[>] 0) (𝓝 g))) :=
  not_forall_exists_tendsto_exp_neg_smul

/-! ### `Y1` — `L_s` is nonnegative -/

/-- `Y1`, restated verbatim and discharged. -/
theorem route_Y1 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀),
      0 ≤ ⟪yosida T hT hs f, f⟫ := by
  intro H₀ H₁ _ _ _ _ _ _ T hT s hs f
  exact yosida_nonneg T hT hs f

/-! ### `Y2` — `L_s` is symmetric -/

/-- `Y2`, restated verbatim and discharged. -/
theorem route_Y2 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f g : H₀),
      ⟪yosida T hT hs f, g⟫ = ⟪f, yosida T hT hs g⟫ := by
  intro H₀ H₁ _ _ _ _ _ _ T hT s hs f g
  exact yosida_symm T hT hs f g

/-! ### `Y3` — the Yosida family commutes -/

/-- `Y3`, restated verbatim and discharged. -/
theorem route_Y3 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s) (hr : 0 < r),
      (yosida T hT hs).comp (yosida T hT hr) = (yosida T hT hr).comp (yosida T hT hs) := by
  intro H₀ H₁ _ _ _ _ _ _ T hT s r hs hr
  exact yosida_comp_comm T hT hs hr

/-! ### `Y4` — `L_s = J_s T†T` on `D(T†T)` -/

/-- `Y4`, restated verbatim and discharged. -/
theorem route_Y4 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) → ∀ {s : ℝ} (hs : 0 < s),
      ∀ f : (adjointComp T).domain,
        yosida T hT hs f = resolventCLM T hT hs (adjointComp T f) := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd s hs f
  exact yosida_apply_eq_resolventCLM_adjointComp T hT hd hs f

/-! ### `Y5` — `L_s f → T†T f` on `D(T†T)` -/

/-- `Y5`, restated verbatim and discharged. -/
theorem route_Y5 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) →
      ∀ (f : (adjointComp T).domain) {ε : ℝ}, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
          ‖yosida T hT hs f - adjointComp T f‖ < ε := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd f ε hε
  exact exists_delta_norm_yosida_sub_adjointComp_lt T hT hd f hε

end YosidaFamilyAudit

/-! ### Axiom reports -/

#print axioms FunctionalInequalities.Analysis.Semigroup.counterSet
#print axioms FunctionalInequalities.Analysis.Semigroup.counterCoeff
#print axioms FunctionalInequalities.Analysis.Semigroup.counterCoeff_nonneg
#print axioms FunctionalInequalities.Analysis.Semigroup.counterCoeff_of_mem
#print axioms FunctionalInequalities.Analysis.Semigroup.counterCoeff_of_notMem
#print axioms FunctionalInequalities.Analysis.Semigroup.counterFamily
#print axioms FunctionalInequalities.Analysis.Semigroup.counterFamily_nonneg
#print axioms FunctionalInequalities.Analysis.Semigroup.counterFamily_comm
#print axioms FunctionalInequalities.Analysis.Semigroup.exp_smul_one_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.counterFamily_exp_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.tendsto_one_div_nhdsGT_zero
#print axioms FunctionalInequalities.Analysis.Semigroup.tendsto_two_div_nhdsGT_zero
#print axioms FunctionalInequalities.Analysis.Semigroup.counterCoeff_one_div
#print axioms FunctionalInequalities.Analysis.Semigroup.counterCoeff_two_div
#print axioms FunctionalInequalities.Analysis.Semigroup.not_forall_exists_tendsto_exp_neg_smul
#print axioms FunctionalInequalities.Analysis.Semigroup.yosida_nonneg
#print axioms FunctionalInequalities.Analysis.Semigroup.yosida_symm
#print axioms FunctionalInequalities.Analysis.Semigroup.yosida_comp_comm
#print axioms FunctionalInequalities.Analysis.Semigroup.yosida_apply_eq_resolventCLM_adjointComp
#print axioms FunctionalInequalities.Analysis.Semigroup.exists_delta_norm_yosida_sub_adjointComp_lt
#print axioms YosidaFamilyAudit.route_Y0
#print axioms YosidaFamilyAudit.route_Y1
#print axioms YosidaFamilyAudit.route_Y2
#print axioms YosidaFamilyAudit.route_Y3
#print axioms YosidaFamilyAudit.route_Y4
#print axioms YosidaFamilyAudit.route_Y5

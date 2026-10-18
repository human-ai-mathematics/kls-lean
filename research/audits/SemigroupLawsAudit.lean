import FunctionalInequalities.Analysis.Semigroup.Generated.Laws

/-!
# Scope audit for `S7` (`P1`–`P8`) of the generated-semigroup route

The obligations `P1`–`P8` of `research/audits/GeneratedSemigroupRouteStatements.lean` — Part A of
the generated-semigroup route — are restated
here **verbatim**, copied character for character from that route contract, and discharged from the
hole-free module `Analysis/Semigroup/Generated/Laws.lean`. A renamed binder, a reordered hypothesis
or a weakened conclusion would fail to elaborate here.

No route hypothesis is discarded: every `P1`–`P8` statement is proved with exactly the data it
carries. The module lemmas differ from the route propositions only by currying (the route bundles
the typeclass parameters into one `∀`, the module takes them as section variables) and by naming
the `0 ≤ t` hypothesis.

Out of scope, deliberately absent: `G1`–`G3` (`S8`, the identification of the generator as `-T†T`),
which are Part B of the same route file and have the client `research/audits/GeneratorAudit.lean`. Nothing here is the
Markov property, Bakry–Émery `Γ`-calculus, a small-time heat estimate, localization or any step of
Buser's inequality.

The `#print axioms` reports at the end must all read `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open Filter Topology InnerProductSpace FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

namespace SemigroupLawsAudit

/-- **`P1`**, verbatim from the route contract (uniqueness of the limit defining `P_t`), discharged from
`Analysis/Semigroup/Generated/Laws.lean`. -/
theorem route_P1 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}, 0 ≤ t →
      ∀ (f g : H₀), (∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
        ‖NormedSpace.exp (-t • yosida T hT hs) f - g‖ < ε) →
        g = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd t ht f g hg
  exact FunctionalInequalities.Analysis.Semigroup.Generated.eq_apply_of_tendsto T hT hd ht f g hg

/-- **`P2`**, verbatim from the route contract (`P_t` is linear), discharged from
`Analysis/Semigroup/Generated/Laws.lean`. -/
theorem route_P2 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}, 0 ≤ t →
      ∀ (a : ℝ) (f g : H₀),
        FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (a • f + g) =
          a • FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f + FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t g := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd t ht a f g
  exact FunctionalInequalities.Analysis.Semigroup.Generated.map_smul_add T hT hd ht a f g

/-- **`P3`**, verbatim from the route contract (`P_t` is a contraction), discharged from
`Analysis/Semigroup/Generated/Laws.lean`. -/
theorem route_P3 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}, 0 ≤ t →
      ∀ f : H₀, ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f‖ ≤ ‖f‖ := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd t ht f
  exact FunctionalInequalities.Analysis.Semigroup.Generated.norm_apply_le T hT hd ht f

/-- **`P4`**, verbatim from the route contract (`P_t` is symmetric), discharged from
`Analysis/Semigroup/Generated/Laws.lean`. -/
theorem route_P4 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}, 0 ≤ t →
      ∀ f g : H₀, ⟪FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f, g⟫ = ⟪f, FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t g⟫ := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd t ht f g
  exact FunctionalInequalities.Analysis.Semigroup.Generated.symmetric T hT hd ht f g

/-- **`P5`**, verbatim from the route contract (`P_0 = 1`), discharged from
`Analysis/Semigroup/Generated/Laws.lean`. -/
theorem route_P5 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) (f : H₀),
      FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd 0 f = f := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd f
  exact FunctionalInequalities.Analysis.Semigroup.Generated.zero_time T hT hd f

/-- **`P6`**, verbatim from the route contract (the semigroup law `P_{t+u} = P_t P_u`), discharged from
`Analysis/Semigroup/Generated/Laws.lean`. -/
theorem route_P6 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t u : ℝ}, 0 ≤ t → 0 ≤ u →
      ∀ f : H₀, FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (t + u) f =
        FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd u f) := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd t u ht hu f
  exact FunctionalInequalities.Analysis.Semigroup.Generated.add_time T hT hd ht hu f

/-- **`P7`**, verbatim from the route contract (strong continuity at `0`), discharged from
`Analysis/Semigroup/Generated/Laws.lean`. -/
theorem route_P7 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) (f : H₀) {ε : ℝ}, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f - f‖ < ε := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd f ε hε
  exact FunctionalInequalities.Analysis.Semigroup.Generated.continuous_at_zero T hT hd f hε

/-- **`P8`**, verbatim from the route contract (strong continuity on `[0, ∞)`), discharged from
`Analysis/Semigroup/Generated/Laws.lean`. -/
theorem route_P8 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) (f : H₀),
      ContinuousOn (fun t : ℝ => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f) (Set.Ici 0) := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd f
  exact FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn T hT hd f

end SemigroupLawsAudit

/-! ## Axiom reports

Every report below must be exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms SemigroupLawsAudit.route_P1
#print axioms SemigroupLawsAudit.route_P2
#print axioms SemigroupLawsAudit.route_P3
#print axioms SemigroupLawsAudit.route_P4
#print axioms SemigroupLawsAudit.route_P5
#print axioms SemigroupLawsAudit.route_P6
#print axioms SemigroupLawsAudit.route_P7
#print axioms SemigroupLawsAudit.route_P8

#print axioms FunctionalInequalities.Analysis.Semigroup.eq_zero_of_forall_pos_lt
#print axioms FunctionalInequalities.Analysis.Semigroup.eq_zero_of_forall_le_mul
#print axioms FunctionalInequalities.Analysis.Semigroup.exp_neg_add_smul_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_exp_neg_smul_yosida_sub_le
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.eq_apply_of_tendsto
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.norm_apply_le
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.map_smul_add
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.map_sub
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.map_zero
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.map_smul
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.map_add
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.operator
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.operator_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.isSelfAdjoint_exp_neg_smul_yosida
#print axioms FunctionalInequalities.Analysis.Semigroup.inner_exp_neg_smul_yosida
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.symmetric
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.zero_time
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.add_time
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.displacement_le
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.continuous_at_zero
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn

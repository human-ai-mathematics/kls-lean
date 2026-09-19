import FunctionalInequalities.Analysis.Semigroup.Exponential.Limit

/-!
# Scope audit for `Y6`–`Y7` of the Yosida-limit route

The obligations `Y6` and `Y7` of `research/audits/YosidaLimitRouteStatements.lean` are restated
here **verbatim** — each proposition is copied character for character from that route snapshot,
including the implicit `{ε}` and `{s r}` binders of `Y7` — and discharged from the new hole-free
module `Analysis/Semigroup/Exponential/Limit.lean`. A renamed binder, a reordered hypothesis or a
weakened conclusion would fail to elaborate here.

`Y6` is the difference estimate `‖exp (-t • A) f - exp (-t • B) f‖ ≤ t ‖A f - B f‖` for commuting
nonnegative bounded operators, and `Y7` is the corrected abstract `S6`: the strong limit of
`exp (-t • L s hs)` as `s ↓ 0` under a Cauchy hypothesis on a dense set. **No hypothesis of
either proposition is discarded**: both nonnegativity assumptions of `Y6` supply one of the two
contraction estimates, commutation supplies the cancellation in the derivative of the
interpolation path, and `Y7` uses all four of its hypotheses.

Out of scope, deliberately absent: `Y0`–`Y5` (the counterexample and the properties of the actual
Yosida family `L_s = s⁻¹ (1 - J_s)`), `Y8` (`S6` for that family), `S7`–`S8` (the semigroup and
strong-continuity laws, and the identification of the generator), and every later gap of
`thm:logconcave-cheeger-poincare-comparison` — the Markov property, Bakry–Émery `Γ`-calculus,
small-time heat estimates and localization. The module mentions no unbounded operator `T`, no
resolvent and no adjoint. **Nothing here is Buser's inequality or any step of it.**

Two boundary cases follow the route items: `t = 0` in `Y6`, where both exponentials are the
identity and the bound reads `0 ≤ 0`, and `A = B` in `Y6`, where the bound reads `0 ≤ 0` for
every `t`.

The axiom reports at the end cover every public declaration of the new module and every theorem
of this client.
-/

noncomputable section

open InnerProductSpace FunctionalInequalities

open scoped RealInnerProductSpace

namespace SemigroupLimitAudit

/-! ### `Y6` — the difference estimate for two commuting nonnegative exponentials -/

/-- `Y6`, restated verbatim and discharged. No hypothesis is unused. -/
theorem route_Y6 :
    ∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (A B : H₀ →L[ℝ] H₀), (∀ f, 0 ≤ ⟪A f, f⟫) → (∀ f, 0 ≤ ⟪B f, f⟫) → A.comp B = B.comp A →
      ∀ t : ℝ, 0 ≤ t → ∀ f : H₀,
        ‖NormedSpace.exp (-t • A) f - NormedSpace.exp (-t • B) f‖ ≤ t * ‖A f - B f‖ := by
  intro H₀ _ _ _ A B hA hB hAB t ht f
  exact Analysis.Semigroup.norm_exp_neg_smul_sub_le A B hA hB hAB ht f

/-! ### `Y7` — the corrected abstract `S6` -/

/-- `Y7`, restated verbatim and discharged. No hypothesis is unused. -/
theorem route_Y7 :
    ∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (L : ∀ s : ℝ, 0 < s → H₀ →L[ℝ] H₀),
      (∀ (s : ℝ) (hs : 0 < s) (f : H₀), 0 ≤ ⟪L s hs f, f⟫) →
      (∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r), (L s hs).comp (L r hr) = (L r hr).comp (L s hs)) →
      ∀ D : Set H₀, Dense D →
        (∀ f ∈ D, ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ {s r : ℝ} (hs : 0 < s) (hr : 0 < r), s < δ → r < δ → ‖L s hs f - L r hr f‖ < ε) →
        ∀ (f : H₀) (t : ℝ), 0 ≤ t → ∃ g : H₀, ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖NormedSpace.exp (-t • L s hs) f - g‖ < ε := by
  intro H₀ _ _ _ L hL hcomm D hD hC f t ht
  exact Analysis.Semigroup.route_Y7 L hL hcomm D hD hC f t ht

/-! ### Boundary cases -/

/-- At `t = 0` both exponentials in `Y6` are the identity and the bound is `0 ≤ 0`. -/
theorem boundary_Y6_t_zero {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    [CompleteSpace H₀] (A B : H₀ →L[ℝ] H₀) (hA : ∀ f, 0 ≤ ⟪A f, f⟫) (hB : ∀ f, 0 ≤ ⟪B f, f⟫)
    (hAB : A.comp B = B.comp A) (f : H₀) :
    ‖NormedSpace.exp (-(0 : ℝ) • A) f - NormedSpace.exp (-(0 : ℝ) • B) f‖ = 0 := by
  have h := Analysis.Semigroup.norm_exp_neg_smul_sub_le A B hA hB hAB le_rfl f
  simp only [zero_mul] at h
  exact le_antisymm h (norm_nonneg _)

/-- For `A = B` the `Y6` bound reads `0 ≤ 0` for every `t ≥ 0`. -/
theorem boundary_Y6_eq {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    [CompleteSpace H₀] (A : H₀ →L[ℝ] H₀) (hA : ∀ f, 0 ≤ ⟪A f, f⟫) {t : ℝ} (ht : 0 ≤ t)
    (f : H₀) : ‖NormedSpace.exp (-t • A) f - NormedSpace.exp (-t • A) f‖ ≤ t * ‖A f - A f‖ :=
  Analysis.Semigroup.norm_exp_neg_smul_sub_le A A hA hA rfl ht f

end SemigroupLimitAudit

/-! ### Axiom reports

Every report below must be exactly `[propext, Classical.choice, Quot.sound]`. -/

section AxiomReports

open FunctionalInequalities.Analysis.Semigroup

-- Public declarations of `Analysis/Semigroup/Exponential/Limit.lean`.
#print axioms norm_exp_smul_apply_le_of_nonpos
#print axioms norm_exp_smul_neg_apply_le
#print axioms norm_exp_neg_smul_sub_le
#print axioms exists_limit_of_cauchy_along_pos
#print axioms exists_limit_exp_neg_smul
#print axioms FunctionalInequalities.Analysis.Semigroup.route_Y6
#print axioms FunctionalInequalities.Analysis.Semigroup.route_Y7

-- Theorems of this client.
#print axioms SemigroupLimitAudit.route_Y6
#print axioms SemigroupLimitAudit.route_Y7
#print axioms SemigroupLimitAudit.boundary_Y6_t_zero
#print axioms SemigroupLimitAudit.boundary_Y6_eq

end AxiomReports

import FunctionalInequalities.Analysis.Semigroup.Generated.Generator

/-!
# Scope audit for `G1` and `G3` (`S8`) of the generated-semigroup route

The obligations `G1` and `G3` of `research/audits/GeneratedSemigroupRouteStatements.lean` — the
part of Part B of the route recorded in
`research/decisions/2026-09-19-generated-semigroup-route.md` that was still open after `G2`
(`Analysis/Semigroup/Exponential/MeanValue.lean`) — are restated here **verbatim**, copied character for
character from that route snapshot, and discharged from the hole-free module
`Analysis/Semigroup/Generated/Generator.lean`. A renamed binder, a reordered hypothesis or a weakened
conclusion would fail to elaborate here.

`G1` is the uniformity on `[0, t]` of the `S6` convergence `exp (-τ • L_s) g → P_τ g`; `G3` is
`S8`, the generator identity `(P_t f - f)/t → -T†T f` on `D(T†T)`. Together with `G2` and with
`P1`–`P8` (`S7`, `research/audits/SemigroupLawsAudit.lean`) they close `S1`–`S8` of the
semigroup-generation route.

No route hypothesis is discarded: both statements are proved with exactly the data they carry.
The module lemmas differ from the route propositions only by currying (the route bundles the
typeclass parameters into one `∀`, the module takes them as section variables) and by naming the
`0 ≤ t` and `0 < ε` hypotheses. The module proves two intermediate results that are *stronger*
than the route asks — a `≤`-form of `G1` on `D(T†T)` and the quantitative
`‖P_t f - f + t • T†T f‖ ≤ (7 ε / 8) * t` behind `G3` — and the route statements are derived from
them; the verbatim restatements below are the route's own, unweakened.

Out of scope, deliberately absent: the Markov property (gap 2), Bakry–Émery `Γ`-calculus (gap 3),
a small-time heat estimate (gap 4), localization (gap 5) and every step of Buser's inequality.
`thm:logconcave-cheeger-poincare-comparison` gains no progress marker from `S7`–`S8`.

The `#print axioms` reports at the end must all read `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open Filter Topology InnerProductSpace FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

namespace GeneratorAudit

/-- **`G1`**, verbatim from the route snapshot (the `S6` convergence is uniform on `[0, t]`),
discharged from `Analysis/Semigroup/Generated/Generator.lean`. -/
theorem route_G1 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) (g : H₀) {t : ℝ}, 0 ≤ t →
      ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ → ∀ τ ∈ Set.Icc 0 t,
        ‖NormedSpace.exp (-τ • yosida T hT hs) g - semigroupApply T hT hd τ g‖ < ε := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd g t ht ε hε
  exact exists_delta_norm_exp_neg_smul_yosida_sub_semigroupApply_lt T hT hd g ht hε

/-- **`G3`** (`= S8`), verbatim from the route snapshot (the generator of `P_t` is `-T†T` on
`D(T†T)`), discharged from `Analysis/Semigroup/Generated/Generator.lean`. -/
theorem route_G3 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    (f : (adjointComp T).domain) {ε : ℝ}, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
        ‖t⁻¹ • (semigroupApply T hT hd t f - f) + adjointComp T f‖ < ε := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd f ε hε
  exact exists_delta_norm_inv_smul_semigroupApply_sub_self_add_adjointComp_lt T hT hd f hε

end GeneratorAudit

/-! ## Axiom reports

Every report below must be exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms GeneratorAudit.route_G1
#print axioms GeneratorAudit.route_G3

#print axioms FunctionalInequalities.Analysis.Semigroup.le_of_forall_pos_add_le
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_sub_le_add_norm_sub
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_exp_neg_smul_yosida_sub_semigroupApply_le
#print axioms FunctionalInequalities.Analysis.Semigroup.exists_delta_norm_exp_neg_smul_yosida_sub_semigroupApply_lt
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_semigroupApply_sub_self_add_smul_le
#print axioms FunctionalInequalities.Analysis.Semigroup.exists_delta_norm_inv_smul_semigroupApply_sub_self_add_adjointComp_lt

import FunctionalInequalities.Analysis.Semigroup.Yosida.Limit
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Scope audit for `Y8` of `YosidaLimitRouteStatements.lean`

The obligation `Y8` of `research/audits/Semigroup/YosidaLimitRouteStatements.lean` is restated here
**verbatim** — the proposition is copied character for character from that route file — and
discharged from the hole-free module `Analysis/Semigroup/Yosida/Limit.lean`, which composes `Y7`
(`SemigroupLimit.lean`) with `Y1`, `Y3`, `Y5` (`YosidaFamily.lean`) and the density of `D(T†T)`
(`dense_adjointComp_domain`, `VonNeumann.lean`). The obligations `Y0`–`Y5` and `Y6`–`Y7` of
`YosidaLimitRouteStatements.lean` are audited in `YosidaFamilyAudit.lean` and
`ExponentialLimitAudit.lean` respectively.

This closes `S6` of `GenerationRouteStatements.lean` for the concrete Yosida approximation; the
abstract `S6` of that file is false (`Analysis/Semigroup/Exponential/Counterexample.lean`) and is
not claimed.

Out of scope, deliberately absent: `S7` (the limit is a strongly continuous semigroup of
self-adjoint contractions) and `S8` (its generator is `T†T`) of `GenerationRouteStatements.lean`,
the Markov property, Bakry–Émery `Γ`-calculus, small-time heat estimates, localization and
Buser's inequality.
`thm:logconcave-cheeger-poincare-comparison` gains no progress marker.

The axiom reports at the end cover every public declaration of the new module and every theorem
of this client.
-/

noncomputable section

open InnerProductSpace FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

namespace YosidaLimitAudit

/-- `Y8` of `YosidaLimitRouteStatements.lean`, restated verbatim and discharged. -/
theorem route_Y8 :
    ∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) →
      ∀ (f : H₀) (t : ℝ), 0 ≤ t → ∃ g : H₀, ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖NormedSpace.exp (-t • yosida T hT hs) f - g‖ < ε := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd f t ht
  exact exists_limit_exp_neg_smul_yosida T hT hd f ht

/-- Boundary case `t = 0`: the exponentials are the identity and the limit is `f` itself. -/
theorem boundary_t_zero {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    [CompleteSpace H₀] [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (f : H₀) {s : ℝ} (hs : 0 < s) :
    NormedSpace.exp (-(0 : ℝ) • yosida T hT hs) f = f := by
  simp

end YosidaLimitAudit

/-! ### Axiom reports -/

#print axioms FunctionalInequalities.Analysis.Semigroup.yosida_cauchy_on_adjointComp_domain
#print axioms FunctionalInequalities.Analysis.Semigroup.exists_limit_exp_neg_smul_yosida
#print axioms YosidaLimitAudit.route_Y8
#print axioms YosidaLimitAudit.boundary_t_zero

import FunctionalInequalities.Analysis.Semigroup.Exponential.MeanValue

/-!
# Scope audit for `G2` of `GeneratedRouteStatements.lean`

The obligation `G2` of `research/audits/Semigroup/GeneratedRouteStatements.lean` is restated here
**verbatim** — the proposition is copied character for character from that route file,
including the implicit `{t}` and `{C}` binders — and discharged from the hole-free module
`Analysis/Semigroup/Exponential/MeanValue.lean`. A renamed binder, a reordered hypothesis or a weakened
conclusion would fail to elaborate here.

The obligation is the mean value bound: for a bounded operator `A`, a vector `f`, `0 ≤ t` and a
real `C`, if `‖exp (-τ • A) (A f) - A f‖ ≤ C` on `[0, t]`, then
`‖exp (-t • A) f - f + t • A f‖ ≤ C * t`.

**One route hypothesis is discarded**: the `InnerProductSpace ℝ H₀` instance. The proof uses no
inner product — no symmetry, no nonnegativity of `A`, no Cauchy–Schwarz — so the module proves
`norm_exp_neg_smul_sub_add_smul_le` for an arbitrary `[NormedSpace ℝ H₀] [CompleteSpace H₀]`, and
the audit takes and drops the stronger instance, as the audits of `GenerationRouteStatements.lean`
and `VonNeumannRouteStatements.lean` do for their superfluous hypotheses. The
hypotheses `0 ≤ t` and completeness are both used: completeness makes `H₀ →L[ℝ] H₀` complete, so
that `NormedSpace.exp` is differentiable, and `0 ≤ t` makes `[0, t]` the interval of the mean
value inequality with `t` as its right endpoint. `C` is **not** assumed nonnegative.

Out of scope, deliberately absent: `G1` (uniformity on `[0, t]` of the strong Yosida
convergence), `G3` (the generator of the limit semigroup is `-T†T`) and `P1`–`P8` (the semigroup
and strong-continuity laws) of `GeneratedRouteStatements.lean`, and every later step of
`thm:logconcave-cheeger-poincare-comparison` — the Markov property, Bakry–Émery `Γ`-calculus,
small-time heat estimates and localization. The module mentions no unbounded operator `T`, no
adjoint, no resolvent and no Yosida approximation. **Nothing here is Buser's inequality or any
step of it.**

One boundary case follows the route item: `t = 0`, where the left side is `‖f - f + 0‖ = 0`, the
right side is `C * 0 = 0`, and the bound holds for every `C`, including negative `C`.

The axiom reports at the end cover every public declaration of the new module and every theorem
of this client.
-/

noncomputable section

open FunctionalInequalities

namespace ExpMeanValueAudit

/-! ### The mean value bound -/

/-- `G2` of `GeneratedRouteStatements.lean`, restated verbatim and discharged. The
`InnerProductSpace ℝ H₀` hypothesis is taken and not used; `0 ≤ t` and completeness are used. -/
theorem route_G2 :
    ∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (A : H₀ →L[ℝ] H₀) (f : H₀) {t : ℝ}, 0 ≤ t → ∀ {C : ℝ},
      (∀ τ ∈ Set.Icc 0 t, ‖NormedSpace.exp (-τ • A) (A f) - A f‖ ≤ C) →
        ‖NormedSpace.exp (-t • A) f - f + t • A f‖ ≤ C * t := by
  intro H₀ _ _ _ A f t ht C hC
  exact Analysis.Semigroup.norm_exp_neg_smul_sub_add_smul_le A f ht hC

/-! ### Boundary case -/

/-- `t = 0`: both sides of the mean value bound are `0`, for every `C` — the hypothesis on
`[0, 0]` is then only the statement `‖exp 0 (A f) - A f‖ = 0 ≤ C`, and no sign assumption on `C`
is made. -/
theorem boundary_G2_t_zero {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    [CompleteSpace H₀] (A : H₀ →L[ℝ] H₀) (f : H₀) {C : ℝ}
    (hC : ∀ τ ∈ Set.Icc (0 : ℝ) 0, ‖NormedSpace.exp (-τ • A) (A f) - A f‖ ≤ C) :
    ‖NormedSpace.exp (-(0 : ℝ) • A) f - f + (0 : ℝ) • A f‖ ≤ C * 0 :=
  Analysis.Semigroup.norm_exp_neg_smul_sub_add_smul_le A f le_rfl hC

end ExpMeanValueAudit

/-! ### Axiom reports

Every report below must be exactly `[propext, Classical.choice, Quot.sound]`. -/

section AxiomReports

open FunctionalInequalities.Analysis.Semigroup

-- Public declarations of `Analysis/Semigroup/Exponential/MeanValue.lean`.
#print axioms hasDerivAt_exp_neg_smul_path
#print axioms norm_exp_neg_smul_sub_add_smul_le

-- Theorems of this client.
#print axioms ExpMeanValueAudit.route_G2
#print axioms ExpMeanValueAudit.boundary_G2_t_zero

end AxiomReports

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if env.contains `FunctionalInequalities.Analysis.Semigroup.route_G2 then
    throwError "The route-only production wrapper must not survive"

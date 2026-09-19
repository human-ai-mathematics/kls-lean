import FunctionalInequalities.Analysis.Semigroup.Resolvent.Limit
import FunctionalInequalities.Analysis.Semigroup.VonNeumann
import FunctionalInequalities.Analysis.Semigroup.Exponential.Contraction
import FunctionalInequalities.Analysis.Semigroup.Yosida.Approximation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Route statements: strong convergence of the Yosida exponentials (`S6`)

**This file contains only `#check`s.  A proposition that type-checks is not a proof.**  It declares
nothing, proves nothing, and introduces no placeholder axiom.  Each proposition below is an
obligation of the route recorded in `research/decisions/2026-09-19-yosida-limit-route.md`, and **at
the time of this route snapshot none of `Y0`–`Y8` had been proved**.

## The target, and a correction to the earlier route

`S6` of `SemigroupGenerationRouteStatements.lean` asked for the strong convergence of
`exp (-t • L s) f` as `s ↓ 0` for an **abstract** family `L : ℝ → H₀ →L[ℝ] H₀` assumed only
nonnegative and commuting.  **That abstract statement is false**: `L s = c s • 1` with `c` taking the
values `0` and `1` on two sequences accumulating at `0⁺` is nonnegative and commuting, and
`exp (-t • L s) f = exp (-t c s) • f` has no limit.  `Y0` states this counterexample so the correction
is on record rather than silently absorbed.  The route file `SemigroupGenerationRouteStatements.lean`
is kept byte-unchanged.

The correct statement needs a **Cauchy hypothesis on a dense set**: `Y7` is the corrected abstract
`S6`, and `Y8` is `S6` for the actual Yosida approximation
`L_s = s⁻¹ (1 - J_s)` (`Analysis.Semigroup.yosida`), where the dense set is `D(T†T)` (`V4`) and the
Cauchy property comes from `L_s f → T†T f` (`Y5`, from `V5` and `R2`).

## Deliberately out of scope

`S7` (semigroup and strong-continuity laws of the limit) and `S8` (the generator is `T†T`) are not
stated.  Nothing here is the Markov property, Bakry–Émery calculus, a heat estimate or any step of
Buser's inequality; `thm:logconcave-cheeger-poincare-comparison` gains no progress marker.

## Conventions

`⟪x, y⟫` is the real inner product.  `resolventCLM T hT hs` is `J_s`; `yosida T hT hs` is `L_s`
with `yosida_apply : L_s f = s⁻¹ • (f - J_s f)`; `adjointComp T` is `T†T` with domain
`adjointCompDomain T ⊓ T.domain`, so `⟨f, f.2.2⟩ : T.domain` for `f : (adjointComp T).domain`.
Limits `s ↓ 0` are written in `ε`–`δ` form because `resolventCLM` and `yosida` carry the proof
`0 < s` as an argument; `Y0` alone uses `Tendsto` and `𝓝[>] 0` to match the original `S6` text.
Families are written `L : ∀ s : ℝ, 0 < s → H₀ →L[ℝ] H₀` for the same reason.
-/

noncomputable section

open Filter Topology InnerProductSpace FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

/-! ### Proved inputs, for reference -/

#check @FunctionalInequalities.Analysis.Semigroup.norm_exp_neg_smul_apply_le
#check @FunctionalInequalities.Analysis.Semigroup.resolventCLM_comp_comm
#check @FunctionalInequalities.Analysis.Semigroup.exists_delta_norm_resolventCLM_sub_lt
#check @FunctionalInequalities.Analysis.Semigroup.sub_resolvent_eq_smul
#check @FunctionalInequalities.Analysis.Semigroup.dense_adjointComp_domain
#check @FunctionalInequalities.Analysis.Semigroup.yosida_apply
#check @hasDerivAt_exp_smul_const
#check @Commute.exp_right
#check @norm_image_sub_le_of_norm_deriv_le_segment'

/-! ## Part A — the Yosida family -/

/-! ### `Y0` — the abstract `S6` is false

The original `S6`, specialised to `H₀ = ℝ`, fails: nonnegativity and commutation alone do not force
`exp (-t • L s) f` to converge.  Take `L s = c s • 1` with `c s = 1` when `s = 1/n` for some `n` and
`c s = 0` otherwise, `f = 1`, `t = 1`: the values `e⁻¹` and `1` both occur along sequences `s ↓ 0`. -/

#check (¬ (∀ (L : ℝ → ℝ →L[ℝ] ℝ),
      (∀ s : ℝ, 0 < s → ∀ f, 0 ≤ ⟪L s f, f⟫) →
      (∀ s r : ℝ, 0 < s → 0 < r → (L s).comp (L r) = (L r).comp (L s)) →
      (∀ f : ℝ, ∀ t : ℝ, 0 ≤ t →
        ∃ g : ℝ, Tendsto (fun s : ℝ => NormedSpace.exp (-t • L s) f) (𝓝[>] 0) (𝓝 g))))

/-! ### `Y1` — `L_s` is nonnegative

`⟪L_s f, f⟫ = s⁻¹ (‖f‖² - ⟪J_s f, f⟫) ≥ 0` since `⟪J_s f, f⟫ ≤ ‖J_s f‖ ‖f‖ ≤ ‖f‖²`
(`norm_resolventCLM_le`). -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀),
      0 ≤ ⟪yosida T hT hs f, f⟫)

/-! ### `Y2` — `L_s` is symmetric

From `resolventCLM_symm`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f g : H₀),
      ⟪yosida T hT hs f, g⟫ = ⟪f, yosida T hT hs g⟫)

/-! ### `Y3` — the Yosida family commutes

From `resolventCLM_comp_comm` (`R3`): `L_s L_r = s⁻¹ r⁻¹ (1 - J_s - J_r + J_s J_r)` is symmetric
in `s, r`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s) (hr : 0 < r),
      (yosida T hT hs).comp (yosida T hT hr) = (yosida T hT hr).comp (yosida T hT hs))

/-! ### `Y4` — `L_s = J_s T†T` on `D(T†T)`

`V5` (`sub_resolvent_eq_smul`) rewritten through `yosida_apply`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) → ∀ {s : ℝ} (hs : 0 < s),
      ∀ f : (adjointComp T).domain,
        yosida T hT hs f = resolventCLM T hT hs (adjointComp T f))

/-! ### `Y5` — `L_s f → T†T f` on `D(T†T)`

`Y4` and `R2` (`exists_delta_norm_resolventCLM_sub_lt`) applied to the vector `T†T f`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) →
      ∀ (f : (adjointComp T).domain) {ε : ℝ}, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
          ‖yosida T hT hs f - adjointComp T f‖ < ε)

/-! ## Part B — abstract semigroup limits (bounded operators only) -/

/-! ### `Y6` — two commuting nonnegative exponentials differ by at most `t ‖A f - B f‖`

For bounded nonnegative `A, B` that commute and `t ≥ 0`,
`‖exp (-t • A) f - exp (-t • B) f‖ ≤ t ‖A f - B f‖`.  Proof: `φ τ = exp (-τ • A) (exp (-(t - τ) • B) f)`
has `φ' τ = exp (-τ • A) (exp (-(t - τ) • B) ((B - A) f))` (product rule, `hasDerivAt_exp_smul_const`,
and `Commute.exp_right` to move `A` past `exp (-(t - τ) • B)`), whose norm is at most `‖(B - A) f‖` by
`S5` (`norm_exp_neg_smul_apply_le`) twice; the mean value inequality
`norm_image_sub_le_of_norm_deriv_le_segment'` on `[0, t]` gives the bound for `φ t - φ 0`. -/

#check (∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (A B : H₀ →L[ℝ] H₀), (∀ f, 0 ≤ ⟪A f, f⟫) → (∀ f, 0 ≤ ⟪B f, f⟫) → A.comp B = B.comp A →
      ∀ t : ℝ, 0 ≤ t → ∀ f : H₀,
        ‖NormedSpace.exp (-t • A) f - NormedSpace.exp (-t • B) f‖ ≤ t * ‖A f - B f‖)

/-! ### `Y7` — the corrected abstract `S6`

A family `L s hs` of nonnegative commuting bounded operators whose values `L s hs f` are Cauchy as
`s ↓ 0` for every `f` in a dense set `D` has `exp (-t • L s hs) f` convergent as `s ↓ 0` for **every**
`f` and every `t ≥ 0`.  Proof: for `f ∈ D`, `Y6` makes `exp (-t • L s hs) f` Cauchy, so it converges
(`H₀` complete); for general `f` approximate by `g ∈ D` and use the uniform contraction bound `S5`
on `f - g` (`ε/3` argument), then completeness again. -/

#check (∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (L : ∀ s : ℝ, 0 < s → H₀ →L[ℝ] H₀),
      (∀ (s : ℝ) (hs : 0 < s) (f : H₀), 0 ≤ ⟪L s hs f, f⟫) →
      (∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r), (L s hs).comp (L r hr) = (L r hr).comp (L s hs)) →
      ∀ D : Set H₀, Dense D →
        (∀ f ∈ D, ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ {s r : ℝ} (hs : 0 < s) (hr : 0 < r), s < δ → r < δ → ‖L s hs f - L r hr f‖ < ε) →
        ∀ (f : H₀) (t : ℝ), 0 ≤ t → ∃ g : H₀, ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖NormedSpace.exp (-t • L s hs) f - g‖ < ε)

/-! ### `Y8` — `S6` for the Yosida approximation

For `T` closed and densely defined, `exp (-t • L_s) f` converges as `s ↓ 0` for every `f : H₀` and
`t ≥ 0`.  This is `Y7` applied to `L s hs = yosida T hT hs` with `D = D(T†T)`: nonnegativity `Y1`,
commutation `Y3`, density `V4` (`dense_adjointComp_domain`), and the Cauchy property from `Y5`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) →
      ∀ (f : H₀) (t : ℝ), 0 ≤ t → ∃ g : H₀, ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖NormedSpace.exp (-t • yosida T hT hs) f - g‖ < ε)

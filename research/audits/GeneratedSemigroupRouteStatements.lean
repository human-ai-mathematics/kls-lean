import FunctionalInequalities.Analysis.Semigroup.Generated.Basic
import FunctionalInequalities.Analysis.Semigroup.Exponential.Limit
import FunctionalInequalities.Analysis.Semigroup.Yosida.Family

/-!
# Route statements: the generated semigroup (`S7`) and its generator (`S8`)

**This file contains only `#check`s.  A proposition that type-checks is not a proof.**  It declares
nothing, proves nothing, and introduces no placeholder axiom.  Each proposition below is an
obligation of the route recorded in `research/decisions/2026-09-19-generated-semigroup-route.md`,
and **at the time of this route snapshot none of `P1`–`P8`, `G1`–`G3` had been proved**.

## The target

`S1`–`S6` of the semigroup-generation route are proved.  `Analysis/Semigroup/Generated/Basic.lean` names
the `S6` limit: `P_t f = semigroupApply T hT hd t f` is the strong limit of `exp (-t • L_s) f` as
`s ↓ 0` (`semigroupApply_spec`), for `T` closed and densely defined and `t ≥ 0`.  What remains of
the route is

* **`S7`** (`P1`–`P8`): `P_t` is linear and a contraction, symmetric, `P_0 = 1`, `P_{t+u} = P_t P_u`,
  and `t ↦ P_t f` is continuous on `[0, ∞)` — a strongly continuous semigroup of self-adjoint
  contractions;
* **`S8`** (`G1`–`G3`): on `D(T†T)`, `(P_t f - f)/t → -T†T f` as `t ↓ 0`, i.e. the generator is
  `-T†T`.

All of it is general real Hilbert space material with no measure, no log-concavity and no KLS
content.

## Deliberately out of scope

Nothing here is the Markov property (gap 2), Bakry–Émery `Γ`-calculus (gap 3), a small-time heat
estimate (gap 4), localization (gap 5) or any step of Buser's inequality.  Even with `S7`–`S8`
proved, `thm:logconcave-cheeger-poincare-comparison` gains no progress marker: the semigroup is
only the first of the four prerequisites recorded for it.

## Conventions

`⟪x, y⟫` is the real inner product.  `L_s = yosida T hT hs`, `P t f = semigroupApply T hT hd t f`
(equal to `f` for `t < 0` by convention, so every statement below carries `0 ≤ t`).  Limits are in
`ε`–`δ` form because `yosida` carries the proof `0 < s` as an argument.  `adjointComp T` is `T†T`;
for `f : (adjointComp T).domain`, `(f : H₀)` is the vector and `adjointComp T f` is `T†T f`.
-/

noncomputable section

open Filter Topology InnerProductSpace FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

/-! ### Proved inputs, for reference -/

#check @FunctionalInequalities.Analysis.Semigroup.semigroupApply_spec
#check @FunctionalInequalities.Analysis.Semigroup.norm_exp_neg_smul_apply_le
#check @FunctionalInequalities.Analysis.Semigroup.norm_exp_neg_smul_sub_le
#check @FunctionalInequalities.Analysis.Semigroup.yosida_nonneg
#check @FunctionalInequalities.Analysis.Semigroup.yosida_symm
#check @FunctionalInequalities.Analysis.Semigroup.yosida_comp_comm
#check @FunctionalInequalities.Analysis.Semigroup.exists_delta_norm_yosida_sub_adjointComp_lt
#check @FunctionalInequalities.Analysis.Semigroup.dense_adjointComp_domain
#check @NormedSpace.exp_add_of_commute
#check @NormedSpace.exp_zero

/-! ## Part A — `S7`: the semigroup laws -/

/-! ### `P1` — the limit is unique

Any `g` with `exp (-t • L_s) f → g` as `s ↓ 0` equals `P_t f`.  Triangle inequality against
`semigroupApply_spec`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}, 0 ≤ t →
      ∀ (f g : H₀), (∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
        ‖NormedSpace.exp (-t • yosida T hT hs) f - g‖ < ε) →
        g = semigroupApply T hT hd t f)

/-! ### `P2` — `P_t` is linear

`exp (-t • L_s)` is linear and limits are unique (`P1`). -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}, 0 ≤ t →
      ∀ (a : ℝ) (f g : H₀),
        semigroupApply T hT hd t (a • f + g) =
          a • semigroupApply T hT hd t f + semigroupApply T hT hd t g)

/-! ### `P3` — `P_t` is a contraction

`‖exp (-t • L_s) f‖ ≤ ‖f‖` (`S5`, `norm_exp_neg_smul_apply_le` with `yosida_nonneg`) passes to the
limit. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}, 0 ≤ t →
      ∀ f : H₀, ‖semigroupApply T hT hd t f‖ ≤ ‖f‖)

/-! ### `P4` — `P_t` is symmetric

`L_s` is symmetric (`yosida_symm`), hence self-adjoint as a `ContinuousLinearMap`
(`LinearMap.IsSymmetric.isSelfAdjoint` / `ContinuousLinearMap.isSelfAdjoint_iff'`), so
`exp (-t • L_s)` is self-adjoint (`IsSelfAdjoint.exp` or `star_exp`, star being the adjoint on
`H₀ →L[ℝ] H₀`), which gives `⟪exp (-t • L_s) f, g⟫ = ⟪f, exp (-t • L_s) g⟫`
(`ContinuousLinearMap.adjoint_inner_left`); pass to the limit using continuity of the inner
product. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t : ℝ}, 0 ≤ t →
      ∀ f g : H₀, ⟪semigroupApply T hT hd t f, g⟫ = ⟪f, semigroupApply T hT hd t g⟫)

/-! ### `P5` — `P_0 = 1`

`exp (-0 • L_s) = 1` (`NormedSpace.exp_zero`), so the constant family converges to `f`; `P1`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) (f : H₀),
      semigroupApply T hT hd 0 f = f)

/-! ### `P6` — the semigroup law

`exp (-(t + u) • L_s) = exp (-t • L_s) * exp (-u • L_s)` (`NormedSpace.exp_add_of_commute`, the two
scalar multiples of `L_s` commute).  Then `exp (-t • L_s) (exp (-u • L_s) f) → P_t (P_u f)`: split
`‖exp (-t • L_s) (exp (-u • L_s) f) - P_t (P_u f)‖ ≤ ‖exp (-u • L_s) f - P_u f‖ +
‖exp (-t • L_s) (P_u f) - P_t (P_u f)‖` using the contraction `S5` on the first term; conclude by
`P1`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) {t u : ℝ}, 0 ≤ t → 0 ≤ u →
      ∀ f : H₀, semigroupApply T hT hd (t + u) f =
        semigroupApply T hT hd t (semigroupApply T hT hd u f))

/-! ### `P7` — strong continuity at `0`

For `f ∈ D(T†T)`: `‖exp (-t • L_s) f - f‖ ≤ t ‖L_s f‖` (`Y6` with `B = 0` and `exp_zero`), and
`‖L_s f‖ ≤ ‖T†T f‖ + 1` for small `s` (`Y5`), so `‖P_t f - f‖ ≤ t (‖T†T f‖ + 1)` in the limit.  For
general `f` approximate by `g ∈ D(T†T)` (`dense_adjointComp_domain`) and use the contraction `P3`:
`‖P_t f - f‖ ≤ 2 ‖f - g‖ + ‖P_t g - g‖`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) (f : H₀) {ε : ℝ}, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → ‖semigroupApply T hT hd t f - f‖ < ε)

/-! ### `P8` — strong continuity on `[0, ∞)`

`t ↦ P_t f` is continuous on `Set.Ici 0`.  For `t₀ ≤ t`: `P_t f - P_{t₀} f = P_{t₀} (P_{t - t₀} f - f)`
(`P6`), so `‖P_t f - P_{t₀} f‖ ≤ ‖P_{t - t₀} f - f‖` (`P3`) and `P7` applies; for `t ≤ t₀` exchange the
roles.  `Metric.continuousOn_iff`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) (f : H₀),
      ContinuousOn (fun t : ℝ => semigroupApply T hT hd t f) (Set.Ici 0))

/-! ## Part B — `S8`: the generator is `-T†T` -/

/-! ### `G1` — the `S6` convergence is uniform on `[0, t]`

For `g ∈ D(T†T)`, `Y6` gives `‖exp (-τ • L_s) g - exp (-τ • L_r) g‖ ≤ τ ‖L_s g - L_r g‖ ≤
t ‖L_s g - L_r g‖`, uniformly in `τ ∈ [0, t]`, so the Cauchy property and hence the convergence to
`P_τ g` are uniform in `τ`; for general `g` approximate in `D(T†T)` and use the contraction (`S5`
and `P3`). -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀)) (g : H₀) {t : ℝ}, 0 ≤ t →
      ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ → ∀ τ ∈ Set.Icc 0 t,
        ‖NormedSpace.exp (-τ • yosida T hT hs) g - semigroupApply T hT hd τ g‖ < ε)

/-! ### `G2` — the mean value bound for `exp (-t • A) f - f + t • A f`

For a bounded `A`, `φ τ = exp (-τ • A) f - f + τ • A f` has `φ' τ = A f - exp (-τ • A) (A f)`
(`hasDerivAt_exp_smul_const'`), so if `‖exp (-τ • A) (A f) - A f‖ ≤ C` on `[0, t]` then
`‖φ t - φ 0‖ ≤ C t` (`norm_image_sub_le_of_norm_deriv_le_segment'`).  No nonnegativity of `A` is
needed. -/

#check (∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (A : H₀ →L[ℝ] H₀) (f : H₀) {t : ℝ}, 0 ≤ t → ∀ {C : ℝ},
      (∀ τ ∈ Set.Icc 0 t, ‖NormedSpace.exp (-τ • A) (A f) - A f‖ ≤ C) →
        ‖NormedSpace.exp (-t • A) f - f + t • A f‖ ≤ C * t)

/-! ### `G3` — `S8`: the generator is `-T†T` on `D(T†T)`

For `f ∈ D(T†T)` and `ε > 0` there is `δ > 0` with `‖(P_t f - f)/t + T†T f‖ < ε` for `0 < t < δ`.
Proof: put `g = T†T f`.  Choose `δ` with `‖P_τ g - g‖ < ε/3` for `τ < δ` (`P7`).  For `0 < t < δ` and
`s` small, `‖exp (-τ • L_s) (L_s f) - L_s f‖ ≤ 2 ‖L_s f - g‖ + ‖exp (-τ • L_s) g - P_τ g‖ +
‖P_τ g - g‖ < ε` for all `τ ∈ [0, t]` (`Y5`, `G1`, `S5`), so `G2` with `A = L_s` gives
`‖exp (-t • L_s) f - f + t • L_s f‖ ≤ ε t`; let `s ↓ 0` (`semigroupApply_spec`, `Y5`) to get
`‖P_t f - f + t • g‖ ≤ ε t`, and divide by `t`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    (f : (adjointComp T).domain) {ε : ℝ}, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
        ‖t⁻¹ • (semigroupApply T hT hd t f - f) + adjointComp T f‖ < ε)

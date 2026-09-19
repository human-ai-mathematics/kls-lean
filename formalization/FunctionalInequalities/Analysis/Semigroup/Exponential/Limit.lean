import FunctionalInequalities.Analysis.Semigroup.Exponential.Contraction
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Strong limits of exponentials of commuting nonnegative bounded operators

`Y6` and `Y7` of the Yosida-limit route
(`research/decisions/2026-09-19-yosida-limit-route.md`, statements in
`research/audits/YosidaLimitRouteStatements.lean`), proved here and restated verbatim as
`route_Y6` and `route_Y7`.

* `Y6` (`norm_exp_neg_smul_sub_le`) is the analytic core: for bounded **commuting** nonnegative
  operators `A, B` on a real Hilbert space and `t ≥ 0`,
  `‖exp (-t • A) f - exp (-t • B) f‖ ≤ t ‖A f - B f‖`, pointwise in `f`.
* `Y7` (`exists_limit_exp_neg_smul`) is the **corrected** abstract `S6`: a family `L s hs` of
  nonnegative commuting bounded operators whose values are Cauchy as `s ↓ 0` on a dense set has
  `exp (-t • L s hs) f` convergent as `s ↓ 0` for every `f` and every `t ≥ 0`. The Cauchy
  hypothesis on a dense set is what `S6` of
  `research/audits/SemigroupGenerationRouteStatements.lean` was missing; `Y0` of the route file
  records the counterexample to the uncorrected statement.

## Proof of `Y6`: differentiate the interpolation path

With `φ τ = exp (τ • (-A)) (exp ((τ - t) • B) f)` the product rule
(`HasDerivAt.clm_apply`, `hasDerivAt_exp_smul_const`) gives
`φ' τ = exp (τ • (-A)) ((-A) (exp ((τ - t) • B) f)) + exp (τ • (-A)) (exp ((τ - t) • B) (B f))`,
and `Commute.exp_right` moves `A` past `exp ((τ - t) • B)`, so
`φ' τ = exp (τ • (-A)) (exp ((τ - t) • B) (B f - A f))`. On `[0, t]` both exponentials are
contractions by `S5` (`norm_exp_neg_smul_apply_le`), so `‖φ' τ‖ ≤ ‖A f - B f‖`, and the mean value
inequality `norm_image_sub_le_of_norm_deriv_le_segment'` applied to `φ t - φ 0` is the claim. No
operator norm is ever estimated: everything is pointwise in `f`, which avoids the
`ContinuousLinearMap` norm instance diamond.

## Proof of `Y7`: Cauchy on a dense set, then everywhere

`exists_limit_of_cauchy_along_pos` is the completeness step, stated for an arbitrary family
`u : ∀ s : ℝ, 0 < s → H₀` in a complete normed group: an `ε`–`δ` Cauchy family as `s ↓ 0`
converges. It is proved by extracting the sequence `u (1 / (n + 1))`, which is `CauchySeq`, and
comparing an arbitrary small `s` with a far enough member of that sequence. `Y6` makes the family
`s ↦ exp (-t • L s hs) v` Cauchy for `v` in the dense set, and the contraction bound `S5` upgrades
this to every `f` by an `ε/3` argument through a nearby `v ∈ D`.

## Route hypotheses used, and the general form of the lemmas

Every hypothesis of `Y6` is used: nonnegativity of `A` and of `B` each supply one of the two
contraction estimates on `‖φ' τ‖`, commutation supplies the cancellation in `φ'`, and `0 ≤ t` is
needed both for the contraction estimates and for `[0, t]` to be the correct interval. `Y7` uses
all four of its hypotheses through `Y6` and `S5`. The module lemmas differ from the route
propositions only in binder shape (explicit `ε`, `s`, `r` instead of the route's implicit ones)
and in that `exists_limit_of_cauchy_along_pos` is stated for a bare complete normed group; the
verbatim route statements are `route_Y6` and `route_Y7`.

## Deliberately out of scope

`Y8` (`S6` for the actual Yosida approximation `L_s = s⁻¹ (1 - J_s)`) is **not** proved here: this
module mentions no unbounded operator `T`, no resolvent and no adjoint. `S7` (the semigroup and
strong-continuity laws of the limit) and `S8` (the generator is `T†T`) are not stated. Nothing
here is the Markov property, Bakry–Émery calculus, a heat kernel estimate or any step of Buser's
inequality; `thm:logconcave-cheeger-poincare-comparison` gains no progress marker from this
module.
-/

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

section Contraction

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]

/-- Restatement of `S5` (`norm_exp_neg_smul_apply_le`) for a **nonpositive** scalar: if `L` is
bounded and nonnegative and `c ≤ 0`, then `exp (c • L)` is a pointwise contraction. -/
theorem norm_exp_smul_apply_le_of_nonpos (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) {c : ℝ}
    (hc : c ≤ 0) (f : H₀) : ‖NormedSpace.exp (c • L) f‖ ≤ ‖f‖ := by
  have h := norm_exp_neg_smul_apply_le L hL (neg_nonneg.mpr hc) f
  rwa [neg_neg] at h

/-- Restatement of `S5` (`norm_exp_neg_smul_apply_le`) with the sign on the **operator**: if `L`
is bounded and nonnegative and `0 ≤ c`, then `exp (c • (-L))` is a pointwise contraction. This is
the normal form produced by `hasDerivAt_exp_smul_const` along the orbit of `-L`. -/
theorem norm_exp_smul_neg_apply_le (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) {c : ℝ}
    (hc : 0 ≤ c) (f : H₀) : ‖NormedSpace.exp (c • (-L)) f‖ ≤ ‖f‖ := by
  have h := norm_exp_neg_smul_apply_le L hL hc f
  rwa [neg_smul, ← smul_neg] at h

/-- **`Y6`.** Two commuting bounded nonnegative operators have exponentials that differ, pointwise
at `f` and for `t ≥ 0`, by at most `t ‖A f - B f‖`:
`‖exp (-t • A) f - exp (-t • B) f‖ ≤ t * ‖A f - B f‖`.

The proof differentiates the interpolation path `τ ↦ exp (τ • (-A)) (exp ((τ - t) • B) f)` on
`[0, t]` and applies the mean value inequality; see the module docstring. Every hypothesis is
used. -/
theorem norm_exp_neg_smul_sub_le (A B : H₀ →L[ℝ] H₀) (hA : ∀ f, 0 ≤ ⟪A f, f⟫)
    (hB : ∀ f, 0 ≤ ⟪B f, f⟫) (hAB : A.comp B = B.comp A) {t : ℝ} (ht : 0 ≤ t) (f : H₀) :
    ‖NormedSpace.exp (-t • A) f - NormedSpace.exp (-t • B) f‖ ≤ t * ‖A f - B f‖ := by
  have hcomm : Commute A B := hAB
  have hmove : ∀ (c : ℝ) (v : H₀),
      A (NormedSpace.exp (c • B) v) = NormedSpace.exp (c • B) (A v) := by
    intro c v
    have h : Commute A (NormedSpace.exp (c • B)) := (hcomm.smul_right c).exp_right
    exact congrArg (fun M : H₀ →L[ℝ] H₀ => M v) h
  have hderiv : ∀ τ : ℝ, HasDerivAt
      (fun σ : ℝ => NormedSpace.exp (σ • (-A)) (NormedSpace.exp ((σ - t) • B) f))
      (NormedSpace.exp (τ • (-A)) (NormedSpace.exp ((τ - t) • B) (B f - A f))) τ := by
    intro τ
    have hc : HasDerivAt (fun σ : ℝ => NormedSpace.exp (σ • (-A)))
        (NormedSpace.exp (τ • (-A)) * (-A)) τ := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) τ
    have hE : HasDerivAt (fun σ : ℝ => NormedSpace.exp ((σ - t) • B))
        (NormedSpace.exp ((τ - t) • B) * B) τ := by
      have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) B (τ - t)).scomp τ
        ((hasDerivAt_id τ).sub_const t)
      simpa [Function.comp_def] using h
    have hu : HasDerivAt (fun σ : ℝ => NormedSpace.exp ((σ - t) • B) f)
        (NormedSpace.exp ((τ - t) • B) (B f)) τ := by
      have h := hE.clm_apply (hasDerivAt_const τ f)
      simpa using h
    refine (hc.clm_apply hu).congr_deriv ?_
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, neg_apply, hmove]
    simp only [map_sub, map_neg]
    abel
  have hbd : ∀ τ ∈ Set.Ico (0 : ℝ) t,
      ‖NormedSpace.exp (τ • (-A)) (NormedSpace.exp ((τ - t) • B) (B f - A f))‖ ≤
        ‖A f - B f‖ := by
    intro τ hτ
    calc ‖NormedSpace.exp (τ • (-A)) (NormedSpace.exp ((τ - t) • B) (B f - A f))‖
        ≤ ‖NormedSpace.exp ((τ - t) • B) (B f - A f)‖ :=
          norm_exp_smul_neg_apply_le A hA hτ.1 _
      _ ≤ ‖B f - A f‖ :=
          norm_exp_smul_apply_le_of_nonpos B hB (sub_nonpos.mpr hτ.2.le) _
      _ = ‖A f - B f‖ := norm_sub_rev _ _
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun σ : ℝ => NormedSpace.exp (σ • (-A)) (NormedSpace.exp ((σ - t) • B) f))
    (f' := fun τ : ℝ => NormedSpace.exp (τ • (-A)) (NormedSpace.exp ((τ - t) • B) (B f - A f)))
    (C := ‖A f - B f‖) (fun x _ => (hderiv x).hasDerivWithinAt) hbd t
    (Set.right_mem_Icc.mpr ht)
  simp only [sub_self, zero_smul, NormedSpace.exp_zero, one_apply_eq_self, zero_sub,
    sub_zero] at hmvt
  rw [neg_smul, ← smul_neg, mul_comm]
  exact hmvt

end Contraction

section Completeness

variable {H₀ : Type*} [NormedAddCommGroup H₀] [CompleteSpace H₀]

/-- A family `u s hs` indexed by the positive reals that is Cauchy as `s ↓ 0`, in the `ε`–`δ`
form, converges as `s ↓ 0`, again in the `ε`–`δ` form.

Only completeness of the normed group is used; no inner product, no operators. This is the
completeness step of `Y7`. -/
theorem exists_limit_of_cauchy_along_pos (u : ∀ s : ℝ, 0 < s → H₀)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r), s < δ → r < δ → ‖u s hs - u r hr‖ < ε) :
    ∃ g : H₀, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (s : ℝ) (hs : 0 < s), s < δ → ‖u s hs - g‖ < ε := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hsmall : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / ((n : ℝ) + 1) < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hcs : CauchySeq fun n : ℕ => u (1 / ((n : ℝ) + 1)) (hpos n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hu ε hε
    obtain ⟨N, hN⟩ := hsmall δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact hδ' _ _ _ _ (hN m hm) (hN n hn)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨g, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδ'⟩ := hu (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := hsmall δ hδ
  rw [Metric.tendsto_atTop] at hg
  obtain ⟨N', hN'⟩ := hg (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, N ≤ n ∧ N' ≤ n :=
    ⟨max N N', le_max_left _ _, le_max_right _ _⟩
  have h1 : ‖u s hs - u (1 / ((n : ℝ) + 1)) (hpos n)‖ < ε / 2 :=
    hδ' _ _ _ _ hsδ (hN n hn1)
  have h2 : ‖u (1 / ((n : ℝ) + 1)) (hpos n) - g‖ < ε / 2 := by
    have h := hN' n hn2
    rwa [dist_eq_norm] at h
  have h3 := norm_add_le (u s hs - u (1 / ((n : ℝ) + 1)) (hpos n))
    (u (1 / ((n : ℝ) + 1)) (hpos n) - g)
  rw [sub_add_sub_cancel] at h3
  linarith

end Completeness

section Limit

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]

/-- **`Y7`, the corrected abstract `S6`.** Let `L s hs` be bounded, nonnegative and pairwise
commuting for `s > 0`, and suppose the values `L s hs v` are Cauchy as `s ↓ 0` for every `v` in a
dense set `D`. Then for every `f : H₀` and every `t ≥ 0` the family `exp (-t • L s hs) f`
converges as `s ↓ 0`.

`Y6` gives the Cauchy property of `exp (-t • L s hs) v` for `v ∈ D`, the contraction bound `S5`
transports it to every `f` by an `ε/3` argument, and `exists_limit_of_cauchy_along_pos` produces
the limit. -/
theorem exists_limit_exp_neg_smul (L : ∀ s : ℝ, 0 < s → H₀ →L[ℝ] H₀)
    (hL : ∀ (s : ℝ) (hs : 0 < s) (f : H₀), 0 ≤ ⟪L s hs f, f⟫)
    (hcomm : ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r),
      (L s hs).comp (L r hr) = (L r hr).comp (L s hs))
    (D : Set H₀) (hD : Dense D)
    (hC : ∀ v ∈ D, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r), s < δ → r < δ → ‖L s hs v - L r hr v‖ < ε)
    (f : H₀) {t : ℝ} (ht : 0 ≤ t) :
    ∃ g : H₀, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (s : ℝ) (hs : 0 < s), s < δ → ‖NormedSpace.exp (-t • L s hs) f - g‖ < ε := by
  -- Step 1: the Cauchy property on the dense set, from `Y6`.
  have key : ∀ v ∈ D, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r), s < δ → r < δ →
        ‖NormedSpace.exp (-t • L s hs) v - NormedSpace.exp (-t • L r hr) v‖ < ε := by
    intro v hv ε hε
    have ht1 : (0 : ℝ) < t + 1 := by linarith
    have hε' : 0 < ε / (t + 1) := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := hC v hv (ε / (t + 1)) hε'
    refine ⟨δ, hδ, fun s r hs hr hsδ hrδ => ?_⟩
    have h6 := norm_exp_neg_smul_sub_le (L s hs) (L r hr) (hL s hs) (hL r hr)
      (hcomm s r hs hr) ht v
    have h2 : t * ‖L s hs v - L r hr v‖ ≤ t * (ε / (t + 1)) :=
      mul_le_mul_of_nonneg_left (hδ' s r hs hr hsδ hrδ).le ht
    have h3 : t * (ε / (t + 1)) < ε := by
      calc t * (ε / (t + 1)) < (t + 1) * (ε / (t + 1)) :=
            mul_lt_mul_of_pos_right (by linarith) hε'
        _ = ε := by field_simp
    linarith
  -- Step 2: the Cauchy property for an arbitrary vector, by an `ε/3` argument.
  have general : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r), s < δ → r < δ →
        ‖NormedSpace.exp (-t • L s hs) f - NormedSpace.exp (-t • L r hr) f‖ < ε := by
    intro ε hε
    obtain ⟨v, hvD, hvf⟩ := Metric.mem_closure_iff.mp (hD f) (ε / 3) (by linarith)
    obtain ⟨δ, hδ, hδ'⟩ := key v hvD (ε / 3) (by linarith)
    refine ⟨δ, hδ, fun s r hs hr hsδ hrδ => ?_⟩
    have hfv : ‖f - v‖ < ε / 3 := by rwa [← dist_eq_norm]
    have c1 : ‖NormedSpace.exp (-t • L s hs) f - NormedSpace.exp (-t • L s hs) v‖ < ε / 3 := by
      rw [← map_sub]
      exact lt_of_le_of_lt (norm_exp_neg_smul_apply_le (L s hs) (hL s hs) ht _) hfv
    have c2 : ‖NormedSpace.exp (-t • L r hr) v - NormedSpace.exp (-t • L r hr) f‖ < ε / 3 := by
      rw [← map_sub]
      refine lt_of_le_of_lt (norm_exp_neg_smul_apply_le (L r hr) (hL r hr) ht _) ?_
      rwa [norm_sub_rev]
    have c3 := hδ' s r hs hr hsδ hrδ
    have h4 := dist_triangle4 (NormedSpace.exp (-t • L s hs) f)
      (NormedSpace.exp (-t • L s hs) v) (NormedSpace.exp (-t • L r hr) v)
      (NormedSpace.exp (-t • L r hr) f)
    simp only [dist_eq_norm] at h4
    linarith
  exact exists_limit_of_cauchy_along_pos (fun s hs => NormedSpace.exp (-t • L s hs) f) general

end Limit

/-! ### The route propositions, verbatim -/

/-- **`Y6` of the Yosida-limit route**, stated verbatim as in
`research/audits/YosidaLimitRouteStatements.lean` and discharged from `norm_exp_neg_smul_sub_le`.
No hypothesis is discarded. -/
theorem route_Y6 :
    ∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (A B : H₀ →L[ℝ] H₀), (∀ f, 0 ≤ ⟪A f, f⟫) → (∀ f, 0 ≤ ⟪B f, f⟫) → A.comp B = B.comp A →
      ∀ t : ℝ, 0 ≤ t → ∀ f : H₀,
        ‖NormedSpace.exp (-t • A) f - NormedSpace.exp (-t • B) f‖ ≤ t * ‖A f - B f‖ := by
  intro H₀ _ _ _ A B hA hB hAB t ht f
  exact norm_exp_neg_smul_sub_le A B hA hB hAB ht f

/-- **`Y7` of the Yosida-limit route**, stated verbatim as in
`research/audits/YosidaLimitRouteStatements.lean` and discharged from
`exists_limit_exp_neg_smul`. The route's implicit `{ε}` and `{s r}` binders are converted to the
explicit ones of the module lemma; no hypothesis is discarded. -/
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
  have hC' : ∀ v ∈ D, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (s r : ℝ) (hs : 0 < s) (hr : 0 < r), s < δ → r < δ → ‖L s hs v - L r hr v‖ < ε := by
    intro v hv ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hC v hv hε
    exact ⟨δ, hδ, fun s r hs hr h1 h2 => hδ' hs hr h1 h2⟩
  obtain ⟨g, hg⟩ := exists_limit_exp_neg_smul L hL hcomm D hD hC' f ht
  refine ⟨g, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hg ε hε
  exact ⟨δ, hδ, fun {s} hs hsδ => hδ' s hs hsδ⟩

end FunctionalInequalities.Analysis.Semigroup

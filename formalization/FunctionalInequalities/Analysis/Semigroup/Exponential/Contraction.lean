import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exponential of a bounded nonnegative operator is a contraction

resolvent contraction of the semigroup-generation route (obligation `S5` of
`research/audits/SemigroupGenerationRouteStatements.lean`), proved here as
`norm_exp_neg_smul_apply_le` and restated verbatim as `route_S5`. See `Resolvent/Form.lean` for the form construction, the shifted weak form
and the resolvent operator, and `Resolvent/Basic.lean` for resolvent solvability.

The route applies this to the Yosida approximation `L_s = (1 - J_s)/s`, a bounded nonnegative
self-adjoint operator, to see that `NormedSpace.exp (-t • L_s)` is a contraction for `t ≥ 0`.
Nothing here is specific to `L_s`: the statement is about an arbitrary bounded operator on a real
Hilbert space.

## Proof: monotonicity of the norm along the orbit

Write `u t = exp (t • (-L)) f`. Mathlib's `hasDerivAt_exp_smul_const'` gives `u' t = -L (u t)`, so
the product rule for the inner product (`HasDerivAt.inner`) gives
`(d/dt) ‖u t‖² = -2 ⟪L (u t), u t⟫ ≤ 0`. The function `t ↦ ‖u t‖²` is therefore antitone on all of
`ℝ` (`antitone_of_deriv_nonpos`), and evaluating at `0 ≤ t` against `u 0 = f` gives
`‖u t‖² ≤ ‖f‖²`. No spectral theory, no functional calculus and no operator-norm estimate is used;
the conclusion is pointwise in `f`, as the route states it.

## Route hypothesis not used

The route assumes `L` self-adjoint, `⟪L f, g⟫ = ⟪f, L g⟫`. The proof never uses it: the derivative
of `⟪u t, u t⟫` is `⟪u t, -L (u t)⟫ + ⟪-L (u t), u t⟫`, and both terms are `-⟪L (u t), u t⟫` by
symmetry of the **real inner product** alone (`real_inner_comm`). The module therefore proves the
stronger statement `norm_exp_neg_smul_apply_le` for every bounded nonnegative `L`, and `route_S5`
accepts and discards the self-adjointness hypothesis, exactly as the shifted weak form discards `0 < s` and resolvent solvability
discards density. The hypothesis `0 ≤ t` **is** used: for `t < 0` the orbit norm is larger, not
smaller, than `‖f‖`.

## Deliberately out of scope

the adjoint-product identification–the semigroup limit (strong convergence of the Yosida exponentials, the semigroup and strong-continuity
laws, the generator) are not proved here. This is one step of the abstract semigroup
construction; it is not the Markov property, not Bakry–Émery calculus, and not any step of
Buser's inequality. `thm:logconcave-cheeger-poincare-comparison` gains no progress marker from
this module.
-/

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

section Orbit

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]

/-- The orbit `t ↦ exp (t • A) f` of a bounded operator is differentiable, with derivative
`A (exp (t • A) f)`. This is `hasDerivAt_exp_smul_const'` evaluated at the fixed vector `f`. -/
theorem hasDerivAt_exp_smul_apply (A : H₀ →L[ℝ] H₀) (f : H₀) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) f) (A (NormedSpace.exp (t • A) f)) t := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).clm_apply (hasDerivAt_const t f)
  simpa using h

/-- Along the orbit `u t = exp (t • (-L)) f` of a nonnegative bounded operator `L`, the squared
norm `‖u t‖²` has derivative `-2 ⟪L (u t), u t⟫ ≤ 0` and is therefore antitone on all of `ℝ`.

Only nonnegativity of `L` and symmetry of the real inner product are used; self-adjointness of
`L` is not assumed. -/
theorem antitone_normSq_exp_smul_neg (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) (f : H₀) :
    Antitone fun t : ℝ => ‖NormedSpace.exp (t • (-L)) f‖ ^ 2 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ‖NormedSpace.exp (s • (-L)) f‖ ^ 2)
      (-(2 * ⟪L (NormedSpace.exp (t • (-L)) f), NormedSpace.exp (t • (-L)) f⟫)) t := by
    intro t
    have h := (hasDerivAt_exp_smul_apply (-L) f t).inner ℝ (hasDerivAt_exp_smul_apply (-L) f t)
    have hfun : (fun s : ℝ => ‖NormedSpace.exp (s • (-L)) f‖ ^ 2) =
        fun s : ℝ => ⟪NormedSpace.exp (s • (-L)) f, NormedSpace.exp (s • (-L)) f⟫ := by
      funext s
      rw [real_inner_self_eq_norm_sq]
    rw [hfun]
    refine h.congr_deriv ?_
    rw [neg_apply, inner_neg_left, inner_neg_right,
      real_inner_comm (L (NormedSpace.exp (t • (-L)) f))]
    ring
  refine antitone_of_deriv_nonpos (fun t => (hderiv t).differentiableAt) fun t => ?_
  rw [(hderiv t).deriv]
  have := hL (NormedSpace.exp (t • (-L)) f)
  linarith

/-- **resolvent contraction, strengthened.** If `L` is a bounded nonnegative operator on a real Hilbert space, then
`exp (-t • L)` is a contraction for every `t ≥ 0`, pointwise: `‖exp (-t • L) f‖ ≤ ‖f‖`.

The route's self-adjointness hypothesis is not needed and not assumed. -/
theorem norm_exp_neg_smul_apply_le (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) {t : ℝ}
    (ht : 0 ≤ t) (f : H₀) : ‖NormedSpace.exp (-t • L) f‖ ≤ ‖f‖ := by
  have h := antitone_normSq_exp_smul_neg L hL f ht
  simp only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self] at h
  rw [neg_smul, ← smul_neg]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end Orbit

/-- **resolvent contraction of the semigroup-generation route**, stated verbatim as in
`research/audits/SemigroupGenerationRouteStatements.lean` and discharged from
`norm_exp_neg_smul_apply_le`.

The route hypothesis `∀ f g, ⟪L f, g⟫ = ⟪f, L g⟫` (self-adjointness) is accepted here and **not
used**; the stronger unconditional statement is `norm_exp_neg_smul_apply_le`. -/
theorem route_S5 :
    ∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (L : H₀ →L[ℝ] H₀), (∀ f, 0 ≤ ⟪L f, f⟫) → (∀ f g, ⟪L f, g⟫ = ⟪f, L g⟫) →
      ∀ t : ℝ, 0 ≤ t → ∀ f : H₀, ‖NormedSpace.exp (-t • L) f‖ ≤ ‖f‖ := by
  intro H₀ _ _ _ L hL _ t ht f
  exact norm_exp_neg_smul_apply_le L hL ht f

end FunctionalInequalities.Analysis.Semigroup

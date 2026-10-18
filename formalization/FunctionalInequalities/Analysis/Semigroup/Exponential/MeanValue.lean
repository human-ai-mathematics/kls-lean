import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A mean value bound for `exp (-t • A) f - f + t • A f`

The estimate is `norm_exp_neg_smul_sub_add_smul_le`.

For a bounded operator `A` on a complete normed space, a vector `f`, `0 ≤ t` and a real `C`: if
`‖exp (-τ • A) (A f) - A f‖ ≤ C` for every `τ ∈ [0, t]`, then

`‖exp (-t • A) f - f + t • A f‖ ≤ C * t`.

This is the quantitative statement that `exp (-t • A) f = f - t • A f + O(t)` with a constant
controlled by the motion of `A f` along the orbit; the route uses it with `A = L_s` the Yosida
approximation to identify the generator of the limit semigroup.

## Proof

The path `φ τ = exp (-τ • A) f - f + τ • A f` has `φ 0 = 0` and, by
`hasDerivAt_exp_smul_const` evaluated at the fixed vector `f` (`HasDerivAt.clm_apply` against
`hasDerivAt_const`) plus the derivative `A f` of `τ ↦ τ • A f`,

`φ' τ = -(exp (-τ • A) (A f)) + A f`,

recorded as `hasDerivAt_exp_neg_smul_path`. Its norm is `‖exp (-τ • A) (A f) - A f‖ ≤ C` on
`[0, t]`, so the mean value inequality
`norm_image_sub_le_of_norm_deriv_le_segment'` on `[0, t]`, evaluated at `t`, gives
`‖φ t - φ 0‖ ≤ C * (t - 0)`. Everything is pointwise in `f`: no operator norm of `A` or of an
exponential is ever estimated, which avoids the `ContinuousLinearMap` norm instance diamond.
Nonnegativity of `A` is not assumed and not needed, nor is `0 ≤ C`: for `t = 0` both sides
are `0`.

## Scope

The route states the exponential mean-value bound on a real Hilbert space, `[InnerProductSpace ℝ H₀] [CompleteSpace H₀]`. The
inner product plays no role — no symmetry, no nonnegativity, no Cauchy–Schwarz — so the module
lemmas are proved for an arbitrary `[NormedSpace ℝ H₀] [CompleteSpace H₀]`, and `route_G2`
accepts the `InnerProductSpace` instance and discards it. Completeness **is** used: it supplies
`CompleteSpace (H₀ →L[ℝ] H₀)`, the hypothesis under which `NormedSpace.exp` is differentiable.
The hypothesis `0 ≤ t` **is** used, so that `[0, t]` is the correct interval and `t` its right
endpoint. This follows the precedent of the shifted weak form, resolvent solvability, resolvent contraction and the form identity, which likewise prove the
general statement and keep a verbatim wrapper.

## Deliberately out of scope

the generator right derivative (uniformity on `[0, t]` of the the adjoint-product identification convergence) and `G3`/the semigroup limit (the generator of the limit
semigroup is `-T†T`) are **not** proved here; neither are `P1`–`P8` (the exponential approximation). This module mentions
no unbounded operator `T`, no adjoint, no resolvent and no Yosida approximation: it is a
statement about a single bounded operator. Nothing here is the Markov property, Bakry–Émery
calculus, a small-time heat estimate, localization or any step of Buser's inequality;
`thm:logconcave-cheeger-poincare-comparison` gains no progress marker from this module.
-/

noncomputable section

namespace FunctionalInequalities.Analysis.Semigroup

section MeanValue

variable {H₀ : Type*} [NormedAddCommGroup H₀] [NormedSpace ℝ H₀] [CompleteSpace H₀]

/-- The path `σ ↦ exp (-σ • A) f - f + σ • A f` used in the exponential mean-value bound is differentiable, with derivative
`-(exp (-τ • A) (A f)) + A f`.

This is `hasDerivAt_exp_smul_const` for the operator `-A`, evaluated at the fixed vector `f`,
plus the derivative `A f` of the linear term; the constant `-f` contributes nothing. -/
theorem hasDerivAt_exp_neg_smul_path (A : H₀ →L[ℝ] H₀) (f : H₀) (τ : ℝ) :
    HasDerivAt (fun σ : ℝ => NormedSpace.exp (-σ • A) f - f + σ • A f)
      (-(NormedSpace.exp (-τ • A) (A f)) + A f) τ := by
  have hswap : ∀ σ : ℝ, NormedSpace.exp (-σ • A) = NormedSpace.exp (σ • (-A)) := by
    intro σ
    rw [neg_smul, ← smul_neg]
  have hfun : (fun σ : ℝ => NormedSpace.exp (-σ • A) f - f + σ • A f) =
      fun σ : ℝ => NormedSpace.exp (σ • (-A)) f - f + σ • A f := by
    funext σ
    rw [hswap]
  have hc : HasDerivAt (fun σ : ℝ => NormedSpace.exp (σ • (-A)))
      (NormedSpace.exp (τ • (-A)) * (-A)) τ := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) τ
  have hu : HasDerivAt (fun σ : ℝ => NormedSpace.exp (σ • (-A)) f)
      (-(NormedSpace.exp (τ • (-A)) (A f))) τ := by
    have h := hc.clm_apply (hasDerivAt_const τ f)
    simpa using h
  have hs : HasDerivAt (fun σ : ℝ => σ • A f) (A f) τ := by
    have h := (hasDerivAt_id τ).smul_const (A f)
    simpa using h
  rw [hfun]
  refine ((hu.sub_const f).add hs).congr_deriv ?_
  rw [hswap]

/-- **the exponential mean-value bound, for an arbitrary complete normed space.** Let `A` be a bounded operator, `f` a vector,
`0 ≤ t` and `C : ℝ`. If `‖exp (-τ • A) (A f) - A f‖ ≤ C` for every `τ ∈ [0, t]`, then

`‖exp (-t • A) f - f + t • A f‖ ≤ C * t`.

No nonnegativity, symmetry or inner product is needed, and `C` is not assumed nonnegative (for
`t = 0` both sides vanish). See the module docstring for the proof. -/
theorem norm_exp_neg_smul_sub_add_smul_le (A : H₀ →L[ℝ] H₀) (f : H₀) {t : ℝ} (ht : 0 ≤ t)
    {C : ℝ} (hC : ∀ τ ∈ Set.Icc 0 t, ‖NormedSpace.exp (-τ • A) (A f) - A f‖ ≤ C) :
    ‖NormedSpace.exp (-t • A) f - f + t • A f‖ ≤ C * t := by
  have hbd : ∀ τ ∈ Set.Ico (0 : ℝ) t, ‖-(NormedSpace.exp (-τ • A) (A f)) + A f‖ ≤ C := by
    intro τ hτ
    have hrw : -(NormedSpace.exp (-τ • A) (A f)) + A f =
        -(NormedSpace.exp (-τ • A) (A f) - A f) := by abel
    rw [hrw, norm_neg]
    exact hC τ ⟨hτ.1, hτ.2.le⟩
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun σ : ℝ => NormedSpace.exp (-σ • A) f - f + σ • A f)
    (f' := fun τ : ℝ => -(NormedSpace.exp (-τ • A) (A f)) + A f)
    (C := C) (fun x _ => (hasDerivAt_exp_neg_smul_path A f x).hasDerivWithinAt) hbd t
    (Set.right_mem_Icc.mpr ht)
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero, one_apply_eq_self, sub_self, add_zero,
    sub_zero] at hmvt
  exact hmvt

end MeanValue

/-- **the exponential mean-value bound of the generated-semigroup route**, stated verbatim as in
`research/audits/GeneratedSemigroupRouteStatements.lean` and discharged from
`norm_exp_neg_smul_sub_add_smul_le`.

The route's `InnerProductSpace ℝ H₀` instance is accepted here and **not used**; the general
statement, for any complete normed space over `ℝ`, is `norm_exp_neg_smul_sub_add_smul_le`. -/
theorem route_G2 :
    ∀ {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    (A : H₀ →L[ℝ] H₀) (f : H₀) {t : ℝ}, 0 ≤ t → ∀ {C : ℝ},
      (∀ τ ∈ Set.Icc 0 t, ‖NormedSpace.exp (-τ • A) (A f) - A f‖ ≤ C) →
        ‖NormedSpace.exp (-t • A) f - f + t • A f‖ ≤ C * t := by
  intro H₀ _ _ _ A f t ht C hC
  exact norm_exp_neg_smul_sub_add_smul_le A f ht hC

end FunctionalInequalities.Analysis.Semigroup

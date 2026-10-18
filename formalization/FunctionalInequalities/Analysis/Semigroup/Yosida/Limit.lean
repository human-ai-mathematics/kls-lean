import FunctionalInequalities.Analysis.Semigroup.Exponential.Limit
import FunctionalInequalities.Analysis.Semigroup.Yosida.Laws

/-!
# the adjoint-product identification: the Yosida exponentials converge strongly

`Y8` of the Yosida-limit route (`research/decisions/2026-09-19-yosida-limit-route.md`), which is
the adjoint-product identification of the semigroup-generation route for the actual Yosida approximation
`L_s = s⁻¹ (1 - J_s)` of `T†T`: for `T` closed and densely defined,
`exp (-t • L_s) f` converges as `s ↓ 0`, for every `f : H₀` and every `t ≥ 0`.

The proof is pure composition. The corrected abstract statement `Y7`
(`exists_limit_exp_neg_smul`, `Exponential/Limit.lean`) is applied to the family `s ↦ L_s` with the
dense set `D(T†T)`: nonnegativity is `Y1` (`yosida_nonneg`), commutation is `Y3`
(`yosida_comp_comm`), density is density of D(T†T) (`dense_adjointComp_domain`), and the Cauchy property on
`D(T†T)` follows from the convergence `L_s f → T†T f` of `Y5`
(`exists_delta_norm_yosida_sub_adjointComp_lt`) by the triangle inequality.

The limit `g` is not yet named as an operator: the exponential approximation (the limit defines a strongly continuous
semigroup of self-adjoint contractions) and the semigroup limit (its generator is `T†T`) are not proved here. Nothing
here is the Markov property, Bakry–Émery calculus, a heat estimate or any step of Buser's inequality.
-/

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-- On `D(T†T)` the Yosida approximations `L_s f` are Cauchy as `s ↓ 0`: they converge to
`T†T f` (`Y5`). -/
theorem yosida_cauchy_on_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (v : H₀) (hv : v ∈ ((adjointComp T).domain : Set H₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s r : ℝ} (hs : 0 < s) (hr : 0 < r), s < δ → r < δ →
      ‖yosida T hT hs v - yosida T hT hr v‖ < ε := by
  obtain ⟨δ, hδ, h⟩ :=
    exists_delta_norm_yosida_sub_adjointComp_lt T hT hd ⟨v, hv⟩ (half_pos hε)
  refine ⟨δ, hδ, fun {s r} hs hr hsδ hrδ => ?_⟩
  have h1 : ‖yosida T hT hs v - adjointComp T ⟨v, hv⟩‖ < ε / 2 := h hs hsδ
  have h2 : ‖yosida T hT hr v - adjointComp T ⟨v, hv⟩‖ < ε / 2 := h hr hrδ
  calc ‖yosida T hT hs v - yosida T hT hr v‖
      = ‖(yosida T hT hs v - adjointComp T ⟨v, hv⟩)
          - (yosida T hT hr v - adjointComp T ⟨v, hv⟩)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖yosida T hT hs v - adjointComp T ⟨v, hv⟩‖
          + ‖yosida T hT hr v - adjointComp T ⟨v, hv⟩‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

/-- **the adjoint-product identification for the Yosida approximation** (`Y8`). For `T` closed and densely defined, every
`t ≥ 0` and every `f : H₀`, the vectors `exp (-t • L_s) f` converge as `s ↓ 0`, in the `ε`–`δ`
sense forced by the proof argument `0 < s` carried by `L_s`. -/
theorem exists_limit_exp_neg_smul_yosida (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) {t : ℝ} (ht : 0 ≤ t) :
    ∃ g : H₀, ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖NormedSpace.exp (-t • yosida T hT hs) f - g‖ < ε := by
  obtain ⟨g, hg⟩ := exists_limit_exp_neg_smul (fun s hs => yosida T hT hs)
    (fun s hs v => yosida_nonneg T hT hs v) (fun s r hs hr => yosida_comp_comm T hT hs hr)
    ((adjointComp T).domain : Set H₀) (dense_adjointComp_domain T hT hd)
    (fun v hv ε hε => yosida_cauchy_on_adjointComp_domain T hT hd v hv hε) f ht
  refine ⟨g, fun {ε} hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hg ε hε
  exact ⟨δ, hδ, fun {s} hs hsδ => h s hs hsδ⟩

end FunctionalInequalities.Analysis.Semigroup

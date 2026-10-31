module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # C¹ local inverses on prescribed open domains

This layer uses only Mathlib. Both the map and its inverse are C¹ on their respective
open domains; no smoothness is required outside the prescribed source domain.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContDiff

namespace FunctionalInequalities.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A C¹ map with invertible derivative admits a C¹ local inverse whose source lies in
the prescribed open domain. Regularity is on the entire source and target. -/
theorem exists_contDiffOn_localInverse {f : E → F} {O : Set E} {x : E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ 1 f O) (hx : x ∈ O)
    {L : E ≃L[ℝ] F} (hL : HasFDerivAt f (L : E →L[ℝ] F) x) :
    ∃ D : OpenPartialHomeomorph E F, (⇑D = f) ∧ x ∈ D.source ∧ D.source ⊆ O ∧
      ContDiffOn ℝ 1 D D.source ∧ ContDiffOn ℝ 1 D.symm D.target := by
  have hfx := hf.contDiffAt (hO.mem_nhds hx)
  let D := hfx.toOpenPartialHomeomorph f hL one_ne_zero
  have hxD : x ∈ D.source := hfx.mem_toOpenPartialHomeomorph_source hL one_ne_zero
  have hsymm : ContDiffAt ℝ 1 D.symm (D x) := by
    apply D.contDiffAt_symm (D.map_source hxD)
    · rw [D.left_inv hxD]
      exact hL
    · rw [D.left_inv hxD]
      exact hfx
  let C := D.restrContDiff ℝ 1 (by simp)
  have hxC : x ∈ C.source := ⟨hxD, hfx, hsymm⟩
  refine ⟨C.restr O, rfl, ?_, ?_, ?_, ?_⟩
  · rw [C.restr_source' O hO]
    exact ⟨hxC, hx⟩
  · rw [C.restr_source' O hO]
    exact inter_subset_right
  · exact (D.contDiffOn_restrContDiff_source ℝ (by simp : (1 : ℕ∞ω) ≠ ∞)).mono
      (by rw [C.restr_source' O hO]; exact inter_subset_left)
  · exact (D.contDiffOn_restrContDiff_target ℝ (by simp : (1 : ℕ∞ω) ≠ ∞)).mono
      (by intro y hy; exact hy.1)

end FunctionalInequalities.Analysis

/-! ## Global inverses of injective maps with invertible derivative -/

noncomputable section InjectiveInverse

namespace FunctionalInequalities.Analysis

section InverseRegularity

open Set Function Filter
open scoped Topology

/--
If an injective `C^k` map, `k ≠ 0`, has an invertible derivative at every point, then `invFun f` is
`C^k` on the range
of `f`: near each image point it agrees with the local inverse of the inverse function theorem. -/
theorem contDiffOn_invFun_of_injective_of_hasFDerivAt_equiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Nonempty E]
    {k : WithTop ℕ∞} (hk : k ≠ 0) {f : E → F} (hf : ContDiff ℝ k f) (hi : Injective f)
    (A : E → E ≃L[ℝ] F) (hA : ∀ x, HasFDerivAt f (A x : E →L[ℝ] F) x) :
    ContDiffOn ℝ k (invFun f) (range f) := by
  rintro y ⟨a, rfl⟩
  have hs := hf.contDiffAt.hasStrictFDerivAt' (hA a) hk
  have he := hs.localInverse_unique (Eventually.of_forall (leftInverse_invFun hi))
  exact ((hf.contDiffAt.to_localInverse (hA a) hk).congr_of_eventuallyEq he).contDiffWithinAt

end InverseRegularity

section InverseDerivative

open Set Function Filter FunctionalInequalities
open scoped Topology

/--
If an injective `f` is `C¹` at `a` with invertible derivative `A`, then `invFun f` has derivative
`A⁻¹` at `f a`. -/
theorem hasFDerivAt_invFun_of_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Nonempty E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {a : E}
    (hf : ContDiffAt ℝ 1 f a) (hi : Injective f) (A : E ≃L[ℝ] F)
    (hA : HasFDerivAt f (A : E →L[ℝ] F) a) :
    HasFDerivAt (invFun f) (A.symm : F →L[ℝ] E) (f a) := by
  exact
    ((hf.hasStrictFDerivAt' hA (by norm_num)).to_local_left_inverse
        (Eventually.of_forall (leftInverse_invFun hi))).hasFDerivAt

end InverseDerivative

end FunctionalInequalities.Analysis

end InjectiveInverse

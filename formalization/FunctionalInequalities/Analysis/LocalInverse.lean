import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # C¹ local inverses on prescribed open domains

This layer uses only Mathlib. Both the map and its inverse are C¹ on their respective
open domains; no smoothness is required outside the prescribed source domain.
-/

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

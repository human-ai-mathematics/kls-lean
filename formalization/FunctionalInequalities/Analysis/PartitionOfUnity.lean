import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Finite smooth decomposition of a compactly supported field

General analysis, independent of the KLS objects: a compactly supported `C^n` map on a
finite-dimensional real normed space splits as a **finite** sum of `C^n` maps, each of which has
compact support inside a prescribed member of an open cover of the support.  Every statement here
is proved and uses only the standard axioms; the module contains no hole.

## What the statement gives, and why each clause is needed

`exists_finset_sum_eq_of_isOpen_cover` produces a `Finset` of indices and a family `G` with

* `ContDiff ℝ n (G i)` and `HasCompactSupport (G i)` — so each piece is an admissible input to the
  local identities that will be applied to it;
* `tsupport (G i) ⊆ W i` — the **closed** support, not merely `support (G i) ⊆ W i`.  This is what
  a localization argument needs: it makes `G i` vanish on a *neighbourhood* of every point outside
  `W i`, hence makes `fderiv ℝ (G i)` vanish there too;
* `∀ x, ∑ i ∈ s, G i x = F x` — an equality of functions on the **whole** space, not only on
  `tsupport F`.  A pointwise identity valid only on the support could not be differentiated.

The family is indexed by all of `γ`, and the finite sum runs over `s`; for `i ∉ s` the piece
`G i` is identically zero, so summing over a larger finite set changes nothing.

## Route

`SmoothPartitionOfUnity.exists_isSubordinate` on the manifold `V` modelled on itself
(`𝓘(ℝ, V)`; `V` is Hausdorff, σ-compact and finite-dimensional, and `contMDiff_iff_contDiff`
identifies `C^∞` in the manifold sense with `ContDiff ℝ ∞`), then `G i = χ i • F`.  Finiteness is
`LocallyFinite.finite_nonempty_inter_compact` applied to the compact set `tsupport F`: only
finitely many members of a locally finite family of supports meet it, and a member that does not
meet it contributes the zero function *everywhere*, not just on the support.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace FunctionalInequalities.Analysis

universe u v w

/-- **Finite smooth decomposition subordinate to an open cover of the support.**  A compactly
supported `C^n` map whose support is covered by open sets `W i` is a finite sum of `C^n` maps with
compact support, the `i`-th one supported inside `W i`.  The sum identity holds at every point of
the space. -/
theorem exists_finset_sum_eq_of_isOpen_cover {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {γ : Type w} {n : ℕ∞} {F : V → E} (hF : ContDiff ℝ n F)
    (hFc : HasCompactSupport F) {W : γ → Set V} (hWo : ∀ i, IsOpen (W i))
    (hcover : tsupport F ⊆ ⋃ i, W i) :
    ∃ (s : Finset γ) (G : γ → V → E),
      (∀ i, ContDiff ℝ n (G i)) ∧ (∀ i, HasCompactSupport (G i)) ∧
        (∀ i, tsupport (G i) ⊆ W i) ∧ ∀ x, ∑ i ∈ s, G i x = F x := by
  classical
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, V))
    (isClosed_tsupport F) W hWo hcover
  refine ⟨(χ.locallyFinite.finite_nonempty_inter_compact hFc).toFinset,
    fun i x => χ i x • F x, fun i => ?_, fun i => ?_, fun i => ?_, fun x => ?_⟩
  · exact ((contMDiff_iff_contDiff.mp (χ i).contMDiff).of_le (by exact_mod_cast le_top)).smul hF
  · exact HasCompactSupport.smul_left (f := fun x => χ i x) hFc
  · exact (tsupport_smul_subset_left _ _).trans (hχ i)
  · by_cases hx : x ∈ tsupport F
    · have hsub : support (fun i => χ i x)
          ⊆ ((χ.locallyFinite.finite_nonempty_inter_compact hFc).toFinset : Set γ) := by
        intro i hi
        simpa using ⟨x, hi, hx⟩
      have hone : ∑ i ∈ (χ.locallyFinite.finite_nonempty_inter_compact hFc).toFinset, χ i x = 1 := by
        rw [← finsum_eq_finsetSum_of_support_subset _ hsub]
        exact χ.sum_eq_one hx
      rw [← Finset.sum_smul, hone, one_smul]
    · simp [image_eq_zero_of_notMem_tsupport hx]

end FunctionalInequalities.Analysis

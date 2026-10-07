import FunctionalInequalities.Analysis.Tensor.Symmetrization
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Partial symmetrization of coordinate tensors

Bizeul–Klartag–Lehec, *Presenting a proof of the Kannan–Lovász–Simonovits conjecture*
(arXiv:2610.05474v1), Lemma 2.2, in the source's coordinates. A real tensor with `k` indices in
`Fin n` is a vector of `Coord n k = EuclideanSpace ℝ (Fin k → Fin n)`, so its norm is the
Hilbert–Schmidt norm of the source. Permuting index positions is an orthogonal representation of
`Perm (Fin k)`, and `S_q` averages over the permutations of the first `q` positions, leaving the
trailing positions fixed. If `3d ≤ k` and a tensor is symmetric in its first `d` indices and in its
next `2d` indices, then `|A| ≤ 4^d |S_{2d} A|`. The dimension `n` is arbitrary, including `0`.
-/

noncomputable section

open Finset

namespace FunctionalInequalities.Analysis.Tensor

/-- Real tensors with `k` indices, each ranging over `Fin n`, as a Euclidean space: the norm is the
Hilbert–Schmidt norm `|A| = (∑_{i₁,…,i_k} A_{i₁…i_k}²)^{1/2}` of BKL Section 2. -/
abbrev Coord (n k : ℕ) : Type := EuclideanSpace ℝ (Fin k → Fin n)

/-- The positions `a ≤ p < b` among the `k` index positions. -/
def slots (k a b : ℕ) : Finset (Fin k) :=
  univ.filter fun p => a ≤ p.val ∧ p.val < b

/-- Permuting the index positions of a tensor: `(slotPerm σ A) i = A (i ∘ σ)`. -/
def slotPerm (n k : ℕ) (σ : Equiv.Perm (Fin k)) : Coord n k ≃ₗᵢ[ℝ] Coord n k :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.arrowCongr σ (Equiv.refl (Fin n)))

theorem slotPerm_apply (n k : ℕ) (σ : Equiv.Perm (Fin k)) (A : Coord n k) (i : Fin k → Fin n) :
    slotPerm n k σ A i = A (i ∘ σ) := by
    simp [slotPerm, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft', Equiv.arrowCongr, Function.comp_def]

theorem slotPerm_one (n k : ℕ) : slotPerm n k 1 = 1 := by
    apply LinearIsometryEquiv.ext
    intro A
    apply PiLp.ext
    intro i
    rw [slotPerm_apply]
    simp

theorem slotPerm_mul (n k : ℕ) (σ τ : Equiv.Perm (Fin k)) :
    slotPerm n k (σ * τ) = slotPerm n k σ * slotPerm n k τ := by
    ext A i
    simp [slotPerm_apply, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      Function.comp_assoc]

/-- The orthogonal representation of `Perm (Fin k)` on tensors with `k` indices by permutation of
index positions. -/
def slotRep (n k : ℕ) : Equiv.Perm (Fin k) →* (Coord n k ≃ₗᵢ[ℝ] Coord n k) where
  toFun := slotPerm n k
  map_one' := slotPerm_one n k
  map_mul' := slotPerm_mul n k

/-- `S_q A`: the average of `A` over all permutations of its first `q` indices. -/
def symmetrize (n k q : ℕ) (A : Coord n k) : Coord n k :=
  blockAverage (slotRep n k) (slots k 0 q) A

/-- The number of positions `a ≤ p < b` among `k` positions, for `b ≤ k`. -/
theorem card_slots {k a b : ℕ} (hb : b ≤ k) : (slots k a b).card = b - a := by
    have hmap : (slots k a b).map Fin.valEmbedding = Ico a b := by
      ext x
      constructor
      · intro hx
        rcases mem_map.mp hx with ⟨p, hp, rfl⟩
        apply mem_Ico.mpr
        simpa [slots] using hp
      · intro hx
        have hx' : a ≤ x ∧ x < b := mem_Ico.mp hx
        let p : Fin k := ⟨x, lt_of_lt_of_le hx'.2 hb⟩
        apply mem_map.mpr
        refine ⟨p, ?_, ?_⟩
        · simpa [slots, p] using hx'
        · simp [p]
    calc
      (slots k a b).card = ((slots k a b).map Fin.valEmbedding).card := by simp
      _ = (Ico a b).card := by rw [hmap]
      _ = b - a := by simp

/-- **BKL Lemma 2.2.** Let `d ≥ 0` and let `A` be a tensor with `k ≥ 3d` indices over `Fin n`,
invariant under permutations of its first `d` indices and under permutations of its next `2d`
indices. Then `|A| ≤ 4^d |S_{2d} A|`. Indices beyond the first `3d` are untouched. -/
theorem norm_le_four_pow_mul_norm_symmetrize {n k d : ℕ} (hk : 3 * d ≤ k) (A : Coord n k)
    (h₁ : ∀ σ ∈ fixingOutside (slots k 0 d), slotRep n k σ A = A)
    (h₂ : ∀ σ ∈ fixingOutside (slots k d (3 * d)), slotRep n k σ A = A) :
    ‖A‖ ≤ (4 : ℝ) ^ d * ‖symmetrize n k (2 * d) A‖ := by
    change
      ‖A‖ ≤ (4 : ℝ) ^ d *
        ‖blockAverage (slotRep n k) (slots k 0 (2 * d)) A‖
    have hAcard : (slots k 0 d).card = d := by
      rw [card_slots (k := k) (a := 0) (b := d) (by omega)]
      omega
    have hBcard : (slots k d (3 * d)).card = 2 * d := by
      rw [card_slots (k := k) (a := d) (b := 3 * d) hk]
      omega
    have hQcard : (slots k 0 (2 * d)).card = 2 * d := by
      rw [card_slots (k := k) (a := 0) (b := 2 * d) (by omega)]
      omega
    have hdis : Disjoint (slots k 0 d) (slots k d (3 * d)) := by
      refine Finset.disjoint_left.2 ?_
      intro x hx₁ hx₂
      simp [slots] at hx₁ hx₂
      omega
    have hAQ : slots k 0 d ⊆ slots k 0 (2 * d) := by
      intro x hx
      simp [slots] at hx ⊢
      omega
    have hQ : slots k 0 (2 * d) ⊆ slots k 0 d ∪ slots k d (3 * d) := by
      intro x hx
      simp [slots] at hx ⊢
      by_cases h : x.val < d
      · left
        omega
      · right
        omega
    exact
      norm_le_four_pow_mul_norm_blockAverage
        (ρ := slotRep n k) (A := slots k 0 d) (B := slots k d (3 * d))
        (Q := slots k 0 (2 * d)) (d := d)
        hAcard hBcard hdis hAQ hQ hQcard A h₁ h₂

end FunctionalInequalities.Analysis.Tensor

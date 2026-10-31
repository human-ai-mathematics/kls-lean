module

public import FunctionalInequalities.Analysis.Holder.Representative
public import FunctionalInequalities.Analysis.Matrix.RankOneFrame

/-!
# Hölder representatives of matrix entries

If a frame contains every coordinate direction and every normalized pair `(e_i + e_j)/√2`, local
Hölder representatives of the
frame quadratic forms of an a.e. symmetric matrix field give local Hölder representatives of every
matrix entry.
-/

@[expose] public section

/-! ## Entries from frame quadratic forms -/

noncomputable section MatrixEntryHolder

open MeasureTheory Set Matrix
open scoped NNReal ENNReal

namespace FunctionalInequalities.Analysis

/--
If a frame contains every coordinate direction and every normalized pair, local Hölder
representatives (constant `C`) of
the frame quadratic forms of an a.e. symmetric matrix field give local Hölder representatives of
every entry, with constant
`2C`. -/
theorem exists_matrix_entry_holder_representatives {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) (U : Set X) {n N : ℕ} (A : X → Matrix (Fin n) (Fin n) ℝ)
    (γ : Fin N → Fin n → ℝ) (hcoord : ∀ i : Fin n, ∃ k : Fin N, γ k = Pi.single i 1)
    (hpair :
      ∀ i j : Fin n,
        i ≠ j →
          ∃ k : Fin N,
            γ k = fun a =>
              ((Pi.single i (1 : ℝ) : Fin n → ℝ) a + (Pi.single j (1 : ℝ) : Fin n → ℝ) a) /
                Real.sqrt 2)
    (hSym : ∀ᵐ x ∂μ.restrict U, (A x).IsSymm) {C η : ℝ≥0} (hη : 0 < η)
    (hrep :
      ∀ k : Fin N,
        ∃ g : U → ℝ,
          HolderWith C η g ∧
            ∀ᵐ x ∂μ.restrict U,
              ∀ hx : x ∈ U, g ⟨x, hx⟩ = ∑ i : Fin n, ∑ j : Fin n, γ k i * γ k j * A x i j) :
    ∀ i j : Fin n,
      ∃ g : U → ℝ,
        HolderWith (2 * C) η g ∧
          Continuous g ∧ ∀ᵐ x ∂μ.restrict U, ∀ hx : x ∈ U, g ⟨x, hx⟩ = A x i j := by
  intro i j
  obtain ⟨ki, hki⟩ := hcoord i
  obtain ⟨gi, hgi, hgiAE⟩ := hrep ki
  by_cases hij : i = j
  · subst j
    have hgi2 : HolderWith (2 * C) η gi :=
      hgi.mono
        (le_mul_of_one_le_left (show (0 : ℝ≥0) ≤ C from zero_le) (by norm_num : (1 : ℝ≥0) ≤ 2))
    refine ⟨gi, hgi2, hgi2.continuous hη, ?_⟩
    filter_upwards [hgiAE] with x hx
    intro hxU
    rw [hx hxU, hki]
    exact quadratic_coordinate (A x) i
  obtain ⟨kj, hkj⟩ := hcoord j
  obtain ⟨kp, hkp⟩ := hpair i j hij
  obtain ⟨gj, hgj, hgjAE⟩ := hrep kj
  obtain ⟨gp, hgp, hgpAE⟩ := hrep kp
  let g := gp + (-1 / 2 : ℝ) • (gi + gj)
  have hn : ‖(-1 / 2 : ℝ)‖₊ = (1 / 2 : ℝ≥0) := by
    apply NNReal.coe_injective
    norm_num
  have hc : C + (C + C) * ‖(-1 / 2 : ℝ)‖₊ = 2 * C := by norm_num [hn]; ring
  have hg : HolderWith (2 * C) η g := by
    simpa only [hc] using hgp.add ((hgi.add hgj).smul (-1 / 2 : ℝ))
  refine ⟨g, hg, hg.continuous hη, ?_⟩
  filter_upwards [hSym, hgiAE, hgjAE, hgpAE] with x hxSym hxi hxj hxp
  intro hxU
  simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hxp hxU, hxi hxU, hxj hxU, hkp, hki, hkj, quadratic_coordinate, quadratic_coordinate,
    quadratic_normalized_pair (A x) hxSym i j]
  ring

end FunctionalInequalities.Analysis

end MatrixEntryHolder

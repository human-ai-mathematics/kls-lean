module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Determinant arithmetic-geometric mean and Minkowski inequalities

Matrix supports for the contact-density step of Caffarelli's nonlinear interior
W²,p argument (Annals of Mathematics 131 (1990), 135–150, DOI 10.2307/1971510),
used by Berman–Berndtsson arXiv:1207.6128v1 Theorem 2.24(ii) and the literal
convex-source class in Letwin arXiv:2607.24164v1 Lemma 2.2.

For real positive semidefinite matrices in every positive dimension, scalar
AM–GM on nonnegative eigenvalues gives `det A ^ (1/n) ≤ tr A / n`.
Conjugation by the inverse positive square root of `A + B` then proves
Minkowski's determinant-root inequality when the sum is positive definite.
Neither summand need be invertible, and no commutation is assumed.

The residual determinant consequence retains singular positive semidefinite
residuals and a unit-determinant positive reference, with the exact bound
`det A ≤ (ε + δ)^n`. These are matrix facts only; comparison-solution existence,
contact Monge–Ampère measure control and Sobolev regularity are separate steps.
-/

@[expose] public section

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace FunctionalInequalities.Analysis

/-- Matrix arithmetic-geometric mean inequality. The residual matrix can
be singular: nonnegative eigenvalues suffice for the actual scalar AM-GM proof. -/
theorem det_root_le_trace_div {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : Real.rpow A.det (1 / (n : ℝ)) ≤ A.trace / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let a : Fin n → ℝ := hA.isHermitian.eigenvalues
  have ha : ∀ i ∈ Finset.univ, 0 ≤ a i := fun i _ => hA.eigenvalues_nonneg i
  have hw : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin n => 1 / (n : ℝ)) a
      (by intro i _; positivity) hw ha
  rw [Real.finsetProd_rpow Finset.univ a ha] at h
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  simpa only [Real.rpow_eq_pow, a, ← Finset.mul_sum, div_eq_mul_inv, one_div, mul_comm,
    mul_one] using h

/-- Determinant-root Minkowski for PSD matrices whose sum is positive definite.
Neither summand need be invertible, and they need not commute. -/
theorem det_root_add_le {n : ℕ} (hn : 0 < n)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hS : (A + B).PosDef) :
    Real.rpow A.det (1 / (n : ℝ)) + Real.rpow B.det (1 / (n : ℝ)) ≤
      Real.rpow (A + B).det (1 / (n : ℝ)) := by
  let S := A + B
  let Q := CFC.sqrt S
  let R := Q⁻¹
  have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
  have hQQ : Q * Q = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hQunit : IsUnit Q := (IsStrictlyPositive.sqrt S hS.isStrictlyPositive).isUnit
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQunit
  have hleft : R * Q = 1 := Matrix.nonsing_inv_mul Q hQdet
  have hright : Q * R = 1 := Matrix.mul_nonsing_inv Q hQdet
  have hR : R.PosSemidef := hQ.inv
  have hRSR : R * S * R = 1 := by
    rw [← hQQ]
    calc
      R * (Q * Q) * R = (R * Q) * (Q * R) := by noncomm_ring
      _ = 1 := by rw [hleft, hright, one_mul]
  let X := R * A * R
  let Y := R * B * R
  have hX : X.PosSemidef := by
    simpa only [hR.isHermitian.eq] using hA.mul_mul_conjTranspose_same R
  have hY : Y.PosSemidef := by
    simpa only [hR.isHermitian.eq] using hB.mul_mul_conjTranspose_same R
  have hXY : X + Y = 1 := by
    change R * A * R + R * B * R = 1
    calc
      _ = R * S * R := by dsimp [S]; noncomm_ring
      _ = 1 := hRSR
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsum : Real.rpow X.det (1 / (n : ℝ)) + Real.rpow Y.det (1 / (n : ℝ)) ≤ 1 := by
    calc
      _ ≤ X.trace / (n : ℝ) + Y.trace / (n : ℝ) :=
        add_le_add (det_root_le_trace_div hn hX) (det_root_le_trace_div hn hY)
      _ = (X.trace + Y.trace) / (n : ℝ) := by ring
      _ = 1 := by rw [← Matrix.trace_add, hXY, Matrix.trace_one, Fintype.card_fin]; field_simp
  have hdet (M : Matrix (Fin n) (Fin n) ℝ) : (R * M * R).det = R.det ^ 2 * M.det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    ring
  have hnorm : R.det ^ 2 * S.det = 1 := by
    rw [← hdet S, hRSR, Matrix.det_one]
  have hfactor : 0 < R.det ^ 2 := by
    have hnonneg := sq_nonneg R.det
    by_contra h
    have hz : R.det ^ 2 = 0 := le_antisymm (le_of_not_gt h) hnonneg
    rw [hz, zero_mul] at hnorm
    norm_num at hnorm
  have hk : 0 < Real.rpow (R.det ^ 2) (1 / (n : ℝ)) :=
    Real.rpow_pos_of_pos hfactor _
  have hprod : Real.rpow (R.det ^ 2) (1 / (n : ℝ)) *
      Real.rpow S.det (1 / (n : ℝ)) = 1 := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.mul_rpow hfactor.le hS.det_pos.le,
      hnorm, Real.one_rpow]
  have hXA : Real.rpow X.det (1 / (n : ℝ)) =
      Real.rpow (R.det ^ 2) (1 / (n : ℝ)) * Real.rpow A.det (1 / (n : ℝ)) := by
    change Real.rpow (R * A * R).det _ = _
    rw [hdet, Real.rpow_eq_pow, Real.mul_rpow hfactor.le hA.det_nonneg]
    rfl
  have hYB : Real.rpow Y.det (1 / (n : ℝ)) =
      Real.rpow (R.det ^ 2) (1 / (n : ℝ)) * Real.rpow B.det (1 / (n : ℝ)) := by
    change Real.rpow (R * B * R).det _ = _
    rw [hdet, Real.rpow_eq_pow, Real.mul_rpow hfactor.le hB.det_nonneg]
    rfl
  rw [hXA, hYB] at hsum
  change _ ≤ Real.rpow S.det _
  nlinarith

/-- The exact residual determinant bound at a supporting contact, relative to a
unit-determinant positive reference. The residual may be singular. This is a
matrix inequality; no contact measure or Sobolev conclusion is asserted. -/
theorem det_le_pow_of_det_add_smul_le {n : ℕ} (hn : 0 < n)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hB : B.PosDef)
    (hdetB : B.det = 1) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 ≤ ε)
    (hdet : (A + (1 - δ) • B).det ≤ (1 + ε) ^ n) :
    A.det ≤ (ε + δ) ^ n := by
  have ht : 0 < 1 - δ := by linarith
  have hT : ((1 - δ) • B).PosDef := hB.smul ht
  have hS : (A + (1 - δ) • B).PosDef := by
    simpa only [add_comm] using hT.add_posSemidef hA
  have hM := det_root_add_le hn hA hT.posSemidef hS
  have hrootB : Real.rpow ((1 - δ) • B).det (1 / (n : ℝ)) = 1 - δ := by
    rw [Matrix.det_smul, Fintype.card_fin, hdetB, mul_one, Real.rpow_eq_pow, one_div,
      Real.pow_rpow_inv_natCast ht.le hn.ne']
  have hupper : Real.rpow (A + (1 - δ) • B).det (1 / (n : ℝ)) ≤ 1 + ε := by
    calc
      _ ≤ Real.rpow ((1 + ε) ^ n) (1 / (n : ℝ)) :=
        Real.rpow_le_rpow hS.det_pos.le hdet (by positivity)
      _ = 1 + ε := by
        rw [Real.rpow_eq_pow, one_div, Real.pow_rpow_inv_natCast (by linarith) hn.ne']
  rw [hrootB] at hM
  have hbound : Real.rpow A.det (1 / (n : ℝ)) ≤ ε + δ := by linarith
  have hnneg : 0 ≤ Real.rpow A.det (1 / (n : ℝ)) := Real.rpow_nonneg hA.det_nonneg _
  calc
    A.det = (Real.rpow A.det (1 / (n : ℝ))) ^ n := by
      rw [Real.rpow_eq_pow, one_div, Real.rpow_inv_natCast_pow hA.det_nonneg hn.ne']
    _ ≤ (ε + δ) ^ n := pow_le_pow_left₀ hnneg hbound n

end FunctionalInequalities.Analysis

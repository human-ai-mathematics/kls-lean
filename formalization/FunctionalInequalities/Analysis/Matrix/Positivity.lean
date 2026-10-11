import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Positive semidefinite Gram matrices with a Kronecker weight

`F (A ⊗ A) Fᵀ` is positive semidefinite for positive semidefinite `A`; written out, this is the
four-index Gram matrix used for the third-derivative term of Letwin's Lemma 2.4. Proof bodies: Codex
route bundle `MA-Second-Derivative` (independently accepted); statements and placement: Claude.

Quadratic floors and the Sylvester estimate: `matrixEntries A` is the Euclidean (Frobenius) view of the
entries; `QuadraticFloor S a` is `a‖v‖² ≤ ⟪v, S v⟫`; a positive definite matrix has a positive floor, a floor
is stable under Frobenius-small perturbations, and for floors `a`, `b` and symmetric `T` the identity
`S(S−T) + (S−T)T = S² − T²` (no commutation) gives `‖S − T‖_F ≤ ‖S² − T²‖_F / (a + b)`. Used for the local
Lipschitz property of the principal inverse square root (`Analysis/PrincipalInverseSqrt.lean`). Proof bodies:
Codex q_batch bundle `Principal-Root-Regularity` (independently accepted); statements and placement: Claude.
-/

noncomputable section
open scoped MatrixOrder Kronecker

namespace FunctionalInequalities.Analysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Weighted Gram matrix**: for a positive semidefinite `A` and any family of matrices `T_i`, the matrix
`G_{ij} = Σ_{a,b,c,d} A_{ac} A_{bd} (T_i)_{ab} (T_j)_{cd} = (F (A ⊗ A) Fᵀ)_{ij}` is positive semidefinite. -/
theorem posSemidef_weightedGram (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (T : κ → Matrix ι ι ℝ) :
    (Matrix.of fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
      A a c * A b d * T i a b * T j c d).PosSemidef := by
  let F : Matrix κ (ι × ι) ℝ := fun i ab => T i ab.1 ab.2
  have h := (hA.kronecker hA).mul_mul_conjTranspose_same F
  have heq : F * (A ⊗ₖ A) * F.conjTranspose = Matrix.of (fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
      A a c * A b d * T i a b * T j c d) := by
    rw [Matrix.mul_assoc]
    ext i j
    change (∑ ab : ι × ι, T i ab.1 ab.2 *
      (∑ cd : ι × ι, (A ab.1 cd.1 * A ab.2 cd.2) * T j cd.1 cd.2)) = _
    simp only [Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro b _hb
    apply Finset.sum_congr rfl
    intro c _hc
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  exact heq ▸ h

section Frobenius

open Matrix Finset
open scoped RealInnerProductSpace

/-- Euclidean view of the matrix entries; its norm is the Frobenius norm. -/
def matrixEntries (A : Matrix ι ι ℝ) : EuclideanSpace ℝ (ι × ι) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

theorem matrixEntries_norm_sq (A : Matrix ι ι ℝ) :
    ‖matrixEntries A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Fintype.sum_prod_type _

theorem matrixEntries_inner (A B : Matrix ι ι ℝ) :
    ⟪matrixEntries A, matrixEntries B⟫ = ∑ i, ∑ j, A i j * B i j := by
  rw [PiLp.inner_apply]
  simp only [matrixEntries, PiLp.toLp_apply, Real.inner_apply]
  exact Fintype.sum_prod_type _

omit [Fintype ι] in
theorem matrixEntries_sub (A B : Matrix ι ι ℝ) :
    matrixEntries (A - B) = matrixEntries A - matrixEntries B := by
  ext ij
  rfl

omit [Fintype ι] in
theorem continuous_matrixEntries :
    Continuous (matrixEntries : Matrix ι ι ℝ → EuclideanSpace ℝ (ι × ι)) :=
  (PiLp.continuous_toLp 2 (fun _ : ι × ι => ℝ)).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end Frobenius

section Floor

open Matrix Finset
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

/-- A quadratic lower floor `a ‖v‖² ≤ ⟪v, A v⟫` in coordinates. -/
def QuadraticFloor (A : Matrix ι ι ℝ) (a : ℝ) : Prop :=
  ∀ v : ι → ℝ, a * (∑ i, (v i) ^ 2) ≤ v ⬝ᵥ (A *ᵥ v)

variable [DecidableEq ι]

/-- A Loewner scalar lower bound gives a quadratic floor. -/
theorem quadraticFloor_of_algebraMap_le {S : Matrix ι ι ℝ} {a : ℝ}
    (h : algebraMap ℝ (Matrix ι ι ℝ) a ≤ S) : QuadraticFloor S a := by
  have hp : (S - algebraMap ℝ (Matrix ι ι ℝ) a).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)
  intro v
  have hv := hp.dotProduct_mulVec_nonneg v
  rw [Algebra.algebraMap_eq_smul_one, sub_mulVec, dotProduct_sub,
    smul_mulVec, one_mulVec, dotProduct_smul] at hv
  simp only [star_trivial, smul_eq_mul] at hv
  have he : v ⬝ᵥ v = ∑ i, (v i) ^ 2 := by simp only [dotProduct, pow_two]
  rw [he] at hv
  linarith

/-- A positive definite matrix has a positive quadratic floor (the empty index type gives floor `1`
without any spectrum argument). -/
theorem exists_quadraticFloor_of_posDef {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∃ a : ℝ, 0 < a ∧ QuadraticFloor S a := by
  classical
  by_cases h : Nonempty ι
  · let : Nonempty ι := h
    obtain ⟨a, ha, hle⟩ :=
      (CFC.exists_pos_algebraMap_le_iff hS.isStrictlyPositive.isSelfAdjoint).mpr
        (fun x hx => hS.isStrictlyPositive.spectrum_pos hx)
    exact ⟨a, ha, quadraticFloor_of_algebraMap_le hle⟩
  · have : IsEmpty ι := not_nonempty_iff.mp h
    refine ⟨1, by norm_num, ?_⟩
    intro v
    simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, le_refl]

private def outer (v : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i * v j

omit [DecidableEq ι] in
private theorem outer_norm (v : ι → ℝ) : ‖matrixEntries (outer v)‖ = ∑ i, (v i) ^ 2 := by
  have he : ‖matrixEntries (outer v)‖ ^ 2 = (∑ i, (v i) ^ 2) ^ 2 := by
    rw [matrixEntries_norm_sq]
    simp only [outer, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hp : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _hi => sq_nonneg _
  nlinarith [norm_nonneg (matrixEntries (outer v))]

omit [DecidableEq ι] in
private theorem outer_inner (D : Matrix ι ι ℝ) (v : ι → ℝ) :
    ⟪matrixEntries D, matrixEntries (outer v)⟫ = v ⬝ᵥ (D *ᵥ v) := by
  rw [matrixEntries_inner]
  simp only [outer, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

omit [DecidableEq ι] in
/-- The quadratic form is controlled by the Frobenius norm. -/
theorem abs_dotProduct_mulVec_le (D : Matrix ι ι ℝ) (v : ι → ℝ) :
    |v ⬝ᵥ (D *ᵥ v)| ≤ ‖matrixEntries D‖ * (∑ i, (v i) ^ 2) := by
  rw [← outer_inner, ← outer_norm]
  simpa only [Real.norm_eq_abs] using
    norm_inner_le_norm (𝕜 := ℝ) (matrixEntries D) (matrixEntries (outer v))

omit [DecidableEq ι] in
/-- A floor persists, halved, under a Frobenius perturbation of size at most `a / 2`. -/
theorem quadraticFloor_of_close {S S0 : Matrix ι ι ℝ} {a : ℝ} (hfloor : QuadraticFloor S0 a)
    (hclose : ‖matrixEntries (S - S0)‖ ≤ a / 2) : QuadraticFloor S (a / 2) := by
  intro v
  have hbase := hfloor v
  have hdiff := abs_dotProduct_mulVec_le (S - S0) v
  have hq : v ⬝ᵥ ((S - S0) *ᵥ v) = v ⬝ᵥ (S *ᵥ v) - v ⬝ᵥ (S0 *ᵥ v) := by
    rw [sub_mulVec, dotProduct_sub]
  rw [hq] at hdiff
  have hp : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _hi => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hclose hp
  have hneg := neg_abs_le (v ⬝ᵥ S *ᵥ v - v ⬝ᵥ S0 *ᵥ v)
  nlinarith [hdiff, hmul, hneg]

end Floor

section Sylvester

open Matrix Finset
open scoped RealInnerProductSpace

variable [DecidableEq ι]

omit [DecidableEq ι] in
private theorem left_floor (S D : Matrix ι ι ℝ) {a : ℝ} (hS : QuadraticFloor S a) :
    a * (∑ i, ∑ j, (D i j) ^ 2) ≤ ∑ i, ∑ j, D i j * (S * D) i j := by
  calc
    a * (∑ i, ∑ j, (D i j) ^ 2) = ∑ j, a * (∑ i, (D i j) ^ 2) := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ j, ∑ i, D i j * (S * D) i j := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [QuadraticFloor, dotProduct, mulVec, Matrix.mul_apply] using hS (fun i => D i j)
    _ = ∑ i, ∑ j, D i j * (S * D) i j := Finset.sum_comm

omit [DecidableEq ι] in
private theorem right_floor (T D : Matrix ι ι ℝ) {b : ℝ} (hT : QuadraticFloor T b)
    (hSym : ∀ i j, T i j = T j i) :
    b * (∑ i, ∑ j, (D i j) ^ 2) ≤ ∑ i, ∑ j, D i j * (D * T) i j := by
  have he (i j : ι) : (D * T) i j = (T *ᵥ (fun k => D i k)) j := by
    simp only [Matrix.mul_apply, mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [hSym k j]
    ring
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  simp_rw [he]
  exact hT (fun j => D i j)

omit [DecidableEq ι] in
/-- **Sylvester coercivity**: `(a + b)‖D‖_F² ≤ ⟪D, SD + DT⟫_F` for floors `a`, `b` and symmetric `T`; no
commutation assumption. -/
theorem sylvester_coercivity (S T D : Matrix ι ι ℝ) {a b : ℝ}
    (hS : QuadraticFloor S a) (hT : QuadraticFloor T b) (hSym : ∀ i j, T i j = T j i) :
    (a + b) * ‖matrixEntries D‖ ^ 2 ≤ ⟪matrixEntries D, matrixEntries (S * D + D * T)⟫ := by
  rw [matrixEntries_norm_sq, matrixEntries_inner]
  have hl := left_floor S D hS
  have hr := right_floor T D hT hSym
  calc
    (a + b) * (∑ i, ∑ j, (D i j) ^ 2) =
        a * (∑ i, ∑ j, (D i j) ^ 2) + b * (∑ i, ∑ j, (D i j) ^ 2) := by ring
    _ ≤ (∑ i, ∑ j, D i j * (S * D) i j) + (∑ i, ∑ j, D i j * (D * T) i j) := add_le_add hl hr
    _ = ∑ i, ∑ j, D i j * (S * D + D * T) i j := by
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- **Root difference bound**: `(a + b)‖S − T‖_F ≤ ‖S² − T²‖_F` from the identity
`S(S − T) + (S − T)T = S² − T²`, which holds without commutation. -/
theorem root_difference_bound (S T : Matrix ι ι ℝ) {a b : ℝ}
    (hS : QuadraticFloor S a) (hT : QuadraticFloor T b) (hSym : ∀ i j, T i j = T j i) :
    (a + b) * ‖matrixEntries (S - T)‖ ≤ ‖matrixEntries (S * S - T * T)‖ := by
  have hid : S * (S - T) + (S - T) * T = S * S - T * T := by noncomm_ring
  have hlo := sylvester_coercivity S T (S - T) hS hT hSym
  rw [hid] at hlo
  have hupper : ⟪matrixEntries (S - T), matrixEntries (S * S - T * T)⟫ ≤
      ‖matrixEntries (S - T)‖ * ‖matrixEntries (S * S - T * T)‖ := by
    have hc : |⟪matrixEntries (S - T), matrixEntries (S * S - T * T)⟫| ≤
        ‖matrixEntries (S - T)‖ * ‖matrixEntries (S * S - T * T)‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ)
        (matrixEntries (S - T)) (matrixEntries (S * S - T * T))
    exact (le_abs_self _).trans hc
  by_cases hz : ‖matrixEntries (S - T)‖ = 0
  · rw [hz, mul_zero]
    exact norm_nonneg _
  have hd : 0 < ‖matrixEntries (S - T)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have h := hlo.trans hupper
  have h' : ‖matrixEntries (S - T)‖ * ((a + b) * ‖matrixEntries (S - T)‖) ≤
      ‖matrixEntries (S - T)‖ * ‖matrixEntries (S * S - T * T)‖ := by
    nlinarith only [h]
  exact (mul_le_mul_iff_right₀ hd).mp h'

theorem root_difference_le_div (S T : Matrix ι ι ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hS : QuadraticFloor S a) (hT : QuadraticFloor T b)
    (hSym : ∀ i j, T i j = T j i) :
    ‖matrixEntries (S - T)‖ ≤ ‖matrixEntries (S * S - T * T)‖ / (a + b) := by
  apply (le_div_iff₀ (add_pos ha hb)).mpr
  simpa only [mul_comm] using root_difference_bound S T hS hT hSym

end Sylvester

end FunctionalInequalities.Analysis

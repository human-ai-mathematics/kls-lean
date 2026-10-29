import FunctionalInequalities.Analysis.BakryEmery.MongeAmpere

/-!
# Trace evolution of the Hessian under the inverse-Hessian operator

For a smooth `φ` on a finite-dimensional real inner-product space, `stdHessianMatrix φ x` is the Hessian matrix of `φ` in the
standard orthonormal basis (index type `StdBasisIndex E`), `stdHessianMatrixDeriv φ x a` its derivative along the `a`-th
basis vector, and `stdHessianMatrixGenerator φ V x` its entrywise image under the inverse-Hessian operator
`L = hessianInverseOperator φ V`. For every constant real matrix `B` and every point `x`
(`hessianInverseOperator_trace_stdHessianMatrix_sq`):
`L tr(B H B H) = 2 tr(B H B (L H)) + 2 Σ_ab A^{ab} tr(B ∂_a H B ∂_b H)` with `A = (∇²φ)⁻¹` (`inverseHessianEntry`), the
pointwise trace identity (2.8) of Letwin, arXiv:2607.24164v1, in the proof of Theorem 2.5. There is no positive
semidefiniteness, commutation or Monge–Ampère premise. Not provided: the substitution of the twice-differentiated
Monge–Ampère equation, (2.10), the tensor comparison and the trace bound of Theorem 2.5.

Monge–Ampère substitution (section `MongeAmpereTrace`). For a GIVEN smooth `φ` with positive definite Hessian at every
point satisfying the zero-order Monge–Ampère relation `log det ∇²φ = −φ + V(∇φ)`, with `V` smooth only on an open `U ⊇
closure K` and `range ∇φ ⊆ K`: Letwin (2.9), `L H = −H + H ∇²V(∇φ) H + G` with the inverse-Hessian third-derivative Gram
matrix `G = stdThirdGram φ x` (`stdHessianMatrixGenerator_apply_on_range`, `stdHessianMatrixGenerator_eq_on_range`), and
(2.10) for every constant real `B` (`traceGenerator_210_on_range`). If moreover `K` is open, `V` convex on `K` and `B`
positive semidefinite, the three remainders `Σ A^{ab} tr(B∂_aH B∂_bH)`, `tr(BHB·H∇²V(∇φ)H)` and `tr(BHB·G)` are
nonnegative, hence `L tr(BHBH) + 2 tr(BHBH) ≥ 0` pointwise (`traceGeneratorCondition_on_range`). This is the pointwise
condition before Lemma A.5; its integration (A.4/A.5 for this trace function), the moment map of an arbitrary source law
and the trace bound of Theorem 2.5 are not provided.
-/

noncomputable section

open scoped BigOperators ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open Matrix

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev StdBasisIndex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] := Fin (Module.finrank ℝ E)

def stdHessianMatrix (φ : E → ℝ) (x : E) : Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ :=
  hessianMatrixIn φ (stdOrthonormalBasis ℝ E) x

def stdHessianMatrixDeriv (φ : E → ℝ) (x : E) (a : StdBasisIndex E) :
    Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ :=
  fun i j => fderiv ℝ
    (fun y => hessianMatrixIn φ (stdOrthonormalBasis ℝ E) y i j) x
    (stdOrthonormalBasis ℝ E a)

def stdHessianMatrixGenerator (φ V : E → ℝ) (x : E) : Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ :=
  fun i j => hessianInverseOperator φ V
    (fun y => hessianMatrixIn φ (stdOrthonormalBasis ℝ E) y i j) x

private lemma contDiff_two_stdHessianMatrix_apply {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i j : StdBasisIndex E) :
    ContDiff ℝ 2 (fun y => stdHessianMatrix φ y i j) := by
  unfold stdHessianMatrix
  exact (contDiff_bilinearIteratedFDerivTwo_apply hφ
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)).of_le
    (WithTop.coe_le_coe.mpr le_top)

private lemma hessianInverseOperator_const {φ : E → ℝ} (_hφ : ContDiff ℝ 2 φ)
    (V : E → ℝ) (c : ℝ) (x : E) :
    hessianInverseOperator φ V (fun _ : E => c) x = 0 := by
  have hz (i j : StdBasisIndex E) :
      bilinearIteratedFDerivTwo ℝ (fun _ : E => c) x
          (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) = 0 := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply contDiff_const]
    simp
  unfold hessianInverseOperator nondivergenceOperator
  simp [hz]

private lemma hessianInverseOperator_const_mul {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (V : E → ℝ) {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E) :
    hessianInverseOperator φ V (fun y => c * f y) x =
      c * hessianInverseOperator φ V f x := by
  have h := hessianInverseOperator_mul hφ V
    (f := fun _ : E => c) (g := f) contDiff_const hf x
  rw [hessianInverseOperator_const hφ V c x] at h
  simpa using h

private lemma hessianInverseOperator_trace_mul
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (V : E → ℝ)
    {A C : E → Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ}
    (hA : ∀ i j, ContDiff ℝ 2 (fun y => A y i j))
    (hC : ∀ i j, ContDiff ℝ 2 (fun y => C y i j)) (x : E) :
    hessianInverseOperator φ V (fun y => (A y * C y).trace) x =
        Matrix.trace
          (@HMul.hMul
            (Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ)
            (Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ)
            (Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ)
            inferInstance
            (A x)
            (fun i j => hessianInverseOperator φ V
              (fun y => C y i j) x)) +
      Matrix.trace
        (@HMul.hMul
          (Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ)
          (Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ)
          (Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ)
          inferInstance
          (fun i j => hessianInverseOperator φ V
            (fun y => A y i j) x)
          (C x)) +
      2 * ∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
        Matrix.trace
          (@HMul.hMul
            (Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ)
            (Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ)
            (Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ)
            inferInstance
            (fun a b => fderiv ℝ (fun y => A y a b) x
              (stdOrthonormalBasis ℝ E i))
            (fun a b => fderiv ℝ (fun y => C y a b) x
              (stdOrthonormalBasis ℝ E j))) := by
  change hessianInverseOperator φ V
      (fun y => ∑ a, ∑ b, A y a b * C y b a) x =
    (∑ a, ∑ b, A x a b * hessianInverseOperator φ V
      (fun y => C y b a) x) +
    (∑ a, ∑ b, hessianInverseOperator φ V
      (fun y => A y a b) x * C x b a) +
    2 * ∑ i, ∑ j, inverseHessianEntry φ
      (stdOrthonormalBasis ℝ E) x i j *
      (∑ a, ∑ b,
        (fderiv ℝ (fun y => A y a b) x (stdOrthonormalBasis ℝ E i)) *
        (fderiv ℝ (fun y => C y b a) x (stdOrthonormalBasis ℝ E j)))
  have hsecond :
      (∑ a, ∑ b, C x b a * hessianInverseOperator φ V
        (fun y => A y a b) x) =
      ∑ a, ∑ b, hessianInverseOperator φ V
        (fun y => A y a b) x * C x b a := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact mul_comm _ _
  have hgrad :
      (∑ a, ∑ b, ∑ i, ∑ j, inverseHessianEntry φ
        (stdOrthonormalBasis ℝ E) x i j *
        (fderiv ℝ (fun y => A y a b) x (stdOrthonormalBasis ℝ E i)) *
        (fderiv ℝ (fun y => C y b a) x (stdOrthonormalBasis ℝ E j))) =
      ∑ i, ∑ j, inverseHessianEntry φ
        (stdOrthonormalBasis ℝ E) x i j *
        (∑ a, ∑ b,
          (fderiv ℝ (fun y => A y a b) x (stdOrthonormalBasis ℝ E i)) *
          (fderiv ℝ (fun y => C y b a) x (stdOrthonormalBasis ℝ E j))) := by
    simp_rw [Finset.mul_sum, mul_assoc]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    exact Finset.sum_comm
  calc
    _ = ∑ a, ∑ b, hessianInverseOperator φ V
          (fun y => A y a b * C y b a) x := by
      rw [hessianInverseOperator_sum Finset.univ φ V (f := fun a y => ∑ b, A y a b * C y b a)
        (fun a _ => ContDiff.sum fun b _ => (hA a b).mul (hC b a)) x]
      apply Finset.sum_congr rfl
      intro a _
      rw [hessianInverseOperator_sum Finset.univ φ V (f := fun b y => A y a b * C y b a)
        (fun b _ => (hA a b).mul (hC b a)) x]
    _ = ∑ a, ∑ b,
        (A x a b * hessianInverseOperator φ V (fun y => C y b a) x +
          C x b a * hessianInverseOperator φ V (fun y => A y a b) x +
          2 * ∑ i, ∑ j, inverseHessianEntry φ
            (stdOrthonormalBasis ℝ E) x i j *
            (fderiv ℝ (fun y => A y a b) x (stdOrthonormalBasis ℝ E i)) *
            (fderiv ℝ (fun y => C y b a) x (stdOrthonormalBasis ℝ E j))) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact hessianInverseOperator_mul hφ V (hA a b) (hC b a) x
    _ = (∑ a, ∑ b, A x a b * hessianInverseOperator φ V
          (fun y => C y b a) x) +
        (∑ a, ∑ b, C x b a * hessianInverseOperator φ V
          (fun y => A y a b) x) +
        2 * (∑ a, ∑ b, ∑ i, ∑ j, inverseHessianEntry φ
          (stdOrthonormalBasis ℝ E) x i j *
          (fderiv ℝ (fun y => A y a b) x (stdOrthonormalBasis ℝ E i)) *
          (fderiv ℝ (fun y => C y b a) x (stdOrthonormalBasis ℝ E j))) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
      rw [hsecond, hgrad]

/-- The trace-square identity for the actual Hessian field and an arbitrary fixed real matrix. -/
theorem hessianInverseOperator_trace_stdHessianMatrix_sq
    {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (B : Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ) (x : E) :
    hessianInverseOperator φ V
        (fun y => (B * stdHessianMatrix φ y * B * stdHessianMatrix φ y).trace) x =
      2 * (B * stdHessianMatrix φ x * B * stdHessianMatrixGenerator φ V x).trace +
        2 * ∑ a, ∑ b,
          inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a b *
            (B * stdHessianMatrixDeriv φ x a * B * stdHessianMatrixDeriv φ x b).trace := by
  classical
  let hφ2 : ContDiff ℝ 2 φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hF : ∀ i j : StdBasisIndex E,
      ContDiff ℝ 2 (fun y => (B * stdHessianMatrix φ y) i j) := by
    intro i j
    change ContDiff ℝ 2 (fun y => ∑ l, B i l * stdHessianMatrix φ y l j)
    exact ContDiff.sum fun l _ => contDiff_const.mul
      (contDiff_two_stdHessianMatrix_apply hφ l j)
  have hLF :
      (fun i j => hessianInverseOperator φ V
        (fun y => (B * stdHessianMatrix φ y) i j) x) =
        B * stdHessianMatrixGenerator φ V x := by
    ext i j
    change hessianInverseOperator φ V
        (fun y => ∑ l, B i l * stdHessianMatrix φ y l j) x =
      ∑ l, B i l * hessianInverseOperator φ V
        (fun y => stdHessianMatrix φ y l j) x
    rw [hessianInverseOperator_sum Finset.univ φ V (f := fun l y => B i l * stdHessianMatrix φ y l j)
      (fun l _ => contDiff_const.mul
        (contDiff_two_stdHessianMatrix_apply hφ l j)) x]
    apply Finset.sum_congr rfl
    intro l _
    exact hessianInverseOperator_const_mul hφ2 V
      (contDiff_two_stdHessianMatrix_apply hφ l j) (B i l) x
  have hDF : ∀ a : StdBasisIndex E,
      (fun i j => fderiv ℝ (fun y => (B * stdHessianMatrix φ y) i j) x
        (stdOrthonormalBasis ℝ E a)) = B * stdHessianMatrixDeriv φ x a := by
    intro a
    ext i j
    change fderiv ℝ (fun y => ∑ l, B i l * stdHessianMatrix φ y l j) x
        (stdOrthonormalBasis ℝ E a) =
      ∑ l, B i l * fderiv ℝ (fun y => stdHessianMatrix φ y l j) x
        (stdOrthonormalBasis ℝ E a)
    have hs := fderiv_sum_apply (E := E)
      (s := (Finset.univ : Finset (StdBasisIndex E)))
      (g := fun l y => B i l * stdHessianMatrix φ y l j) (x := x)
      (fun l _ => ((contDiff_const.mul
        (contDiff_two_stdHessianMatrix_apply hφ l j)).differentiable (by norm_num) x))
      (stdOrthonormalBasis ℝ E a)
    rw [show fderiv ℝ (fun y => ∑ l, B i l * stdHessianMatrix φ y l j) x
        (stdOrthonormalBasis ℝ E a) =
        ∑ l, fderiv ℝ (fun y => B i l * stdHessianMatrix φ y l j) x
          (stdOrthonormalBasis ℝ E a) by simpa using hs]
    apply Finset.sum_congr rfl
    intro l _
    exact fderiv_const_mul_apply
      ((contDiff_two_stdHessianMatrix_apply hφ l j).differentiable (by norm_num) x)
      (B i l) (stdOrthonormalBasis ℝ E a)
  have hmain := hessianInverseOperator_trace_mul hφ2 V
    (A := fun y => B * stdHessianMatrix φ y)
    (C := fun y => B * stdHessianMatrix φ y) hF hF x
  rw [hLF] at hmain
  simp_rw [hDF] at hmain
  rw [Matrix.trace_mul_comm (B * stdHessianMatrixGenerator φ V x) (B * stdHessianMatrix φ x)] at hmain
  simpa [Matrix.mul_assoc, two_mul] using hmain

section MongeAmpereTrace

open scoped Kronecker
open MeasureTheory

/-- The actual Hessian-conjugation term, initially written entrywise. -/
def stdHessianConjugate (φ V : E → ℝ) (x : E) :
    Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ :=
  fun i j => ∑ a, ∑ c,
    stdHessianMatrix φ x i a *
      hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) a c *
      stdHessianMatrix φ x c j

/-- The actual inverse-Hessian-weighted third-derivative Gram matrix. -/
def stdThirdGram (φ : E → ℝ) (x : E) :
    Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ :=
  fun i j => ∑ a, ∑ c, ∑ p, ∑ q,
    inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a p *
      inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x c q *
      stdHessianMatrixDeriv φ x i a c * stdHessianMatrixDeriv φ x j p q

theorem stdHessianConjugate_eq (φ V : E → ℝ) (x : E) :
    stdHessianConjugate φ V x =
      stdHessianMatrix φ x *
        hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
        stdHessianMatrix φ x := by
  classical
  ext i j
  rw [Matrix.mul_assoc]
  change
    (∑ a, ∑ c, stdHessianMatrix φ x i a *
      hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) a c *
      stdHessianMatrix φ x c j) =
    ∑ a, stdHessianMatrix φ x i a *
      (∑ c, hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) a c *
        stdHessianMatrix φ x c j)
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Symmetry is derived for the actual differentiated Hessian entries. -/
theorem stdHessianMatrixDeriv_isSymm {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : E) (a : StdBasisIndex E) : (stdHessianMatrixDeriv φ x a).IsSymm := by
  have h2 : ContDiff ℝ 2 φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  change (stdHessianMatrixDeriv φ x a).transpose = stdHessianMatrixDeriv φ x a
  ext i j
  change
    fderiv ℝ (fun y => hessianMatrixIn φ (stdOrthonormalBasis ℝ E) y j i)
      x (stdOrthonormalBasis ℝ E a) =
    fderiv ℝ (fun y => hessianMatrixIn φ (stdOrthonormalBasis ℝ E) y i j)
      x (stdOrthonormalBasis ℝ E a)
  have he :
      (fun y => hessianMatrixIn φ (stdOrthonormalBasis ℝ E) y j i) =
      (fun y => hessianMatrixIn φ (stdOrthonormalBasis ℝ E) y i j) := by
    funext y
    exact bilinearIteratedFDerivTwo_symm h2 y
      (stdOrthonormalBasis ℝ E j) (stdOrthonormalBasis ℝ E i)
  rw [he]

theorem stdHessianMatrix_posSemidef {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    (stdHessianMatrix φ x).PosSemidef := by
  have h2 : ContDiff ℝ 2 φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  apply hessianMatrixIn_posSemidef (stdOrthonormalBasis ℝ E) h2.contDiffAt
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · exact (hPD v hv).le

theorem stdInverseHessian_posSemidef {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    (Matrix.of fun i j =>
      inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j).PosSemidef := by
  have h2 : ContDiff ℝ 2 φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have h := inv_hessianMatrixIn_posSemidef
    (stdOrthonormalBasis ℝ E) h2 hPD
  rw [inv_hessianMatrixIn (stdOrthonormalBasis ℝ E) h2 x hPD] at h
  exact h

theorem stdHessianConjugate_posSemidef {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {K U : Set E} (hK : IsOpen K)
    (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hc : ConvexOn ℝ K V) (hRange : Set.range (gradient φ) ⊆ K) (x : E) :
    (stdHessianConjugate φ V x).PosSemidef := by
  exact posSemidef_hessian_conj_hessian_on_range (stdOrthonormalBasis ℝ E)
    (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hK hKU
    (hV.of_le (WithTop.coe_le_coe.mpr le_top)) hc hRange x

theorem stdThirdGram_posSemidef {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    (stdThirdGram φ x).PosSemidef := by
  exact posSemidef_inverseHessian_third_gram
    (stdOrthonormalBasis ℝ E) hφ x hPD

theorem posSemidef_mul_stdHessianMatrix_mul {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (B : Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ) (hB : B.PosSemidef) :
    (B * stdHessianMatrix φ x * B).PosSemidef := by
  have h := (stdHessianMatrix_posSemidef hφ x hPD).mul_mul_conjTranspose_same B
  rw [hB.isHermitian] at h
  exact h

/-- Letwin (2.9), entrywise, obtained from the actual second derivative of the
zero-order Monge–Ampère equation. Convexity is not required for this identity. -/
theorem stdHessianMatrixGenerator_apply_on_range {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {K U : Set E} (hU : IsOpen U)
    (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hRange : Set.range (gradient φ) ⊆ K)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y =
      -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (x : E) (i j : StdBasisIndex E) :
    stdHessianMatrixGenerator φ V x i j = -stdHessianMatrix φ x i j +
      (stdHessianMatrix φ x *
        hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
        stdHessianMatrix φ x) i j + stdThirdGram φ x i j := by
  rw [← stdHessianConjugate_eq]
  have h := mongeAmpere_second_derivative_on_range
    hφ hU hKU hV hRange hMA hPD x i j
  change stdHessianMatrixGenerator φ V x i j + stdHessianMatrix φ x i j =
    stdHessianConjugate φ V x i j + stdThirdGram φ x i j at h
  linarith

/-- Matrix form of the actual entrywise (2.9). -/
theorem stdHessianMatrixGenerator_eq_on_range {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {K U : Set E} (hU : IsOpen U)
    (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hRange : Set.range (gradient φ) ⊆ K)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y =
      -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (x : E) :
    stdHessianMatrixGenerator φ V x = -stdHessianMatrix φ x +
      stdHessianMatrix φ x *
        hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
        stdHessianMatrix φ x + stdThirdGram φ x := by
  ext i j
  exact stdHessianMatrixGenerator_apply_on_range hφ hU hKU hV hRange hMA hPD x i j

/-- Letwin (2.10), with all signs and factors of two, for every fixed real B.
No symmetry or positivity of B is required for the identity. -/
theorem traceGenerator_210_on_range {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {K U : Set E} (hU : IsOpen U)
    (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hRange : Set.range (gradient φ) ⊆ K)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y =
      -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (B : Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ) (x : E) :
    hessianInverseOperator φ V
        (fun y => (B * stdHessianMatrix φ y * B * stdHessianMatrix φ y).trace) x =
      -2 * (B * stdHessianMatrix φ x * B * stdHessianMatrix φ x).trace +
      2 * ∑ a, ∑ b,
        inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a b *
          (B * stdHessianMatrixDeriv φ x a * B * stdHessianMatrixDeriv φ x b).trace +
      2 * (B * stdHessianMatrix φ x * B *
        (stdHessianMatrix φ x *
          hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
          stdHessianMatrix φ x)).trace +
      2 * (B * stdHessianMatrix φ x * B * stdThirdGram φ x).trace := by
  rw [hessianInverseOperator_trace_stdHessianMatrix_sq hφ B x,
    stdHessianMatrixGenerator_eq_on_range hφ hU hKU hV hRange hMA hPD x]
  simp only [mul_add, mul_neg, Matrix.trace_add, Matrix.trace_neg]
  ring

/-- Positivity of the weighted derivative trace comes from the actual inverse
Hessian and a PSD Gram matrix, not entrywise positivity of the summands. -/
theorem weightedDerivativeTrace_nonneg {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (B : Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ) (hB : B.PosSemidef) :
    0 ≤ ∑ a, ∑ b,
      inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a b *
        (B * stdHessianMatrixDeriv φ x a * B * stdHessianMatrixDeriv φ x b).trace := by
  exact sum_entry_mul_nonneg (stdInverseHessian_posSemidef hφ x hPD)
    (traceGram_posSemidef B hB (stdHessianMatrixDeriv φ x) (stdHessianMatrixDeriv_isSymm hφ x))

theorem hessianConjugateTrace_nonneg_on_range {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {K U : Set E} (hK : IsOpen K)
    (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hc : ConvexOn ℝ K V) (hRange : Set.range (gradient φ) ⊆ K)
    (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (B : Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ) (hB : B.PosSemidef) :
    0 ≤ (B * stdHessianMatrix φ x * B *
      (stdHessianMatrix φ x *
        hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
        stdHessianMatrix φ x)).trace := by
  rw [← stdHessianConjugate_eq]
  exact trace_mul_nonneg (posSemidef_mul_stdHessianMatrix_mul hφ x hPD B hB)
    (stdHessianConjugate_posSemidef hφ hK hKU hV hc hRange x)

theorem thirdGramTrace_nonneg {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (B : Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ) (hB : B.PosSemidef) :
    0 ≤ (B * stdHessianMatrix φ x * B * stdThirdGram φ x).trace := by
  exact trace_mul_nonneg (posSemidef_mul_stdHessianMatrix_mul hφ x hPD B hB)
    (stdThirdGram_posSemidef hφ x hPD)

/-- The pointwise generator condition used before invoking Lemma A.5.
This theorem supplies no integration or global trace estimate. -/
theorem traceGeneratorCondition_on_range {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {K U : Set E} (hK : IsOpen K) (hU : IsOpen U)
    (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hc : ConvexOn ℝ K V) (hRange : Set.range (gradient φ) ⊆ K)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y =
      -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (B : Matrix (StdBasisIndex E) (StdBasisIndex E) ℝ) (hB : B.PosSemidef) (x : E) :
    0 ≤ hessianInverseOperator φ V
        (fun y => (B * stdHessianMatrix φ y * B * stdHessianMatrix φ y).trace) x +
      2 * (B * stdHessianMatrix φ x * B * stdHessianMatrix φ x).trace := by
  have hD := weightedDerivativeTrace_nonneg hφ x (hPD x) B hB
  have hC := hessianConjugateTrace_nonneg_on_range
    hφ hK hKU hV hc hRange x (hPD x) B hB
  have hG := thirdGramTrace_nonneg hφ x (hPD x) B hB
  rw [traceGenerator_210_on_range hφ hU hKU hV hRange hMA hPD B x]
  linarith

end MongeAmpereTrace

end FunctionalInequalities.Analysis.BakryEmery

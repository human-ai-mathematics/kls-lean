module

public import FunctionalInequalities.KLS.Letwin.MomentCalculus
public import FunctionalInequalities.KLS.LogConcave.BrascampLieb
public import FunctionalInequalities.KLS.LogConcave.HessianTrace
public import FunctionalInequalities.KLS.Isotropic
public import FunctionalInequalities.Analysis.Matrix.Integral
public import FunctionalInequalities.Analysis.Matrix.Trace.Energy
public import FunctionalInequalities.Analysis.Matrix.Trace.Gram

/-!
# Letwin Theorem 2.5 for a given smooth moment map

Letwin, arXiv:2607.24164v1, Theorem 2.5 (pp. 8–12), in the paper's own conditional form. The paper
imports Lemma 2.2 (Klartag [41]: the moment map is smooth with positive definite Hessian, its
gradient maps onto `K` and the Monge–Ampère equation holds pointwise) and the Hessian bound
`∇²φ ≤ 2 sup_K |x|² Id` ([41, Theorem 1]) without proof. Here those outputs are hypotheses of
`integral_trace_hessian_quadratic_le`; only `range ∇φ ⊆ K` and some uniform bound `∇²φ ≤ C Id` are
used, `V` is smooth on an open `U ⊇ closure K` and convex on the bounded open set `K`, and every
dimension is included. The conclusion holds for every real symmetric `B`:
`E_ν tr(B ∇²φ B ∇²φ) ≤ 2 tr(B²)` with `ν = e^{-φ} dy`, together with integrability.

The proof follows the paper. For positive semidefinite `B`, the pointwise identity (2.10) of
`Analysis/BakryEmery/Hessian/Trace.lean`, transported from the standard orthonormal basis to the
coordinate basis, and the tensor comparison (2.12) give `0 ≤ 4D ≤ Lf + 2f` for
`f = tr(B ∇²φ B ∇²φ)` and the weighted third-derivative energy `D`; Lemmas A.4 and A.5 give
`E_ν Lf = 0`, hence (2.14). Lemma 2.3 and the Brascamp–Lieb step are supplied by
`KLS.LogConcave.integral_trace_quadratic_le_two_mul_trace_sq`. The Jordan decomposition extends the
bound to every symmetric `B`. Lemma 2.2 for the source class and Klartag's bound are not proved
here.
-/

@[expose] public section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped ContDiff

namespace FunctionalInequalities.Probability.MomentMeasure

open Matrix

private noncomputable def stdP (n : ℕ) :
    Matrix (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) (Fin n) ℝ :=
  fun a k => stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) a k

private theorem std_eq_sum (n : ℕ) (a : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
    stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) a =
      ∑ k, stdP n a k • EuclideanSpace.basisFun (Fin n) ℝ k :=
  ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr _).symm

private theorem stdP_mul_transpose (n : ℕ) : stdP n * (stdP n)ᵀ = 1 := by
  ext a c
  have h :=
    orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))).orthonormal a c
  rw [Matrix.one_apply, ← h]
  simp [stdP, Matrix.mul_apply, PiLp.inner_apply, mul_comm]

private theorem stdP_transpose_mul (n : ℕ) : (stdP n)ᵀ * stdP n = 1 := by
  ext k l
  have h := (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))).sum_inner_mul_inner
    (EuclideanSpace.basisFun (Fin n) ℝ k) (EuclideanSpace.basisFun (Fin n) ℝ l)
  simp only [EuclideanSpace.basisFun_inner] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, stdP]
  have hc (x : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
      inner ℝ (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) x)
        (EuclideanSpace.basisFun (Fin n) ℝ l) =
        (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) x) l := by
    rw [real_inner_comm, EuclideanSpace.basisFun_inner]
  simp only [hc] at h
  rw [h]
  simp [EuclideanSpace.basisFun_apply]

section ChangeOfBasis

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Ix" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
local notation "P" => stdP n

private theorem conj_apply (X : Matrix (Fin n) (Fin n) ℝ) (c d : Ix) :
    (P * X * Pᵀ) c d = ∑ k, ∑ l, P c k * X k l * P d l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem conj_mul (X Y : Matrix (Fin n) (Fin n) ℝ) :
    (P * X * Pᵀ) * (P * Y * Pᵀ) = P * (X * Y) * Pᵀ := by
  calc (P * X * Pᵀ) * (P * Y * Pᵀ) = P * X * (Pᵀ * P) * Y * Pᵀ := by
        simp only [Matrix.mul_assoc]
    _ = P * (X * Y) * Pᵀ := by
        rw [stdP_transpose_mul, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

private theorem trace_conj (X : Matrix (Fin n) (Fin n) ℝ) : (P * X * Pᵀ).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, stdP_transpose_mul, Matrix.one_mul]

private theorem transpose_conj (X : Matrix (Fin n) (Fin n) ℝ) :
    (P * X * Pᵀ)ᵀ = P * Xᵀ * Pᵀ := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

private theorem sum_mul_eq_trace {ι : Type*} [Fintype ι] (A C : Matrix ι ι ℝ) :
    ∑ a, ∑ c, A a c * C a c = (Aᵀ * C).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

private theorem sum_conj_mul_conj (X Y : Matrix (Fin n) (Fin n) ℝ) :
    ∑ a, ∑ c, (P * X * Pᵀ) a c * (P * Y * Pᵀ) a c = ∑ k, ∑ l, X k l * Y k l := by
  rw [sum_mul_eq_trace, sum_mul_eq_trace, transpose_conj, conj_mul, trace_conj]

private theorem bilin_expand {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Bf : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : ι → ℝ) (c : κ → ℝ) (v : ι → E) (w : κ → E) :
    Bf (∑ k, a k • v k) (∑ l, c l • w l) = ∑ k, ∑ l, a k * c l * Bf (v k) (w l) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Hessian matrices in the standard orthonormal basis are conjugates of the coordinate ones. -/
private theorem hessianMatrixIn_std_eq (g : E → ℝ) (y : E) :
    hessianMatrixIn g (stdOrthonormalBasis ℝ E) y =
      P * hessianMatrixIn g (EuclideanSpace.basisFun (Fin n) ℝ) y * Pᵀ := by
  ext c d
  rw [conj_apply]
  change bilinearIteratedFDerivTwo ℝ g y (stdOrthonormalBasis ℝ E c)
    (stdOrthonormalBasis ℝ E d) = _
  rw [std_eq_sum n c, std_eq_sum n d]
  refine (bilin_expand (bilinearIteratedFDerivTwo ℝ g y) (fun k => P c k) (fun l => P d l)
    _ _).trans ?_
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    simp only [hessianMatrixIn]; ring

/-- Classical directional derivatives of the coordinate Hessian entries. -/
private noncomputable def hessDeriv (φ : E → ℝ) (x : E) (r : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fun y => hessianMatrix φ y i j) x (EuclideanSpace.basisFun (Fin n) ℝ r)

private theorem stdHessianMatrixDeriv_eq {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E) (a : Ix) :
    stdHessianMatrixDeriv φ x a = P * (∑ r, P a r • hessDeriv φ x r) * Pᵀ := by
  ext c d
  have hfun : (fun y => hessianMatrixIn φ (stdOrthonormalBasis ℝ E) y c d) =
      fun y => ∑ k, ∑ l, (P c k * P d l) * hessianMatrix φ y k l := by
    funext y
    rw [hessianMatrixIn_std_eq, conj_apply]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      change _ = _ * bilinearIteratedFDerivTwo ℝ φ y _ _
      simp only [hessianMatrixIn]; ring
  have hd (k l : Fin n) : DifferentiableAt ℝ (fun y => hessianMatrix φ y k l) x :=
    (contDiff_bilinearIteratedFDerivTwo_apply hφ _ _).differentiable (by simp) x
  have hder : fderiv ℝ (fun y => ∑ k, ∑ l, (P c k * P d l) * hessianMatrix φ y k l) x =
      ∑ k, ∑ l, (P c k * P d l) • fderiv ℝ (fun y => hessianMatrix φ y k l) x := by
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro k _
    apply HasFDerivAt.fun_sum
    intro l _
    exact (hd k l).hasFDerivAt.const_mul _
  change fderiv ℝ (fun y => hessianMatrixIn φ (stdOrthonormalBasis ℝ E) y c d) x
    (stdOrthonormalBasis ℝ E a) = _
  rw [hfun, hder, std_eq_sum n a, conj_apply]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    Matrix.sum_apply, Matrix.smul_apply, hessDeriv, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => by ring

private theorem inverseHessianEntry_std_eq {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPDx : (hessianMatrix φ x).PosDef) :
    Matrix.of (fun i j => inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j) =
      P * (hessianMatrix φ x)⁻¹ * Pᵀ := by
  rw [← inv_hessianMatrixIn (stdOrthonormalBasis ℝ E) hφ x
    (Analysis.bilinearIteratedFDerivTwo_pos_of_hessianMatrix_posDef hPDx), hessianMatrixIn_std_eq]
  change (P * hessianMatrix φ x * Pᵀ)⁻¹ = P * (hessianMatrix φ x)⁻¹ * Pᵀ
  apply Matrix.inv_eq_left_inv
  rw [conj_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hPDx.det_pos.ne'),
    Matrix.mul_one, stdP_mul_transpose]

private theorem stdThirdGram_eq_trace {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E) (i j : Ix) :
    stdThirdGram φ x i j =
      (Matrix.of (fun a b => inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a b) *
        stdHessianMatrixDeriv φ x i *
        Matrix.of (fun a b => inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a b) *
        stdHessianMatrixDeriv φ x j).trace := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum]
  simp only [Fintype.sum_prod_type, Matrix.of_apply]
  unfold stdThirdGram
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => ?_
  rw [inverseHessianEntry_symm _ h2 x p a,
    (stdHessianMatrixDeriv_isSymm hφ x j).apply p q]
  ring

private theorem trace_sum_smul (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (X Y : Matrix (Fin n) (Fin n) ℝ) (a b : Ix) :
    (X * (∑ r, P a r • T r) * Y * (∑ s, P b s • T s)).trace =
      ∑ r, ∑ s, P a r * P b s * (X * T r * Y * T s).trace := by
  simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring

private theorem stdHessianMatrix_eq (φ : E → ℝ) (y : E) :
    stdHessianMatrix φ y = P * hessianMatrix φ y * Pᵀ :=
  hessianMatrixIn_std_eq φ y

private theorem stdThirdGram_eq_conj {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPDx : (hessianMatrix φ x).PosDef) :
    stdThirdGram φ x = P * Matrix.of (fun i j => ((hessianMatrix φ x)⁻¹ * hessDeriv φ x i *
      (hessianMatrix φ x)⁻¹ * hessDeriv φ x j).trace) * Pᵀ := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  ext i j
  rw [stdThirdGram_eq_trace hφ, inverseHessianEntry_std_eq h2 x hPDx,
    stdHessianMatrixDeriv_eq hφ, stdHessianMatrixDeriv_eq hφ, conj_mul, conj_mul, conj_mul,
    trace_conj, trace_sum_smul, conj_apply]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    rw [Matrix.of_apply]; ring

private theorem weightedDerivativeTrace_std_eq {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPDx : (hessianMatrix φ x).PosDef) (B : Matrix (Fin n) (Fin n) ℝ) :
    ∑ a, ∑ b, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a b *
        ((P * B * Pᵀ) * stdHessianMatrixDeriv φ x a * (P * B * Pᵀ) *
          stdHessianMatrixDeriv φ x b).trace =
      ∑ k, ∑ l, (hessianMatrix φ x)⁻¹ k l *
        (B * hessDeriv φ x k * B * hessDeriv φ x l).trace := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hA (a b : Ix) : inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a b =
      (P * (hessianMatrix φ x)⁻¹ * Pᵀ) a b := by
    rw [← inverseHessianEntry_std_eq h2 x hPDx, Matrix.of_apply]
  have hQ (a b : Ix) : ((P * B * Pᵀ) * stdHessianMatrixDeriv φ x a * (P * B * Pᵀ) *
      stdHessianMatrixDeriv φ x b).trace =
      (P * Matrix.of (fun k l => (B * hessDeriv φ x k * B * hessDeriv φ x l).trace) * Pᵀ) a b := by
    rw [stdHessianMatrixDeriv_eq hφ, stdHessianMatrixDeriv_eq hφ, conj_mul, conj_mul, conj_mul,
      trace_conj, trace_sum_smul, conj_apply]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      rw [Matrix.of_apply]; ring
  calc _ = ∑ a, ∑ b, (P * (hessianMatrix φ x)⁻¹ * Pᵀ) a b *
        (P * Matrix.of (fun k l => (B * hessDeriv φ x k * B * hessDeriv φ x l).trace) * Pᵀ) a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hA, hQ]
    _ = _ := by
        rw [sum_conj_mul_conj]
        simp only [Matrix.of_apply]

/-- Letwin (2.10) in the coordinates of `EuclideanSpace.basisFun`. -/
private theorem hessianInverseOperator_trace_basisFun {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K U : Set E} (hU : IsOpen U) (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hrange : Set.range (gradient φ) ⊆ K) (hPD : ∀ x, (hessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x))
    (B : Matrix (Fin n) (Fin n) ℝ) (x : E) :
    hessianInverseOperator φ V (fun y => (B * hessianMatrix φ y * B * hessianMatrix φ y).trace) x =
      2 * (B * hessianMatrix φ x * B * (-hessianMatrix φ x +
        hessianMatrix φ x * hessianMatrixIn V (EuclideanSpace.basisFun (Fin n) ℝ) (gradient φ x) *
          hessianMatrix φ x +
        Matrix.of (fun i j => ((hessianMatrix φ x)⁻¹ * hessDeriv φ x i *
          (hessianMatrix φ x)⁻¹ * hessDeriv φ x j).trace))).trace +
      2 * ∑ k, ∑ l, (hessianMatrix φ x)⁻¹ k l *
        (B * hessDeriv φ x k * B * hessDeriv φ x l).trace := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hPD' : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v :=
    fun x v hv => Analysis.bilinearIteratedFDerivTwo_pos_of_hessianMatrix_posDef (hPD x) v hv
  have hMA' : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y) :=
    fun y => by rw [Analysis.logDetHessian_std_eq_log_det_hessianMatrix h2]; exact hMA y
  have hfun : (fun y => (B * hessianMatrix φ y * B * hessianMatrix φ y).trace) =
      fun y => ((P * B * Pᵀ) * stdHessianMatrix φ y * (P * B * Pᵀ) *
        stdHessianMatrix φ y).trace := by
    funext y
    rw [stdHessianMatrix_eq, conj_mul, conj_mul, conj_mul, trace_conj]
  rw [hfun, traceGenerator_210_on_range hφ hU hKU hV hrange hMA' hPD' (P * B * Pᵀ) x,
    weightedDerivativeTrace_std_eq hφ x (hPD x), stdThirdGram_eq_conj hφ x (hPD x),
    stdHessianMatrix_eq, hessianMatrixIn_std_eq V]
  simp only [conj_mul, trace_conj, Matrix.mul_add, Matrix.mul_neg, Matrix.trace_add,
    Matrix.trace_neg]
  ring

end ChangeOfBasis

section Bounds

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem quad_single_add (H : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (s : ℝ) :
    star (Pi.single i 1 + s • Pi.single j 1 : Fin n → ℝ) ⬝ᵥ
        (H *ᵥ (Pi.single i 1 + s • Pi.single j 1)) =
      H i i + s * H i j + s * H j i + s * s * H j j := by
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, single_dotProduct,
    Matrix.col_apply, smul_eq_mul, one_mul]
  ring

private theorem abs_entry_le_of_posSemidef {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosSemidef)
    {C : ℝ} (hC : (C • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef) (i j : Fin n) :
    |H i j| ≤ C := by
  have hsym : H j i = H i j := by simpa only [star_trivial] using hH.isHermitian.apply i j
  have hdi : 0 ≤ (C • (1 : Matrix (Fin n) (Fin n) ℝ) - H) i i := hC.diag_nonneg
  have hdj : 0 ≤ (C • (1 : Matrix (Fin n) (Fin n) ℝ) - H) j j := hC.diag_nonneg
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at hdi hdj
  have hp := hH.dotProduct_mulVec_nonneg (Pi.single i 1 + (1 : ℝ) • Pi.single j 1)
  have hm := hH.dotProduct_mulVec_nonneg (Pi.single i 1 + (-1 : ℝ) • Pi.single j 1)
  rw [quad_single_add] at hp hm
  rw [hsym] at hp hm
  rw [abs_le]
  constructor <;> nlinarith

private theorem norm_clm_le_sum (A : E →L[ℝ] E) :
    ‖A‖ ≤ ∑ j, ∑ r, |FunctionalInequalities.Analysis.operatorMatrix
      (EuclideanSpace.basisFun (Fin n) ℝ) A j r| := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun r _ => abs_nonneg _) fun v => ?_
  set M := FunctionalInequalities.Analysis.operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ) A
  have hrep : A v = ∑ j, (A v) j • EuclideanSpace.basisFun (Fin n) ℝ j :=
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (A v)).symm
  calc ‖A v‖ = ‖∑ j, (A v) j • EuclideanSpace.basisFun (Fin n) ℝ j‖ := by rw [← hrep]
    _ ≤ ∑ j, ‖(A v) j • EuclideanSpace.basisFun (Fin n) ℝ j‖ := norm_sum_le _ _
    _ = ∑ j, |(A v) j| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 j, mul_one,
          Real.norm_eq_abs]
    _ ≤ ∑ j, ∑ r, |M j r| * ‖v‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [FunctionalInequalities.Analysis.euclidean_clm_apply_eq_sum_operatorMatrix A v j]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [← Real.norm_eq_abs]
        exact PiLp.norm_apply_le v r
    _ = (∑ j, ∑ r, |M j r|) * ‖v‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm

private theorem lipschitzWith_gradient_of_entry_bound {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {C : ℝ} (hent : ∀ x i j, |hessianMatrix φ x i j| ≤ C) :
    ∃ G : NNReal, LipschitzWith G (gradient φ) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  refine ⟨(∑ _j : Fin n, ∑ _r : Fin n, max C 0).toNNReal,
    lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) fun x => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  refine (norm_clm_le_sum _).trans (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun r _ => ?_)
  rw [FunctionalInequalities.Analysis.operatorMatrix_apply_eq_operatorEntry]
  change |FunctionalInequalities.Analysis.operatorEntry (EuclideanSpace.basisFun (Fin n) ℝ)
    (hessianOperator φ x) j r| ≤ _
  rw [← hessianMatrix_eq_operatorEntry_hessianOperator h2]
  exact (hent x j r).trans (le_max_left _ _)

private theorem lipschitzWith_of_gradient_mem {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set E} (hKb : Bornology.IsBounded K) (hrange : Set.range (gradient φ) ⊆ K) :
    ∃ L : NNReal, LipschitzWith L φ := by
  obtain ⟨R, hR⟩ := hKb.exists_norm_le
  refine ⟨(max R 0).toNNReal,
    lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable (by simp)) fun x => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
  have hfd : fderiv ℝ φ x = InnerProductSpace.toDual ℝ E (gradient φ x) := by
    simp [gradient]
  rw [hfd, LinearIsometryEquiv.norm_map]
  exact (hR _ (hrange ⟨x, rfl⟩)).trans (le_max_left _ _)

end Bounds

section PositiveSemidefinite

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem memLp_restrict_of_continuous {f : E → ℝ} (hf : Continuous f) (p : ENNReal)
    {S : Set E} (hS : IsCompact S) : MemLp f p ((volume : Measure E).restrict S) := by
  have : IsFiniteMeasure ((volume : Measure E).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    ((ae_restrict_iff' hS.measurableSet).mpr (ae_of_all _ hC))

private theorem continuous_trace_quartic {X Y : E → Matrix (Fin n) (Fin n) ℝ}
    (hX : ∀ i j, Continuous fun x => X x i j) (hY : ∀ i j, Continuous fun x => Y x i j)
    (B : Matrix (Fin n) (Fin n) ℝ) : Continuous fun x => (B * X x * B * Y x).trace := by
  have hXc : Continuous X := continuous_matrix hX
  have hYc : Continuous Y := continuous_matrix hY
  exact
    (((continuous_const.matrix_mul hXc).matrix_mul continuous_const).matrix_mul
        hYc).matrix_trace

/-- Letwin arXiv:2607.24164v1 Theorem 2.5 for positive semidefinite `B`. -/
private theorem integral_trace_hessian_quadratic_le_of_posSemidef {K U : Set E} {V φ : E → ℝ}
    (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hU : IsOpen U) (hKU : closure K ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V) (μ : ProbabilityMeasure E)
    (hiso : KLS.Isotropic μ) (hφ : ContDiff ℝ ∞ φ)
    (hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1)
    (hmap : ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E))
    (hrange : Set.range (gradient φ) ⊆ K) (hPD : ∀ x, (hessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x))
    (hbound : ∃ C : ℝ, ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef) :
    Integrable (fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace)
        ((volume : Measure E).tilted (-φ)) ∧
      (∫ x,
          (B * hessianMatrix φ x * B *
              hessianMatrix φ x).trace ∂((volume : Measure E).tilted (-φ))) ≤
        2 * (B * B).trace := by
  classical
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hPD' : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v := fun x v hv =>
    Analysis.bilinearIteratedFDerivTwo_pos_of_hessianMatrix_posDef (hPD x) v hv
  have hMA' : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y) :=
    fun y => by rw [Analysis.logDetHessian_std_eq_log_det_hessianMatrix h2]; exact hMA y
  have hconv : ConvexOn ℝ Set.univ φ := by
    refine
      FunctionalInequalities.Analysis.BakryEmery.convexOn_of_hessian_ge h2 le_rfl fun x v => ?_
    rw [zero_mul]
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hPD' x v hv).le
  obtain ⟨C, hC⟩ := hbound
  have hent : ∀ x i j, |hessianMatrix φ x i j| ≤ C := fun x =>
    abs_entry_le_of_posSemidef (hPD x).posSemidef (hC x)
  obtain ⟨G, hG⟩ := lipschitzWith_gradient_of_entry_bound hφ hent
  obtain ⟨L, hL⟩ := lipschitzWith_of_gradient_mem hφ hKb hrange
  have hprob : IsProbabilityMeasure ((volume : Measure E).tilted (-φ)) :=
    isProbabilityMeasure_tilted_neg_of_integral_eq_one _ φ hnorm
  let nu : ProbabilityMeasure E := ⟨(volume : Measure E).tilted (-φ), hprob⟩
  have hnuU : (nu : Measure E) = (volume : Measure E).tilted (-φ) := rfl
  have hHs : ∀ i j, ContDiff ℝ ∞ (fun x => hessianMatrix φ x i j) := fun i j =>
    contDiff_bilinearIteratedFDerivTwo_apply hφ _ _
  have hHc : ∀ i j, Continuous (fun x => hessianMatrix φ x i j) := fun i j =>
    (hHs i j).continuous
  -- the classical third-derivative tensor

  let T : E → Fin n → Matrix (Fin n) (Fin n) ℝ := fun x k => hessDeriv φ x k
  have hTc : ∀ k i j, Continuous (fun x => T x k i j) := fun k i j =>
    ((hHs i j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hT :
    ∀ k i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => hessianMatrix φ x i j)
          (fun x => T x k i j) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ K : Set E,
          IsCompact K → MemLp (fun x => T x k i j) 2 ((volume : Measure E).restrict K) :=
    fun k i j =>
    ⟨FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff ((hHs i j).of_le (by simp))
        _,
      fun _ hK => memLp_restrict_of_continuous (hTc k i j) 2 hK⟩
  -- the inverse Hessian

  have hRe :
    ∀ x i j,
      (hessianMatrix φ x)⁻¹ i j =
        inverseHessianEntry φ (EuclideanSpace.basisFun (Fin n) ℝ) x i j := by
    intro x i j
    change (hessianMatrixIn φ (EuclideanSpace.basisFun (Fin n) ℝ) x)⁻¹ i j = _
    rw [inv_hessianMatrixIn _ h2 x (hPD' x), Matrix.of_apply]
  have hRc : ∀ i j, Continuous (fun x => (hessianMatrix φ x)⁻¹ i j) := by
    intro i j
    simp_rw [hRe]
    exact
      continuous_iff_continuousAt.2 fun x =>
        (contDiffAt_inverseHessianEntry _ hφ x (hPD' x) i j).continuousAt
  have hR :
    ∀ i j : Fin n,
      ∀ K : Set E,
        IsCompact K →
          MemLp (fun x => (hessianMatrix φ x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure E).restrict K) :=
    fun i j _ hK =>
    memLp_restrict_of_continuous (hRc i j) ⊤
      hK
  -- Lemma 2.3: mean Hessian

  have hiso' : KLS.Isotropic (nu.map (gradient φ)) := by
    have hmapP : nu.map (gradient φ) = μ :=
      ProbabilityMeasure.toMeasure_injective
        (by
          rw [ProbabilityMeasure.toMeasure_map]
          exact hmap)
    rw [hmapP]
    exact hiso
  have hHI : ∀ i j, Integrable (fun x => hessianMatrix φ x i j) (nu : Measure E) := fun i j =>
    Integrable.of_bound (hHc i j).aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hent x i j)
  have hmean :
    ∀ i j : Fin n,
      Integrable (fun x => hessianMatrix φ x i j) (nu : Measure E) ∧
        (∫ x, hessianMatrix φ x i j ∂(nu : Measure E)) = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j
    refine ⟨hHI i j, ?_⟩
    have h :=
      KLS.integral_hessian_eq_inner_of_isotropic_map φ hφ hconv hnorm nu hnuU hiso'
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
    change (∫ x, bilinearIteratedFDerivTwo ℝ φ x _ _ ∂(nu : Measure E)) = _
    rw [h, EuclideanSpace.basisFun_inner, Matrix.one_apply]
    simp [EuclideanSpace.basisFun_apply]
  -- the trace function and its generator

  let f : E → ℝ := fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace
  have hfs : ContDiff ℝ ∞ f := by
    have hfe :
      f = fun x =>
        ∑ q : Fin n × Fin n × Fin n × Fin n,
          (B q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
            (hessianMatrix φ x q.2.1 q.2.2.1 * hessianMatrix φ x q.2.2.2 q.1) := by
      funext x
      exact FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum _ _ _ _
    rw [hfe]
    exact ContDiff.sum fun q _ => contDiff_const.mul ((hHs _ _).mul (hHs _ _))
  set Df : ℝ :=
    ∑ q : Fin n × Fin n × Fin n × Fin n, |B q.1 q.2.1 * B q.2.2.1 q.2.2.2| * (C * C) with hDf
  have hfb : ∀ x, |f x| ≤ Df := by
    intro x
    change |(B * hessianMatrix φ x * B * hessianMatrix φ x).trace| ≤ Df
    rw [FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_mul]
    exact
      mul_le_mul (hent x _ _) (hent x _ _) (abs_nonneg _)
        ((abs_nonneg _).trans (hent x q.2.1 q.2.2.1))
  have hfc : Continuous f := hfs.continuous
  let D : E → ℝ := fun x =>
    ∑ k : Fin n, ∑ l : Fin n, (hessianMatrix φ x)⁻¹ k l * (B * T x k * B * T x l).trace
  have hDc : Continuous D := by
    refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
    exact
      (hRc k l).mul (continuous_trace_quartic (fun i j => hTc k i j) (fun i j => hTc l i j) B)
  let Lf : E → ℝ := hessianInverseOperator φ V f
  have hptw : ∀ x, 0 ≤ D x ∧ 4 * D x ≤ Lf x + 2 * f x := by
    intro x
    have hxK : gradient φ x ∈ K := hrange ⟨x, rfl⟩
    have hV2 : ContDiffOn ℝ 2 V K :=
      (hV.mono (subset_closure.trans hKU)).of_le (WithTop.coe_le_coe.mpr le_top)
    have hW :
      (hessianMatrixIn V (EuclideanSpace.basisFun (Fin n) ℝ) (gradient φ x)).PosSemidef :=
      hessianMatrixIn_posSemidef _ (hV2.contDiffAt (hKo.mem_nhds hxK))
        (bilinearIteratedFDerivTwo_self_nonneg_of_convexOn_open hKo hV2 hVc hxK)
    let Tt : Fin n → Fin n → Fin n → ℝ := fun i a b => hessDeriv φ x i a b
    have hT1 : ∀ a b c, Tt a b c = Tt b a c := fun a b c =>
      fderiv_bilinearIteratedFDerivTwo_comm hφ x _ _ _
    have hT2 : ∀ a b c, Tt a b c = Tt a c b := by
      intro a b c
      have he : (fun y => hessianMatrix φ y b c) = fun y => hessianMatrix φ y c b :=
        funext fun y => bilinearIteratedFDerivTwo_symm h2 y _ _
      change
        fderiv ℝ (fun y => hessianMatrix φ y b c) x _ =
          fderiv ℝ (fun y => hessianMatrix φ y c b) x _
      rw [he]
    have h4 :=
      FunctionalInequalities.Analysis.four_tensor_trace_le_density_add_twice_energy B
        (hessianMatrix φ x) _ hB (hPD x) hW Tt hT1 hT2
    have hgen := hessianInverseOperator_trace_basisFun hφ hU hKU hV hrange hPD hMA B x
    change hessianInverseOperator φ V f x = _ at hgen
    change 0 ≤ D x ∧ 4 * D x ≤ hessianInverseOperator φ V f x + 2 * f x
    rw [hgen]
    exact
      h4
  -- Lemmas A.4 and A.5

  obtain ⟨χ, Cχ, _hCχ, hχ, hχS, hχB, _hχM, hχL, hχI, _hχD, hχDL⟩ :=
    exists_cutoffs_hessianInverseOperator (volume : Measure E) hφ hconv hKb hrange hU hKU hV
      hMA' hPD' hnorm
  have hLower : ∀ x, 0 ≤ hessianInverseOperator φ V f x + 2 * f x := fun x => by
    have := hptw x
    change 0 ≤ D x ∧ 4 * D x ≤ hessianInverseOperator φ V f x + 2 * f x at this
    linarith [this.1, this.2]
  obtain ⟨hLfI, hLf0⟩ :=
    integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs (volume : Measure E) hφ
      hfs hU hV (hrange.trans (subset_closure.trans hKU)) hMA' hPD' hnorm Df hfb 2 two_pos
      hLower χ hχ hχS hχB hχL hχI hχDL
  have hfI : Integrable f ((volume : Measure E).tilted (-φ)) :=
    Integrable.of_bound hfc.aestronglyMeasurable Df
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hfb x)
  have hSI : Integrable (fun x => (Lf x + 2 * f x) / 4) ((volume : Measure E).tilted (-φ)) :=
    (hLfI.add (hfI.const_mul 2)).div_const 4
  have hDI : Integrable D ((volume : Measure E).tilted (-φ)) := by
    refine hSI.mono' hDc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hptw x).1]
    linarith [(hptw x).2]
  have hhalf :
    (∫ x, D x ∂((volume : Measure E).tilted (-φ))) ≤
      (1 / 2 : ℝ) * ∫ x, f x ∂((volume : Measure E).tilted (-φ)) := by
    calc
      (∫ x, D x ∂((volume : Measure E).tilted (-φ))) ≤
          ∫ x, (Lf x + 2 * f x) / 4 ∂((volume : Measure E).tilted (-φ)) :=
        integral_mono hDI hSI fun x => by linarith [(hptw x).2]
      _ = (1 / 2 : ℝ) * ∫ x, f x ∂((volume : Measure E).tilted (-φ)) := by
        rw [integral_div, integral_add hLfI (hfI.const_mul 2), integral_const_mul]
        change
          ((∫ x, hessianInverseOperator φ V f x ∂((volume : Measure E).tilted (-φ))) + 2 * _) /
              4 =
            _
        rw [hLf0]
        ring
  exact
    FunctionalInequalities.KLS.LogConcave.integral_trace_quadratic_le_two_mul_trace_sq hnuU
      hconv (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hG hL hnorm (ae_of_all _ hPD) T hT hR
      hmean B hB hDI hhalf

end PositiveSemidefinite

/-- Letwin arXiv:2607.24164v1 Theorem 2.5, in the paper's conditional form: the moment-map
properties that the paper imports from Klartag [41] (Lemma 2.2 and [41, Theorem 1]) are hypotheses.
-/
theorem integral_trace_hessian_quadratic_le {n : ℕ} {K U : Set (EuclideanSpace ℝ (Fin n))}
    {V φ : EuclideanSpace ℝ (Fin n) → ℝ} (hKb : Bornology.IsBounded K) (hKo : IsOpen K)
    (hU : IsOpen U) (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hiso : KLS.Isotropic μ)
    (hφ : ContDiff ℝ ∞ φ)
    (hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hmap :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)).map (gradient φ) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hrange : Set.range (gradient φ) ⊆ K) (hPD : ∀ x, (hessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x))
    (hbound : ∃ C : ℝ, ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    Integrable (fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) ∧
      (∫ x,
          (B * hessianMatrix φ x * B *
              hessianMatrix φ
                x).trace ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ))) ≤
        2 * (B * B).trace := by
  exact
    FunctionalInequalities.Analysis.symmetric_trace_integral_extension
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) (hessianMatrix φ)
      (fun i j => (contDiff_bilinearIteratedFDerivTwo_apply hφ _ _).continuous.measurable)
      (fun x => (hPD x).posSemidef)
      (fun A hA =>
        integral_trace_hessian_quadratic_le_of_posSemidef hKb hKo hU hKU hV hVc μ hiso hφ hnorm
          hmap hrange hPD hMA hbound A hA)
      hB

end FunctionalInequalities.Probability.MomentMeasure

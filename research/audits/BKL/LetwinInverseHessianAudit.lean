import FunctionalInequalities.Analysis.BakryEmery.MongeAmpere
import FunctionalInequalities.Analysis.Operator.Coordinates
import FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
import FunctionalInequalities.Analysis.BakryEmery.Hessian.Diffusion
import FunctionalInequalities.Analysis.BakryEmery.Hessian.Operator
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Mul
import Mathlib.LinearAlgebra.Determinant

/-!
# Audit: inverse Hessian (2.5), Jacobi, and the Monge–Ampère derivatives (2.4), (2.6)

Source: Letwin, arXiv:2607.24164v1, pp. 5–7. Clients: the potential `exp` on `ℝ` (nonconstant
Hessian; the inverse-Hessian derivative at `0` is `−1`; it is an analytic example, not a normalized
moment potential and not a Monge–Ampère solution), a `V` smooth only on `(0, 3)` composed with the
gradient, rank zero, and the Codex reviewer's coordinate and operator consumers (credited). Client
bodies: Codex route bundles `MA-Inverse` (receipt d613c8f4…), `MA-Jacobi` (receipt e5938315…) and
`MA-Second-Derivative` (receipt 43cc91b3…), all independently accepted; the reviewer consumers
(basis independence of `log det`, a negative-determinant direction, a signed Gram value) are credited to
the Codex reviewers. Jacobi clients: a nonsymmetric `2×2` matrix with `d(log det) = −1/6`, the `exp`
potential satisfying a zero-order Monge–Ampère equation with a local `V` on `(0, ∞)` and first MA value `1`,
the empty matrix; second-derivative clients: the `exp` potential with a non-convex `V` (negative `V`-term),
the convex `V = ‖·‖²` (value `2`), a `2×2` weighted Gram `[[1,1],[1,4]]`, rank zero.
-/

noncomputable section
open scoped RealInnerProductSpace ContDiff Matrix.Norms.Elementwise
open Filter Topology
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery

namespace ActualMAInverse

theorem gradient_exp (x : ℝ) : gradient Real.exp x = Real.exp x := by
  have h : ⟪gradient Real.exp x, (1 : ℝ)⟫ = fderiv ℝ Real.exp x 1 := inner_gradient_left
  rw [(Real.hasDerivAt_exp x).hasFDerivAt.fderiv] at h
  simpa [Real.inner_apply] using h

theorem hessianOperator_exp (x : ℝ) : hessianOperator Real.exp x = Real.exp x • (1 : ℝ →L[ℝ] ℝ) := by
  have hg : gradient Real.exp = Real.exp := funext gradient_exp
  apply ContinuousLinearMap.ext
  intro v
  rw [hessianOperator, hg, (Real.hasDerivAt_exp x).hasFDerivAt.fderiv]
  simp [smul_eq_mul, mul_comm]

theorem hessian_exp (x u v : ℝ) :
    bilinearIteratedFDerivTwo ℝ Real.exp x u v = Real.exp x * u * v := by
  rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator Real.contDiff_exp, hessianOperator_exp]
  change v * (Real.exp x * u) = Real.exp x * u * v
  ring

theorem exp_hessian_positive (x : ℝ) (v : ℝ) (hv : v ≠ 0) :
    0 < bilinearIteratedFDerivTwo ℝ Real.exp x v v := by
  rw [hessian_exp]
  have h : 0 < Real.exp x * v ^ 2 := mul_pos (Real.exp_pos x) (sq_pos_of_ne_zero hv)
  simpa only [pow_two, mul_assoc] using h

theorem hessianOperator_exp_derivative (x : ℝ) :
    fderiv ℝ (hessianOperator Real.exp) x 1 = Real.exp x • (1 : ℝ →L[ℝ] ℝ) := by
  have heq : hessianOperator Real.exp = fun y : ℝ => Real.exp y • (1 : ℝ →L[ℝ] ℝ) :=
    funext hessianOperator_exp
  rw [heq]
  have hd := (Real.hasDerivAt_exp x).hasFDerivAt.smul_const (1 : ℝ →L[ℝ] ℝ)
  have h := congrArg (fun L : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) => L 1) hd.fderiv
  simpa using h

/-- The inverse-Hessian derivative of `exp` at `0` is `−1` (nonzero). -/
theorem exp_inverse_hessian_derivative_nonzero :
    (fderiv ℝ (fun y : ℝ => Ring.inverse (hessianOperator Real.exp y)) 0 1) 1 = -1 := by
  have h := fderiv_ringInverse_hessianOperator_apply Real.contDiff_exp (0 : ℝ)
    (exp_hessian_positive 0) (1 : ℝ)
  rw [hessianOperator_exp, hessianOperator_exp_derivative] at h
  simp only [Real.exp_zero, one_smul, Ring.inverse_one, one_mul] at h
  have h' := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h
  simpa using h'

def localV (z : ℝ) : ℝ := if z < 3 then z ^ 2 else z

theorem localV_smooth_on : ContDiffOn ℝ ∞ localV (Set.Ioo 0 3) := by
  apply (contDiff_id.pow 2).contDiffOn.congr
  intro z hz
  simp only [localV, if_pos hz.2, id_eq]

theorem actual_local_potential_chain :
    ContDiffAt ℝ ∞ (fun y : ℝ => localV (gradient Real.exp y)) 0 := by
  apply contDiffAt_comp_gradient_of_mem Real.contDiff_exp isOpen_Ioo localV_smooth_on
  rw [gradient_exp]
  norm_num

abbrev ZeroSpace := EuclideanSpace ℝ (Fin 0)

theorem actual_rank0_hessian_unit : IsUnit (hessianOperator (fun _ : ZeroSpace => (0 : ℝ)) 0) := by
  apply hessianOperator_isUnit_of_posDef contDiff_const
  intro v hv
  exact (hv (Subsingleton.elim _ _)).elim

theorem actual_rank0_inverse_hessian_derivative :
    HasFDerivAt (𝕜 := ℝ)
      (fun y : ZeroSpace => Ring.inverse (hessianOperator (fun _ => (0 : ℝ)) y)) 0 0 := by
  have hg : ContDiff ℝ ∞ (gradient (fun _ : ZeroSpace => (0 : ℝ))) :=
    FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ZeroSpace => (0 : ℝ))) (by simp)
  have hH : ContDiff ℝ ∞ (hessianOperator (fun _ : ZeroSpace => (0 : ℝ))) := hg.fderiv_right (m := ∞) (by simp)
  have h := hasFDerivAt_ringInverse_comp
    (hH.differentiable (by simp) 0).hasFDerivAt actual_rank0_hessian_unit
  exact h.congr_fderiv (Subsingleton.elim _ _)
end ActualMAInverse

namespace IndependentMAInverse
open ActualMAInverse

def lineBasis : OrthonormalBasis (Fin 1) ℝ ℝ :=
  (stdOrthonormalBasis ℝ ℝ).reindex (finCongr (by simp))

private theorem line_basis_sq : lineBasis 0 * lineBasis 0 = 1 := by
  have h := lineBasis.inner_eq_ite (0 : Fin 1) 0
  simpa only [Real.inner_apply, ite_true] using h

private theorem line_entry_exp (x : ℝ) :
    bilinearIteratedFDerivTwo ℝ Real.exp x (lineBasis 0) (lineBasis 0) = Real.exp x := by
  rw [hessian_exp]
  rw [mul_assoc, line_basis_sq, mul_one]

/-- Coordinate form of (2.5) for `exp` (Codex reviewer consumer). -/
theorem exp_coordinate_inverse_derivative :
    fderiv ℝ (fun y : ℝ => inverseHessianEntry Real.exp lineBasis y 0 0) 0 (lineBasis 0) =
      -lineBasis 0 := by
  have h := fderiv_inverseHessianEntry_apply lineBasis Real.contDiff_exp (0 : ℝ)
    (exp_hessian_positive 0) (0 : Fin 1) 0 0
  have hH : hessianOperator Real.exp (0 : ℝ) = 1 := by
    simpa only [Real.exp_zero, one_smul] using hessianOperator_exp 0
  have heq : (fun y : ℝ => bilinearIteratedFDerivTwo ℝ Real.exp y
      (lineBasis 0) (lineBasis 0)) = Real.exp := funext line_entry_exp
  simp only [Fin.sum_univ_one] at h
  rw [heq] at h
  have hi : inverseHessianEntry Real.exp lineBasis 0 0 0 = 1 := by
    simp only [inverseHessianEntry, operatorEntry, hH, Ring.inverse_one, one_apply_eq_self,
      Real.inner_apply, line_basis_sq]
  have hd : fderiv ℝ Real.exp 0 (lineBasis 0) = lineBasis 0 := by
    rw [(Real.hasDerivAt_exp 0).hasFDerivAt.fderiv]
    change lineBasis 0 * Real.exp 0 = lineBasis 0
    simp
  rw [hi, one_mul, mul_one, hd] at h
  exact h

/-- The inverse-Hessian operator with zero drift applied to `x²` at `0` is `2` (Codex reviewer consumer). -/
theorem actual_operator_square_at_zero :
    hessianInverseOperator Real.exp (fun _ : ℝ => 0) (fun x : ℝ => x * x) 0 = 2 := by
  let b := stdOrthonormalBasis ℝ ℝ
  have hH : hessianOperator Real.exp (0 : ℝ) = 1 := by
    simpa only [Real.exp_zero, one_smul] using hessianOperator_exp 0
  have hsum : (∑ i, b i * b i) = 1 := by
    simpa only [Real.inner_apply, one_mul, mul_one] using b.sum_inner_mul_inner (1 : ℝ) 1
  have h := hessianInverseOperator_mul (φ := Real.exp) Real.contDiff_exp (fun _ : ℝ => 0)
    (f := id) (g := id) contDiff_id contDiff_id (0 : ℝ)
  have hm : (∑ i, ∑ j, inverseHessianEntry Real.exp b 0 i j *
      fderiv ℝ (id : ℝ → ℝ) 0 (b i) * fderiv ℝ (id : ℝ → ℝ) 0 (b j)) = 1 := by
    simp only [inverseHessianEntry, operatorEntry, hH, Ring.inverse_one, one_apply_eq_self,
      fderiv_id, ContinuousLinearMap.id_apply]
    simp only [b.inner_eq_ite, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    exact hsum
  simp only [id_eq, zero_mul, zero_add] at h
  change hessianInverseOperator Real.exp (fun _ : ℝ => 0) (fun x : ℝ => x * x) 0 =
    2 * (∑ i, ∑ j, inverseHessianEntry Real.exp b 0 i j *
      fderiv ℝ (id : ℝ → ℝ) 0 (b i) * fderiv ℝ (id : ℝ → ℝ) 0 (b j)) at h
  rw [hm, mul_one] at h
  exact h
end IndependentMAInverse

namespace ActualMAJacobi
open ActualMAInverse

def M : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 0, 3]
def N : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
def A : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, -(1 / 6); 0, 1 / 3]

theorem true_inverse : M⁻¹ = A := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, M, Matrix.mul_apply, Fin.sum_univ_two]

/-- Nonsymmetric M/direction exercise transpose and sign: d(logdet)= -1/6. -/
theorem nonsymmetric_logdet_derivative :
    fderiv ℝ (fun Q : Matrix (Fin 2) (Fin 2) ℝ => Real.log Q.det) M N = -(1 / 6) := by
  rw [fderiv_logDet_apply M N (by norm_num [M, Matrix.det_fin_two]), true_inverse]
  norm_num [A, N, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

def b : OrthonormalBasis (Fin 1) ℝ ℝ := OrthonormalBasis.singleton (Fin 1) ℝ

@[simp] theorem b_apply (i : Fin 1) : b i = 1 := OrthonormalBasis.singleton_apply i

theorem hessian_exp_matrix (x : ℝ) : hessianMatrixIn Real.exp b x = !![Real.exp x] := by
  ext i j
  fin_cases i
  fin_cases j
  change bilinearIteratedFDerivTwo ℝ Real.exp x (b 0) (b 0) = Real.exp x
  rw [hessian_exp]
  simp

theorem exp_logdet_derivative : fderiv ℝ (logDetHessian Real.exp b) 0 1 = 1 := by
  have heq : logDetHessian Real.exp b = fun x : ℝ => x := by
    ext x
    rw [logDetHessian, hessian_exp_matrix, Matrix.det_fin_one]
    simp
  rw [heq]
  simp

def V (z : ℝ) : ℝ := z + Real.log z

theorem V_smooth_on : ContDiffOn ℝ ∞ V (Set.Ioi 0) := by
  apply contDiffOn_id.add
  apply Real.contDiffOn_log.mono
  intro z hz
  exact ne_of_gt hz

theorem actual_MA_logdet : ∀ y : ℝ, logDetHessian Real.exp b y = -Real.exp y + V (gradient Real.exp y) := by
  intro y
  rw [logDetHessian, hessian_exp_matrix, Matrix.det_fin_one, gradient_exp]
  simp [V]

/-- Consumes the actual derived first MA equation, with local V and all analytic/MA
inputs discharged. Convex V/bounded K/normalization are not asserted for this client. -/
theorem actual_first_MA :
    (∑ a, ∑ c, inverseHessianEntry Real.exp b 0 a c *
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b a) (b c)) 0 (b 0)) =
      -fderiv ℝ Real.exp 0 (b 0) + ∑ a, fderiv ℝ V (gradient Real.exp 0) (b a) *
        bilinearIteratedFDerivTwo ℝ Real.exp 0 (b a) (b 0) := by
  exact mongeAmpere_first_derivative b Real.contDiff_exp isOpen_Ioi V_smooth_on actual_MA_logdet
    (by rw [gradient_exp]; simpa only [Set.mem_Ioi, Real.exp_zero] using (zero_lt_one : (0 : ℝ) < 1)) (exp_hessian_positive 0) 0

theorem first_MA_nonzero_left :
    (∑ a, ∑ c, inverseHessianEntry Real.exp b 0 a c *
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b a) (b c)) 0 (b 0)) = 1 := by
  rw [← fderiv_logDetHessian_eq_sum b Real.contDiff_exp 0 (exp_hessian_positive 0)]
  simpa only [b_apply] using exp_logdet_derivative

theorem empty_matrix_logdet_derivative (M N : Matrix (Fin 0) (Fin 0) ℝ) :
    fderiv ℝ (fun Q : Matrix (Fin 0) (Fin 0) ℝ => Real.log Q.det) M N = 0 := by
  rw [fderiv_logDet_apply M N (by simp [Matrix.det_isEmpty])]
  simp [Matrix.trace]
end ActualMAJacobi

namespace IndependentMAJacobi

/-- Log determinant of the actual Hessian is independent of its orthonormal coordinates.
The two bases may even have different finite index types. -/
theorem logdet_basis_independent {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {m n : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ E) (c : OrthonormalBasis (Fin n) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) :
    logDetHessian φ b x = logDetHessian φ c x := by
  unfold logDetHessian
  rw [hessianMatrixIn_eq_toMatrix b hφ x, hessianMatrixIn_eq_toMatrix c hφ x]
  rw [LinearMap.det_toMatrix, LinearMap.det_toMatrix]

/-- The stronger generic real-log Jacobi theorem keeps its nonzero-determinant scope.
This negative determinant consumer is not a positive-Hessian or source-MA example. -/
theorem negative_determinant_direction :
    fderiv ℝ (fun M : Matrix (Fin 1) (Fin 1) ℝ => Real.log M.det)
      (!![-1]) (!![1]) = -1 := by
  have hi : (!![-1] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![-1] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.mul_apply, Fin.sum_univ_one]
  rw [fderiv_logDet_apply _ _ (by norm_num [Matrix.det_fin_one]), hi]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_one]
end IndependentMAJacobi

namespace ActualMASecond
open ActualMAInverse ActualMAJacobi

lemma exp_inverse_entry (a c : Fin 1) : inverseHessianEntry Real.exp b 0 a c = 1 := by
  simp [inverseHessianEntry, operatorEntry, hessianOperator_exp, b_apply]

lemma exp_hessian_entry (y : ℝ) (a c : Fin 1) :
    bilinearIteratedFDerivTwo ℝ Real.exp y (b a) (b c) = Real.exp y := by
  simp [b_apply, hessian_exp]

lemma exp_third_entry (a c i : Fin 1) :
    fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b a) (b c)) 0 (b i) = 1 := by
  have heq : (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b a) (b c)) = Real.exp :=
    funext fun y => exp_hessian_entry y a c
  rw [heq, (Real.hasDerivAt_exp 0).hasFDerivAt.fderiv]
  simp [b_apply]

lemma actual_V_first {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt V (1 + z⁻¹) z := (hasDerivAt_id z).add (Real.hasDerivAt_log hz)

lemma V_hessian_negative (a c : Fin 1) :
    bilinearIteratedFDerivTwo ℝ V 1 (b a) (b c) = -1 := by
  have hv : ContDiffAt ℝ 2 V 1 :=
    (V_smooth_on.contDiffAt (isOpen_Ioi.mem_nhds (by norm_num))).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply_at hv, b_apply, b_apply]
  have heq : (fun z => fderiv ℝ V z (1 : ℝ)) =ᶠ[𝓝 (1 : ℝ)] (fun z => 1 + z⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with z hz
    rw [(actual_V_first hz).hasFDerivAt.fderiv]
    simp
  rw [heq.fderiv_eq]
  have hd : HasDerivAt (fun z : ℝ => 1 + z⁻¹) (-1) 1 := by
    simpa using (hasDerivAt_inv (x := (1 : ℝ)) (by norm_num)).const_add 1
  rw [hd.hasFDerivAt.fderiv]
  simp

/-- Actual first-to-second MA consumer with zero-order MA and all derivative inputs derived. -/
theorem actual_exp_second_MA :
    (∑ a, ∑ c, inverseHessianEntry Real.exp b 0 a c *
      bilinearIteratedFDerivTwo ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b 0) (b 0)) 0 (b a) (b c)) -
      (∑ a, fderiv ℝ V (gradient Real.exp 0) (b a) *
        fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b 0) (b 0)) 0 (b a)) +
      bilinearIteratedFDerivTwo ℝ Real.exp 0 (b 0) (b 0) =
      (∑ a, ∑ c, bilinearIteratedFDerivTwo ℝ Real.exp 0 (b 0) (b a) *
        bilinearIteratedFDerivTwo ℝ V (gradient Real.exp 0) (b a) (b c) *
        bilinearIteratedFDerivTwo ℝ Real.exp 0 (b c) (b 0)) +
      ∑ a, ∑ c, ∑ p, ∑ q, inverseHessianEntry Real.exp b 0 a p * inverseHessianEntry Real.exp b 0 c q *
        fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b a) (b c)) 0 (b 0) *
        fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b p) (b q)) 0 (b 0) := by
  exact mongeAmpere_second_derivative_coordinate b Real.contDiff_exp isOpen_Ioi V_smooth_on actual_MA_logdet
    exp_hessian_positive (by rw [gradient_exp]; norm_num) 0 0

theorem actual_exp_V_term_negative :
    (∑ a, ∑ c, bilinearIteratedFDerivTwo ℝ Real.exp 0 (b 0) (b a) *
      bilinearIteratedFDerivTwo ℝ V (gradient Real.exp 0) (b a) (b c) *
      bilinearIteratedFDerivTwo ℝ Real.exp 0 (b c) (b 0)) = -1 := by
  rw [gradient_exp]
  simp only [Real.exp_zero, exp_hessian_entry, V_hessian_negative]
  norm_num

theorem actual_exp_third_Gram_nonzero :
    (∑ a, ∑ c, ∑ p, ∑ q, inverseHessianEntry Real.exp b 0 a p * inverseHessianEntry Real.exp b 0 c q *
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b a) (b c)) 0 (b 0) *
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b p) (b q)) 0 (b 0)) = 1 := by
  simp only [exp_inverse_entry, exp_third_entry]
  norm_num

theorem actual_exp_Gram_PSD :
    (Matrix.of fun i j => ∑ a, ∑ c, ∑ p, ∑ q, inverseHessianEntry Real.exp b 0 a p *
      inverseHessianEntry Real.exp b 0 c q *
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b a) (b c)) 0 (b i) *
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ Real.exp y (b p) (b q)) 0 (b j)).PosSemidef :=
  posSemidef_inverseHessian_third_gram b Real.contDiff_exp 0 (exp_hessian_positive 0)


theorem actual_convex_V_PSD :
    (Matrix.of fun i j => ∑ a, ∑ c, bilinearIteratedFDerivTwo ℝ Real.exp 0 (b i) (b a) *
      bilinearIteratedFDerivTwo ℝ (fun z : ℝ => ‖z‖ ^ 2) (gradient Real.exp 0) (b a) (b c) *
      bilinearIteratedFDerivTwo ℝ Real.exp 0 (b c) (b j)).PosSemidef := by
  have hc : ConvexOn ℝ (Set.Ioo (0 : ℝ) 2) (fun z : ℝ => ‖z‖ ^ 2) := by
    have h : ConvexOn ℝ Set.univ (fun z : ℝ => z ^ (2 : ℕ)) :=
      (show Even (2 : ℕ) by decide).convexOn_pow
    simpa only [Real.norm_eq_abs, sq_abs] using h.subset (Set.subset_univ _) (convex_Ioo 0 2)
  exact posSemidef_hessian_conj_hessian b
    (Real.contDiff_exp.of_le (WithTop.coe_le_coe.mpr le_top)) isOpen_Ioo
    (contDiff_norm_sq ℝ).contDiffOn hc (by rw [gradient_exp]; norm_num)

theorem actual_convex_V_term_nonzero :
    (∑ a, ∑ c, bilinearIteratedFDerivTwo ℝ Real.exp 0 (b 0) (b a) *
      bilinearIteratedFDerivTwo ℝ (fun z : ℝ => ‖z‖ ^ 2) (gradient Real.exp 0) (b a) (b c) *
      bilinearIteratedFDerivTwo ℝ Real.exp 0 (b c) (b 0)) = 2 := by
  simp only [gradient_exp, b_apply, hessian_exp, Real.exp_zero, mul_one, one_mul, Fin.sum_univ_one]
  rw [FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_norm_sq]
  norm_num

abbrev ZeroSpace := EuclideanSpace ℝ (Fin 0)

theorem actual_rank0_zero_MA : ∀ y : ZeroSpace,
    logDetHessian (fun _ : ZeroSpace => (0 : ℝ)) (EuclideanSpace.basisFun (Fin 0) ℝ) y =
      -(0 : ℝ) + (fun _ : ZeroSpace => (0 : ℝ)) (gradient (fun _ : ZeroSpace => (0 : ℝ)) y) := by
  intro y
  simp [logDetHessian, Matrix.det_isEmpty]

theorem actual_rank0_operator_zero :
    hessianInverseOperator (fun _ : ZeroSpace => (0 : ℝ)) (fun _ : ZeroSpace => (0 : ℝ))
      (fun _ : ZeroSpace => (0 : ℝ)) 0 + (0 : ℝ) = 0 := by
  have : IsEmpty (Fin (Module.finrank ℝ ZeroSpace)) := by
    rw [finrank_euclideanSpace_fin]
    infer_instance
  simp [hessianInverseOperator, FunctionalInequalities.Analysis.BakryEmery.nondivergenceOperator]

theorem actual_rank0_V_PSD :
    (Matrix.of fun i j => ∑ a, ∑ c, bilinearIteratedFDerivTwo ℝ (fun _ : ZeroSpace => (0 : ℝ)) 0
      (EuclideanSpace.basisFun (Fin 0) ℝ i) (EuclideanSpace.basisFun (Fin 0) ℝ a) *
      bilinearIteratedFDerivTwo ℝ (fun _ : ZeroSpace => (0 : ℝ))
        (gradient (fun _ : ZeroSpace => (0 : ℝ)) 0)
        (EuclideanSpace.basisFun (Fin 0) ℝ a) (EuclideanSpace.basisFun (Fin 0) ℝ c) *
      bilinearIteratedFDerivTwo ℝ (fun _ : ZeroSpace => (0 : ℝ)) 0
        (EuclideanSpace.basisFun (Fin 0) ℝ c) (EuclideanSpace.basisFun (Fin 0) ℝ j)).PosSemidef :=
  posSemidef_hessian_conj_hessian _ contDiff_const isOpen_univ contDiffOn_const
    (convexOn_const _ convex_univ) (Set.mem_univ _)

theorem actual_rank0_Gram_PSD :
    (Matrix.of fun i j => ∑ a, ∑ c, ∑ p, ∑ q,
      inverseHessianEntry (fun _ : ZeroSpace => (0 : ℝ)) (EuclideanSpace.basisFun (Fin 0) ℝ) 0 a p *
      inverseHessianEntry (fun _ : ZeroSpace => (0 : ℝ)) (EuclideanSpace.basisFun (Fin 0) ℝ) 0 c q *
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ (fun _ : ZeroSpace => (0 : ℝ)) y
        (EuclideanSpace.basisFun (Fin 0) ℝ a) (EuclideanSpace.basisFun (Fin 0) ℝ c)) 0
        (EuclideanSpace.basisFun (Fin 0) ℝ i) *
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ (fun _ : ZeroSpace => (0 : ℝ)) y
        (EuclideanSpace.basisFun (Fin 0) ℝ p) (EuclideanSpace.basisFun (Fin 0) ℝ q)) 0
        (EuclideanSpace.basisFun (Fin 0) ℝ j)).PosSemidef := by
  apply posSemidef_inverseHessian_third_gram _ contDiff_const
  intro v hv
  exact (hv (Subsingleton.elim _ _)).elim
end ActualMASecond

namespace ActualMASecondMatrix

def B : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]
def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 2]
def T (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ := if i = 0 then !![1, 0; 0, 0] else !![0, 0; 0, 1]

theorem actual_A_PSD : A.PosSemidef := by
  have h := (Matrix.PosSemidef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef).mul_mul_conjTranspose_same B
  have heq : B * (1 : Matrix (Fin 2) (Fin 2) ℝ) * B.conjTranspose = A := by
    rw [Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [B, A, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  exact heq ▸ h

theorem actual_Gram_matrix :
    Matrix.of (fun i j : Fin 2 => ∑ a, ∑ b, ∑ c, ∑ d, A a c * A b d * T i a b * T j c d) =
      !![1, 1; 1, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, T, Fin.sum_univ_two]

theorem actual_nondiagonal_Gram_PSD : (!![1, 1; 1, 4] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  rw [← actual_Gram_matrix]
  exact posSemidef_weightedGram A actual_A_PSD T
end ActualMASecondMatrix

namespace IndependentMASecond
open ActualMASecondMatrix
private def v : Fin 2 → ℝ := ![1, -1]
theorem actual_signed_gram_value :
    dotProduct (star v) ((Matrix.of fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
      A a c * A b d * T i a b * T j c d).mulVec v) = 3 := by
  rw [actual_Gram_matrix]
  norm_num [v, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
theorem actual_signed_gram_positive :
    (Matrix.of fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
      A a c * A b d * T i a b * T j c d).PosSemidef ∧
    0 < dotProduct (star v) ((Matrix.of fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
      A a c * A b d * T i a b * T j c d).mulVec v) := by
  exact ⟨posSemidef_weightedGram A actual_A_PSD T,
    by rw [actual_signed_gram_value]; norm_num⟩
end IndependentMASecond

#print axioms FunctionalInequalities.Analysis.fderiv_ringInverse_comp_apply
#print axioms FunctionalInequalities.Analysis.operatorEntry_ringInverse_fderiv_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.contDiffAt_comp_gradient_of_mem
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianOperator_isUnit_of_posDef
#print axioms FunctionalInequalities.Analysis.BakryEmery.inner_ringInverse_hessianOperator_pos
#print axioms FunctionalInequalities.Analysis.BakryEmery.sum_inverseHessianEntry_mul_hessian
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_ringInverse_hessianOperator_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_inverseHessianEntry_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianInverseOperator_mul
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_logDetHessian_of_mongeAmpere
#print axioms FunctionalInequalities.Probability.Stein.hessianMatrix_eq_operatorEntry_hessianOperator
#print axioms ActualMAInverse.exp_inverse_hessian_derivative_nonzero
#print axioms ActualMAInverse.actual_local_potential_chain
#print axioms ActualMAInverse.actual_rank0_inverse_hessian_derivative
#print axioms IndependentMAInverse.exp_coordinate_inverse_derivative
#print axioms IndependentMAInverse.actual_operator_square_at_zero
#print axioms FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace
#print axioms FunctionalInequalities.Analysis.fderiv_logDet_comp_apply
#print axioms FunctionalInequalities.Analysis.posSemidef_weightedGram
#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_bilinearIteratedFDerivTwo_comm
#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_self_nonneg_of_convexOn_open
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_logDetHessian_eq_trace
#print axioms FunctionalInequalities.Analysis.BakryEmery.mongeAmpere_first_derivative
#print axioms FunctionalInequalities.Analysis.BakryEmery.mongeAmpere_first_derivative_on_range
#print axioms FunctionalInequalities.Analysis.BakryEmery.inv_hessianMatrixIn_posSemidef
#print axioms FunctionalInequalities.Analysis.BakryEmery.posSemidef_hessian_conj_hessian_on_range
#print axioms FunctionalInequalities.Analysis.BakryEmery.posSemidef_inverseHessian_third_gram
#print axioms FunctionalInequalities.Analysis.BakryEmery.mongeAmpere_second_derivative
#print axioms FunctionalInequalities.Analysis.BakryEmery.mongeAmpere_second_derivative_on_range
#print axioms ActualMAJacobi.nonsymmetric_logdet_derivative
#print axioms ActualMAJacobi.actual_first_MA
#print axioms ActualMAJacobi.first_MA_nonzero_left
#print axioms IndependentMAJacobi.logdet_basis_independent
#print axioms IndependentMAJacobi.negative_determinant_direction
#print axioms ActualMASecond.actual_exp_second_MA
#print axioms ActualMASecond.actual_exp_Gram_PSD
#print axioms ActualMASecond.actual_convex_V_PSD
#print axioms ActualMASecond.actual_rank0_Gram_PSD
#print axioms ActualMASecondMatrix.actual_nondiagonal_Gram_PSD
#print axioms IndependentMASecond.actual_signed_gram_positive

namespace ActualMetricIBP
/-! Compact-test integration by parts for `L` (`IntegrationByParts/InverseHessian.lean`, bundle
`MA-Metric-IntegrationByParts`, receipt 719cbc2a…/e1a2fc36…): the normalised one-dimensional Gaussian
potential (`∫ e^{−Φ} = 1`, `∇²Φ = Id`, MA equation with `V = Φ`) against a nonzero bump, with the
unbounded test `id` and only the bump compactly supported; invariance `∫ L(bump) dν = 0`; and the
exponential potential's inverse-Hessian divergence `−1` at `0`. The Gaussian is a normalised-MA consumer,
not the source bounded-`K` moment map. -/
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery

def Z : ℝ := Real.sqrt (2 * Real.pi)
def Phi (x : ℝ) : ℝ := (1 / 2 : ℝ) * x ^ 2 + Real.log Z

theorem Z_pos : 0 < Z := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)

theorem Phi_smooth : ContDiff ℝ ∞ Phi :=
  (contDiff_const.mul (contDiff_id.pow 2)).add contDiff_const

lemma Phi_derivative (x : ℝ) : HasDerivAt Phi x x := by
  have hd := (((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ)).add_const (Real.log Z)
  convert! hd using 1; simp

lemma gradient_Phi (x : ℝ) : gradient Phi x = x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, (Phi_derivative x).hasFDerivAt.fderiv]
  simp [mul_comm]

lemma hessian_Phi (x : ℝ) : hessianOperator Phi x = ContinuousLinearMap.id ℝ ℝ := by
  have he : gradient Phi = id := funext gradient_Phi
  simp [hessianOperator, he]

theorem Phi_PD (x v : ℝ) (hv : v ≠ 0) : 0 < bilinearIteratedFDerivTwo ℝ Phi x v v := by
  rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator
    (Phi_smooth.of_le (WithTop.coe_le_coe.mpr le_top)), hessian_Phi]
  simpa using sq_pos_of_ne_zero hv

lemma matrix_Phi (x : ℝ) : hessianMatrixIn Phi (stdOrthonormalBasis ℝ ℝ) x = 1 := by
  ext i j
  change bilinearIteratedFDerivTwo ℝ Phi x
    (stdOrthonormalBasis ℝ ℝ i) (stdOrthonormalBasis ℝ ℝ j) = _
  rw [← operatorEntry_hessianOperator _ (Phi_smooth.of_le (WithTop.coe_le_coe.mpr le_top)),
    hessian_Phi]
  simp only [FunctionalInequalities.Analysis.operatorEntry, ContinuousLinearMap.id_apply,
    OrthonormalBasis.inner_eq_ite, Matrix.one_apply]

theorem Phi_MA (x : ℝ) : logDetHessian Phi (stdOrthonormalBasis ℝ ℝ) x =
    -Phi x + Phi (gradient Phi x) := by
  rw [logDetHessian, matrix_Phi, Matrix.det_one, Real.log_one, gradient_Phi]
  ring

theorem Phi_normalized : (∫ x : ℝ, Real.exp (-Phi x)) = 1 := by
  have he : (fun x : ℝ => Real.exp (-Phi x)) =
      fun x : ℝ => Z⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    funext x
    calc
      _ = Real.exp (-(1 / 2 : ℝ) * x ^ 2) * Real.exp (-Real.log Z) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [Phi]
        ring
      _ = _ := by rw [Real.exp_neg, Real.exp_log Z_pos]; ring
  rw [he, integral_const_mul, integral_gaussian]
  have heq : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
  rw [heq]
  exact inv_mul_cancel₀ Z_pos.ne'

def test : ContDiffBump (1 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

theorem test_actual_nonzero : test 1 = 1 ∧ test 4 = 0 := by
  constructor
  · exact test.one_of_mem_closedBall (by norm_num [test, Metric.mem_closedBall])
  · exact test.zero_of_le_dist (by norm_num [test, Real.dist_eq])

/-- Normalised Gaussian source, unbounded `f = id`, only `g` compact. -/
theorem Gaussian_only_second_test_compact :
    (∫ x : ℝ, hessianInverseOperator Phi Phi id x * test x ∂(volume.tilted (-Phi))) =
      -∫ x : ℝ, ∑ i, ∑ j, inverseHessianEntry Phi (stdOrthonormalBasis ℝ ℝ) x i j *
        fderiv ℝ id x (stdOrthonormalBasis ℝ ℝ i) *
        fderiv ℝ (test : ℝ → ℝ) x (stdOrthonormalBasis ℝ ℝ j) ∂(volume.tilted (-Phi)) :=
  integral_hessianInverseOperator_mul_eq_neg volume Phi_smooth contDiff_id test.contDiff
    (Or.inr test.hasCompactSupport) isOpen_univ Phi_smooth.contDiffOn (Set.subset_univ _)
    Phi_MA Phi_PD Phi_normalized

/-- Invariance on a nonzero compact smooth test for the normalised Gaussian law. -/
theorem Gaussian_compact_invariance :
    IsProbabilityMeasure (volume.tilted (-Phi)) ∧
      (∫ x : ℝ, hessianInverseOperator Phi Phi (test : ℝ → ℝ) x ∂(volume.tilted (-Phi))) = 0 :=
  ⟨isProbabilityMeasure_tilted_neg_of_integral_eq_one volume Phi Phi_normalized,
    integral_hessianInverseOperator_eq_zero volume Phi_smooth test.contDiff test.hasCompactSupport
      isOpen_univ Phi_smooth.contDiffOn (Set.subset_univ _) Phi_MA Phi_PD Phi_normalized⟩

/-- A nonconstant inverse-Hessian example: for `φ = exp` on `ℝ` the divergence at `0` is `−1`. -/
theorem exp_divergence_nonzero :
    fderiv ℝ (fun y => inverseHessianEntry Real.exp ActualMAJacobi.b y 0 0) 0
      (ActualMAJacobi.b 0) = -1 := by
  have hh := inverseHessian_divergence ActualMAJacobi.b Real.contDiff_exp isOpen_Ioi
    ActualMAJacobi.V_smooth_on ActualMAJacobi.actual_MA_logdet
    (x := (0 : ℝ)) (by rw [ActualMAInverse.gradient_exp]; norm_num)
    (ActualMAInverse.exp_hessian_positive 0) 0
  simp only [Fin.sum_univ_one] at hh
  have hA : inverseHessianEntry Real.exp ActualMAJacobi.b 0 0 0 = 1 := by
    simp [inverseHessianEntry, FunctionalInequalities.Analysis.operatorEntry,
      ActualMAInverse.hessianOperator_exp, ActualMAJacobi.b_apply]
  have hv : HasDerivAt ActualMAJacobi.V (2 : ℝ) 1 := by
    convert! (hasDerivAt_id (1 : ℝ)).fun_add
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)) using 1
    norm_num [ActualMAJacobi.V]
  rw [hA, ActualMAJacobi.b_apply, ActualMAInverse.gradient_exp, Real.exp_zero,
    (Real.hasDerivAt_exp 0).hasFDerivAt.fderiv, hv.hasFDerivAt.fderiv] at hh
  norm_num at hh ⊢
  exact hh
end ActualMetricIBP

namespace ActualMetricZero
/-! Rank zero: the normalised Haar law on `EuclideanSpace ℝ (Fin 0)` with the constant potential, the
MA equation with an empty determinant, invariance and the closure-`K` adapter. -/
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery
abbrev E := EuclideanSpace ℝ (Fin 0)
def Phi (_ : E) : ℝ := 0

theorem source_normalization : (∫ x : E, Real.exp (-Phi x)) = 1 := by
  rw [volume_euclideanSpace_eq_dirac]
  simp [Phi]

theorem source_MA (x : E) : logDetHessian Phi (stdOrthonormalBasis ℝ E) x =
    -Phi x + Phi (gradient Phi x) := by
  have : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [finrank_euclideanSpace_fin]; infer_instance
  simp [logDetHessian, Phi, Matrix.det_isEmpty]

theorem source_PD (x v : E) (hv : v ≠ 0) : 0 < bilinearIteratedFDerivTwo ℝ Phi x v v :=
  (hv (Subsingleton.elim _ _)).elim

private theorem test_compact : HasCompactSupport (fun _ : E => (1 : ℝ)) :=
  isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)

theorem same_source_rank0 :
    IsProbabilityMeasure (volume.tilted (-Phi)) ∧
      (∫ x : E, hessianInverseOperator Phi Phi (fun _ => (1 : ℝ)) x ∂(volume.tilted (-Phi))) = 0 :=
  ⟨isProbabilityMeasure_tilted_neg_of_integral_eq_one volume Phi source_normalization,
    integral_hessianInverseOperator_eq_zero volume contDiff_const contDiff_const test_compact
      isOpen_univ contDiffOn_const (Set.subset_univ _) source_MA source_PD source_normalization⟩

theorem rank0_closure_range_ibp :
    (∫ x : E, hessianInverseOperator Phi Phi (fun _ => (1 : ℝ)) x * (1 : ℝ)
        ∂(volume.tilted (-Phi))) =
      -∫ x : E, ∑ i, ∑ j, inverseHessianEntry Phi (stdOrthonormalBasis ℝ E) x i j *
        fderiv ℝ (fun _ : E => (1 : ℝ)) x (stdOrthonormalBasis ℝ E i) *
        fderiv ℝ (fun _ : E => (1 : ℝ)) x (stdOrthonormalBasis ℝ E j) ∂(volume.tilted (-Phi)) :=
  integral_hessianInverseOperator_mul_eq_neg_on_range volume contDiff_const contDiff_const
    contDiff_const (Or.inl test_compact) (K := Set.univ) isOpen_univ (by simp) contDiffOn_const
    (Set.subset_univ _) source_MA source_PD source_normalization
end ActualMetricZero

#print axioms FunctionalInequalities.Analysis.BakryEmery.inverseHessian_divergence
#print axioms FunctionalInequalities.Analysis.BakryEmery.density_inverseHessian_divergence
#print axioms FunctionalInequalities.Analysis.BakryEmery.density_hessianInverseOperator_flux
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_fderiv_mul_eq_neg_of_hasCompactSupport
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_hessianInverseOperator_mul_eq_neg
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_hessianInverseOperator_mul_eq_neg_on_range
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_hessianInverseOperator_eq_zero
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_hessianInverseOperator_mul_comm
#print axioms ActualMetricIBP.Phi_normalized
#print axioms ActualMetricIBP.test_actual_nonzero
#print axioms ActualMetricIBP.Gaussian_only_second_test_compact
#print axioms ActualMetricIBP.Gaussian_compact_invariance
#print axioms ActualMetricIBP.exp_divergence_nonzero
#print axioms ActualMetricZero.same_source_rank0
#print axioms ActualMetricZero.rank0_closure_range_ibp

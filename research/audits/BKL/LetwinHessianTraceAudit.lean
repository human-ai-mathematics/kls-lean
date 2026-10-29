import FunctionalInequalities.Analysis.BakryEmery.Hessian.Trace

/-!
# Audit: Hessian trace evolution for a nonconstant real potential

Source: Letwin, arXiv:2607.24164v1, (2.8) in the proof of Theorem 2.5 (support only). For the
real potential `φ(x) = x⁴/12 + x²/2` (smooth, Hessian `1 + x²`, positive and nonconstant:
`H(0) ≠ H(1)`), `V = 0` and `B = 1`, the library identity
`hessianInverseOperator_trace_stdHessianMatrix_sq` is invoked at every point. Every premise is
derived. Not (2.10), the trace bound or a moment-map client.
-/

noncomputable section

open scoped BigOperators ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open Matrix

namespace LetwinHessianTraceAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def realGeneratorPotential (x : ℝ) : ℝ :=
  (1 / 12 : ℝ) * x ^ 4 + (1 / 2 : ℝ) * x ^ 2

def realGeneratorV : ℝ → ℝ := fun _ => 0

def realGeneratorB : Matrix (StdBasisIndex ℝ) (StdBasisIndex ℝ) ℝ := 1

def realGeneratorH (x : ℝ) : Matrix (StdBasisIndex ℝ) (StdBasisIndex ℝ) ℝ :=
  stdHessianMatrix realGeneratorPotential x

theorem realGenerator_potential_smooth :
    ContDiff ℝ ∞ realGeneratorPotential := by
  unfold realGeneratorPotential
  exact
    (contDiff_const.mul (contDiff_id.pow 4)).add
      (contDiff_const.mul (contDiff_id.pow 2))

theorem realGenerator_hessian_formula (x v w : ℝ) :
    bilinearIteratedFDerivTwo ℝ realGeneratorPotential x v w =
      (1 + x ^ 2) * v * w := by
  have hfirst (y w : ℝ) :
      fderiv ℝ realGeneratorPotential y w =
        ((1 / 3 : ℝ) * y ^ 3 + y) * w := by
    have hfd : HasDerivAt realGeneratorPotential
        ((1 / 12 : ℝ) * (4 * y ^ 3 * 1) +
          (1 / 2 : ℝ) * (2 * y ^ 1 * 1)) y :=
      (((hasDerivAt_id y).pow 4).const_mul (1 / 12 : ℝ)).add
        (((hasDerivAt_id y).pow 2).const_mul (1 / 2 : ℝ))
    have hF : HasFDerivAt realGeneratorPotential
        (ContinuousLinearMap.toSpanSingleton ℝ
          ((1 / 12 : ℝ) * (4 * y ^ 3 * 1) +
            (1 / 2 : ℝ) * (2 * y ^ 1 * 1))) y :=
      HasDerivAt.hasFDerivAt hfd
    rw [HasFDerivAt.fderiv hF]
    change w * ((1 / 12 : ℝ) * (4 * y ^ 3 * 1) +
        (1 / 2 : ℝ) * (2 * y ^ 1 * 1)) =
      ((1 / 3 : ℝ) * y ^ 3 + y) * w
    ring
  have hsecond (x w : ℝ) :
      HasDerivAt
        (fun y : ℝ => ((1 / 3 : ℝ) * y ^ 3 + y) * w)
        ((x ^ 2 + 1) * w) x := by
    have hd : HasDerivAt
        (fun y : ℝ => ((1 / 3 : ℝ) * y ^ 3 + y) * w)
        (((1 / 3 : ℝ) * (3 * x ^ 2 * 1) + 1) * w) x :=
      ((((hasDerivAt_id x).pow 3).const_mul (1 / 3 : ℝ)).add
        (hasDerivAt_id x)).mul_const w
    have hc :
        (((1 / 3 : ℝ) * (3 * x ^ 2 * 1) + 1) * w) =
          ((x ^ 2 + 1) * w) := by
      ring
    rw [hc] at hd
    exact hd
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply
    (realGenerator_potential_smooth.of_le (WithTop.coe_le_coe.mpr le_top)) x v w]
  have heq :
      (fun y : ℝ => fderiv ℝ realGeneratorPotential y w) =
        fun y => ((1 / 3 : ℝ) * y ^ 3 + y) * w :=
    funext fun y => hfirst y w
  have hF : HasFDerivAt
      (fun y : ℝ => ((1 / 3 : ℝ) * y ^ 3 + y) * w)
      (ContinuousLinearMap.toSpanSingleton ℝ ((x ^ 2 + 1) * w)) x :=
    HasDerivAt.hasFDerivAt (hsecond x w)
  rw [heq, HasFDerivAt.fderiv hF]
  change v * ((x ^ 2 + 1) * w) = (1 + x ^ 2) * v * w
  ring

theorem realGenerator_hessian_entry (x : ℝ)
    (i j : StdBasisIndex ℝ) :
    realGeneratorH x i j =
      (1 + x ^ 2) *
        stdOrthonormalBasis ℝ ℝ i *
        stdOrthonormalBasis ℝ ℝ j := by
  unfold realGeneratorH stdHessianMatrix
  exact realGenerator_hessian_formula x
    (stdOrthonormalBasis ℝ ℝ i)
    (stdOrthonormalBasis ℝ ℝ j)

theorem nonconstant_real_generator_client :
    ContDiff ℝ ∞ realGeneratorPotential ∧
      (∀ x v : ℝ, v ≠ 0 →
        0 < bilinearIteratedFDerivTwo ℝ realGeneratorPotential x v v) ∧
      realGeneratorH 0 ≠ realGeneratorH 1 ∧
      (∀ x : ℝ,
        hessianInverseOperator realGeneratorPotential realGeneratorV
            (fun y =>
              (realGeneratorB * realGeneratorH y * realGeneratorB *
                realGeneratorH y).trace) x =
          2 * (realGeneratorB * realGeneratorH x *
              realGeneratorB *
              stdHessianMatrixGenerator realGeneratorPotential realGeneratorV x).trace +
            2 * ∑ a, ∑ b,
              inverseHessianEntry realGeneratorPotential
                  (stdOrthonormalBasis ℝ ℝ) x a b *
                (realGeneratorB * stdHessianMatrixDeriv realGeneratorPotential x a *
                  realGeneratorB * stdHessianMatrixDeriv realGeneratorPotential x b).trace) := by
  have hφ := realGenerator_potential_smooth
  have hPD : ∀ x v : ℝ, v ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ realGeneratorPotential x v v := by
    intro x v hv
    have hx : 0 < 1 + x ^ 2 := by
      nlinarith [sq_nonneg x]
    have hvv : 0 < v * v := mul_self_pos.mpr hv
    have hmul : 0 < (1 + x ^ 2) * (v * v) := mul_pos hx hvv
    rw [realGenerator_hessian_formula]
    convert hmul using 1; ring
  have hne : realGeneratorH 0 ≠ realGeneratorH 1 := by
    let i : StdBasisIndex ℝ := ⟨0, by simp [Module.finrank_self]⟩
    let e : ℝ := stdOrthonormalBasis ℝ ℝ i
    have he_norm : ‖e‖ = 1 := by
      dsimp [e]
      exact (stdOrthonormalBasis ℝ ℝ).norm_eq_one i
    have habs : |e| = 1 := by
      simpa only [Real.norm_eq_abs] using he_norm
    have hsq : e * e = 1 := by
      calc
        e * e = e ^ 2 := by ring
        _ = |e| ^ 2 := by rw [sq_abs]
        _ = 1 := by rw [habs]; norm_num
    intro h
    have heq := congrArg
      (fun M : Matrix (StdBasisIndex ℝ) (StdBasisIndex ℝ) ℝ => M i i) h
    change
      bilinearIteratedFDerivTwo ℝ realGeneratorPotential 0 e e =
        bilinearIteratedFDerivTwo ℝ realGeneratorPotential 1 e e at heq
    rw [realGenerator_hessian_formula, realGenerator_hessian_formula] at heq
    nlinarith [heq, hsq]
  have hmain : ∀ x : ℝ,
      hessianInverseOperator realGeneratorPotential realGeneratorV
          (fun y =>
            (realGeneratorB * realGeneratorH y * realGeneratorB *
              realGeneratorH y).trace) x =
        2 * (realGeneratorB * realGeneratorH x *
            realGeneratorB *
            stdHessianMatrixGenerator realGeneratorPotential realGeneratorV x).trace +
          2 * ∑ a, ∑ b,
            inverseHessianEntry realGeneratorPotential
                (stdOrthonormalBasis ℝ ℝ) x a b *
              (realGeneratorB * stdHessianMatrixDeriv realGeneratorPotential x a *
                realGeneratorB * stdHessianMatrixDeriv realGeneratorPotential x b).trace := by
    intro x
    simpa [realGeneratorH] using
      (hessianInverseOperator_trace_stdHessianMatrix_sq (E := ℝ)
        (φ := realGeneratorPotential) (V := realGeneratorV)
        hφ realGeneratorB x)
  exact ⟨hφ, hPD, hne, hmain⟩

end LetwinHessianTraceAudit

#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianInverseOperator_trace_stdHessianMatrix_sq
#print axioms LetwinHessianTraceAudit.realGenerator_potential_smooth
#print axioms LetwinHessianTraceAudit.realGenerator_hessian_formula
#print axioms LetwinHessianTraceAudit.realGenerator_hessian_entry
#print axioms LetwinHessianTraceAudit.nonconstant_real_generator_client

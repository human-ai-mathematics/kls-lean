module

public import FunctionalInequalities.Analysis.Convex.Pogorelov
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section
open Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise RealInnerProductSpace
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
namespace LetwinPogorelovAudit

private theorem nondiagonal_posDef :
    (!![(1 / 2 : ℝ), 1 / 4; 1 / 4, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  let H : Matrix (Fin 2) (Fin 2) ℝ := !![(1 / 2 : ℝ), 1 / 4; 1 / 4, 1 / 2]
  have hh : H.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [H]
  have hp : H.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hh
    intro y hy
    have hn : y 0 ≠ 0 ∨ y 1 ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hy
      ext i
      fin_cases i
      · exact hn.1
      · exact hn.2
    have hf :
      star y ⬝ᵥ (H *ᵥ y) =
        (1 / 2 : ℝ) * (y 0) ^ 2 + (1 / 2 : ℝ) * y 0 * y 1 + (1 / 2 : ℝ) * (y 1) ^ 2 := by
      simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      ring
    rw [hf]
    rcases hn with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (y 0 + y 1), sq_nonneg (y 1)]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (y 0 + y 1), sq_nonneg (y 0)]
  exact hp

/-- A genuinely NONDIAGONAL classical source constructs its logarithmic maximum
and applies the coordinate-free point estimate. No Hessian/maximum/frame is supplied. -/
theorem actual_nondiagonal_quadratic_point :
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![(1 / 2 : ℝ), 1 / 4; 1 / 4, 1 / 2]
    let u := quadraticAt H 0 0 (-1)
    H 0 1 ≠ 0 ∧
      ContDiff ℝ 4 u ∧
        (∀ y, hessianMatrix u y = H) ∧
          IsLocalMax
              (fun y =>
                Real.log (hessianMatrix u y 0 0) + Real.log (u y) +
                  (1 / 2 : ℝ) * (fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ^ 2)
              0 ∧
            hessianMatrix u 0 0 0 * (-u 0) ≤
              2 + |fderiv ℝ u 0 (EuclideanSpace.basisFun (Fin 2) ℝ 0)| := by
  dsimp only
  let H : Matrix (Fin 2) (Fin 2) ℝ := !![(1 / 2 : ℝ), 1 / 4; 1 / 4, 1 / 2]
  let u := quadraticAt H 0 0 (-1)
  have hp : H.PosDef := nondiagonal_posDef
  have hh : H.IsHermitian := hp.isHermitian
  have hu : ContDiff ℝ 4 u := contDiff_quadraticAt_all _ _ _ _
  have hH (y : EuclideanSpace ℝ (Fin 2)) : hessianMatrix u y = H :=
    hessianMatrix_quadraticAt hh _ _ _ _
  have hd (y : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      (1 / 2 : ℝ) * y 0 + (1 / 4 : ℝ) * y 1 := by
    rw [← inner_gradient_left, gradient_quadraticAt hh]
    simp [H, Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.inner_single_right,
      dotProduct, Fin.sum_univ_succ]
  have hv (y : EuclideanSpace ℝ (Fin 2)) :
    u y = -1 + (1 / 4 : ℝ) * (y 0) ^ 2 + (1 / 4 : ℝ) * y 0 * y 1 + (1 / 4 : ℝ) * (y 1) ^ 2 := by
    simp [u, quadraticAt, H, Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.inner_apply,
      dotProduct, Fin.sum_univ_succ]
    ring
  have hmax :
    IsLocalMax
      (fun y =>
        Real.log (hessianMatrix u y 0 0) + Real.log (u y) +
          (1 / 2 : ℝ) * (fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ^ 2)
      0 := by
    have hn : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin 2)), u y < 0 :=
      (hu.continuous.continuousAt.eventually (gt_mem_nhds (by norm_num [hv] : u 0 < 0)))
    filter_upwards [hn] with y hy
    have hl := Real.log_le_sub_one_of_pos (neg_pos.mpr hy)
    have hg :
      (1 / 2 : ℝ) * ((1 / 2 : ℝ) * y 0 + (1 / 4 : ℝ) * y 1) ^ 2 ≤
        (1 / 4 : ℝ) * (y 0) ^ 2 + (1 / 4 : ℝ) * y 0 * y 1 + (1 / 4 : ℝ) * (y 1) ^ 2 := by
      nlinarith [sq_nonneg (y 0 + y 1), sq_nonneg (y 0), sq_nonneg (y 1)]
    rw [Real.log_neg_eq_log, hv y] at hl
    have ht : Real.log (u y) + (1 / 2 : ℝ) * ((1 / 2 : ℝ) * y 0 + (1 / 4 : ℝ) * y 1) ^ 2 ≤ 0 := by
      rw [hv y]
      linarith
    rw [hH y, hH 0, hd y, hd 0]
    simpa [hv, add_assoc] using ht
  refine ⟨by norm_num [H], hu, hH, hmax, ?_⟩
  have heq (y) : (hessianMatrix u y).det = (3 / 16 : ℝ) := by
    rw [hH y]
    norm_num [H, Matrix.det_fin_two]
  have hp0 : (hessianMatrix u 0).PosDef := by rw [hH 0]; exact hp
  exact
    Pogorelov.bound_of_local_max hu.contDiffAt (by norm_num) (Filter.Eventually.of_forall heq)
      hp0 (by norm_num [hv]) 0 hmax

/-- The SAME actual off-diagonal positive form generates an axis-fixing frame. -/
theorem actual_nondiagonal_frame :
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![(1 / 2 : ℝ), 1 / 4; 1 / 4, 1 / 2]
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : Fin 2 → ℝ),
      IsUnit A ∧
        A *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧ (∀ i, 0 < d i) ∧ Aᵀ * H * A = Matrix.diagonal d := by
  exact exists_diagonal_frame_fixing_axis _ nondiagonal_posDef 0

end LetwinPogorelovAudit
#print axioms LetwinPogorelovAudit.actual_nondiagonal_quadratic_point

#print axioms LetwinPogorelovAudit.actual_nondiagonal_frame

module

public import FunctionalInequalities.Analysis.Elliptic.HalfBall
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Clients of the half-ball closure and one-sided normal derivative

* `abs_last_one_sided_normal_client`: `v x = |xₙ|` on the WHOLE ambient space `ℝ^{m+1}` (every `m`;
  `m = 0` is
  the ambient line `Fin 1` with no tangential direction, not an empty carrier). It is `C¹` on the
  closed half-ball,
  where it agrees with the linear height `xₙ`; the main theorem gives the one-sided normal
  derivative and slope
  value `1` at `z = 0`, while `v` is NOT differentiable at `0` in the ambient sense, so its default
  ambient
  `fderiv` there is `0`. A statement using ambient `C¹` or the default global derivative would be
  wrong here.
* `closure_halfBall_fin_one`: in the ambient line (`m = 0`), the closed half-ball is `{x | x₀ ∈ [0,
  R]}`.
* `affine_nonzero_flat_point_client`: `v x = xₙ + 2 x₀ + 5` at the nonzero flat point `z = e₀/2` (`m
  + 1 ≥ 1`
  tangential directions): normal derivative and slope limit `1`.
-/

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace FunctionalInequalities.Analysis.HalfBallBoundaryClient

open FunctionalInequalities.Analysis

/--
**`|xₙ|`: one-sided normal derivative `1` from `C¹` on the closure, but no ambient derivative at
`0`.** -/
theorem abs_last_one_sided_normal_client (m : ℕ) :
    ContDiffOn ℝ 1 (fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|)
        (closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < 1 ∧ 0 < x (Fin.last m)}) ∧
      HasDerivWithinAt
          (fun t : ℝ =>
            |((0 : EuclideanSpace ℝ (Fin (m + 1))) +
                  t • EuclideanSpace.single (Fin.last m) (1 : ℝ))
                (Fin.last m)|)
          1 (Ici 0) 0 ∧
        Tendsto
            (fun t : ℝ =>
              (|((0 : EuclideanSpace ℝ (Fin (m + 1))) +
                        t • EuclideanSpace.single (Fin.last m) (1 : ℝ))
                      (Fin.last m)| -
                  |(0 : EuclideanSpace ℝ (Fin (m + 1))) (Fin.last m)|) /
                t)
            (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
          fderivWithin ℝ (fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|)
                (closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < 1 ∧ 0 < x (Fin.last m)}) 0
                (EuclideanSpace.single (Fin.last m) (1 : ℝ)) =
              1 ∧
            ¬DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|) 0 ∧
              fderiv ℝ (fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|) 0
                  (EuclideanSpace.single (Fin.last m) (1 : ℝ)) =
                0 := by
  set p : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last m) with hp
  set e : EuclideanSpace ℝ (Fin (m + 1)) := EuclideanSpace.single (Fin.last m) (1 : ℝ) with he
  set K := closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < 1 ∧ 0 < x (Fin.last m)} with hK
  have hKeq : K = {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ 1 ∧ 0 ≤ x (Fin.last m)} :=
    closure_halfBall
      one_pos
        -- agreement with the linear height on the closed half-ball

  have hEq : EqOn (fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|) p K := by
    intro x hx
    rw [hKeq] at hx
    simp [hp, abs_of_nonneg hx.2]
  have hC1 : ContDiffOn ℝ 1 (fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|) K :=
    p.contDiff.contDiffOn.congr fun x hx => hEq hx
  have h0K : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ K := by
    rw [hKeq]
    simp
  have hval :
    fderivWithin ℝ (fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|) K 0 e = 1 := by
    rw [fderivWithin_congr' hEq h0K,
      p.fderivWithin (uniqueDiffOn_closure_halfBall one_pos 0 h0K)]
    simp [hp, he]
  obtain ⟨hd, hs⟩ := normal_derivative_halfBall one_pos hC1 (z := 0) (by simp) (by simp)
  rw [hval] at hd hs
        -- no ambient derivative at `0`: along the normal line `v (t e) = |t|`

  have hnd :
    ¬DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|) 0 := by
    intro hdiff
    have hdiff' :
      DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|)
        ((0 : ℝ) • e) := by
      rwa [zero_smul]
    have hline : DifferentiableAt ℝ (fun t : ℝ => t • e) 0 := differentiableAt_id.smul_const e
    have hcomp := hdiff'.comp (0 : ℝ) hline
    have hfun :
      ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => |x (Fin.last m)|) ∘ fun t : ℝ => t • e) =
        fun t : ℝ => |t| := by
      funext t
      simp [he]
    rw [hfun] at hcomp
    exact not_differentiableAt_abs_zero hcomp
  refine ⟨hC1, hd, hs, hval, hnd, ?_⟩
  rw [fderiv_zero_of_not_differentiableAt hnd]
  rfl

/--
**The ambient line `Fin 1` (`m = 0`, no tangential direction)**: the closed half-ball is the
interval
`x₀ ∈ [0, R]`. -/
theorem closure_halfBall_fin_one {R : ℝ} (hR : 0 < R) :
    closure {x : EuclideanSpace ℝ (Fin (0 + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last 0)} =
      {x : EuclideanSpace ℝ (Fin (0 + 1)) | x (Fin.last 0) ∈ Icc 0 R} := by
  rw [closure_halfBall hR]
  ext x
  have hn : ‖x‖ = |x (Fin.last 0)| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
    rfl
  simp only [Set.mem_ofPred_eq, mem_Icc, hn]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (le_abs_self _).trans h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [abs_of_nonneg h1], h1⟩

/--
**Affine function at a nonzero flat point** `z = e₀/2` of the unit half-ball in `ℝ^{m+2}`. -/
theorem affine_nonzero_flat_point_client (m : ℕ) :
    HasDerivWithinAt
        (fun t : ℝ =>
          (fun x : EuclideanSpace ℝ (Fin (m + 1 + 1)) => x (Fin.last (m + 1)) + 2 * x 0 + 5)
            ((1 / 2 : ℝ) • EuclideanSpace.single 0 (1 : ℝ) +
              t • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)))
        1 (Ici 0) 0 ∧
      Tendsto
        (fun t : ℝ =>
          ((fun x : EuclideanSpace ℝ (Fin (m + 1 + 1)) => x (Fin.last (m + 1)) + 2 * x 0 + 5)
                ((1 / 2 : ℝ) • EuclideanSpace.single 0 (1 : ℝ) +
                  t • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)) -
              (fun x : EuclideanSpace ℝ (Fin (m + 1 + 1)) => x (Fin.last (m + 1)) + 2 * x 0 + 5)
                ((1 / 2 : ℝ) • EuclideanSpace.single 0 (1 : ℝ))) /
            t)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  set pl : EuclideanSpace ℝ (Fin (m + 1 + 1)) →L[ℝ] ℝ :=
    EuclideanSpace.proj (Fin.last (m + 1)) with hpl
  set p0 : EuclideanSpace ℝ (Fin (m + 1 + 1)) →L[ℝ] ℝ := EuclideanSpace.proj 0 with hp0
  set z : EuclideanSpace ℝ (Fin (m + 1 + 1)) :=
    (1 / 2 : ℝ) • EuclideanSpace.single 0 (1 : ℝ) with hz
  set K :=
    closure {x : EuclideanSpace ℝ (Fin (m + 1 + 1)) | ‖x‖ < 1 ∧ 0 < x (Fin.last (m + 1))} with
    hK
  have hl0 : (Fin.last (m + 1) : Fin (m + 1 + 1)) ≠ 0 := by simp [Fin.ext_iff]
  have hF :
    HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin (m + 1 + 1)) => x (Fin.last (m + 1)) + 2 * x 0 + 5)
      (pl + (2 : ℝ) • p0) z :=
    (pl.hasFDerivAt.add (p0.hasFDerivAt.const_mul 2)).add_const 5
  have hzK : z ∈ K := by
    rw [hK, closure_halfBall one_pos]
    refine ⟨?_, ?_⟩
    · simp [hz, norm_smul]
      norm_num
    · simp [hz, hl0]
  have hval :
    fderivWithin ℝ
        (fun x : EuclideanSpace ℝ (Fin (m + 1 + 1)) => x (Fin.last (m + 1)) + 2 * x 0 + 5) K z
        (EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)) =
      1 := by
    rw [hF.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_closure_halfBall one_pos z hzK)]
    simp [hpl, hp0]
  have hC :
    ContDiff ℝ 1
      (fun x : EuclideanSpace ℝ (Fin (m + 1 + 1)) => x (Fin.last (m + 1)) + 2 * x 0 + 5) :=
    (pl.contDiff.add (contDiff_const.mul p0.contDiff)).add contDiff_const
  obtain ⟨hd, hs⟩ :=
    normal_derivative_halfBall one_pos hC.contDiffOn (z := z)
      (by simp [hz, norm_smul]; norm_num) (by simp [hz, hl0])
  rw [hval] at hd hs
  exact ⟨hd, hs⟩

end FunctionalInequalities.Analysis.HalfBallBoundaryClient

#print axioms
  FunctionalInequalities.Analysis.HalfBallBoundaryClient.abs_last_one_sided_normal_client
#print axioms FunctionalInequalities.Analysis.HalfBallBoundaryClient.closure_halfBall_fin_one
#print axioms
  FunctionalInequalities.Analysis.HalfBallBoundaryClient.affine_nonzero_flat_point_client

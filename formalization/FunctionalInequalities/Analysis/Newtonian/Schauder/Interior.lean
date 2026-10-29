import FunctionalInequalities.Analysis.Newtonian.Potential.C2
import FunctionalInequalities.Analysis.Newtonian.Schauder.Potential
import FunctionalInequalities.Analysis.Newtonian.Potential.GradientBound
import FunctionalInequalities.Analysis.Harmonic.BallHolder

/-!
# Interior Hessian Hölder estimate for the Poisson equation on a ball (GT Theorem 4.6)

Theorem 4.6 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001
(ISBN 3-540-41160-7), p. 60, in Hessian form. For `n ≥ 2` (including `n = 2`) and `0 < α < 1`,
`poisson_interior_hessian_holder` gives one constant `C(n, α) > 0`, chosen before the centre `c`, the
radius `R` and the data, such that every `u ∈ C²(B_{2R}(c))` with `Δu = f` on `B_{2R}(c)`, `|u| ≤ U`,
`|f| ≤ M` and `[f]_{α; B_{2R}(c)} ≤ H` satisfies on `B_R(c)`
`‖D²u‖ ≤ C (U R⁻² + M + R^α H)` and `‖D²u(x) - D²u(y)‖ ≤ C (U R^(-2-α) + M R^(-α) + H) ‖x - y‖^α`.

The proof is GT's direct route on p. 60. With `w` the Newtonian potential of `f` over `B_{2R}(c)`:
Lemma 4.2 (`newtonianPotential_contDiffOn_two`) gives `w ∈ C²(B_{2R})` with `Δw = f`; Lemma 4.4
(`newtonianPotential_schauder`) bounds `D²w`; the gradient bound `norm_fderiv_newtonianPotential_ball_le` and
the mean value inequality give `|w - w(c)| ≤ 8 n R² M` on `B_{2R}`; `h = u - (w - w(c))` is harmonic on
`B_{2R}` with `|h| ≤ U + 8 n R² M`, and the harmonic interior estimate `ball_harmonic_hessian_holder` bounds
`D²h`. Since `D²u = D²h + D²w` on `B_R`, the two estimates add up.

Scope: the estimate is stated on the open ball `B_R(c)` with the norm of the Hessian as a continuous
bilinear map; the case `α = 1`, the global `C^{2,α}(Ω)` norms of GT (4.20)–(4.22) and boundary
estimates are not claimed. The constant is coarse.
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace FunctionalInequalities.Analysis

/-- **GT 2001 Theorem 4.6 (p. 60), Hessian form.** Interior Hessian and Hessian-Hölder estimates on `B_R(c)` for
`C²` solutions of `Δu = f` on `B_{2R}(c)`, with one constant `C(n, α)` for `n ≥ 2` and `0 < α < 1`. -/
theorem poisson_interior_hessian_holder {n : ℕ} (hn : 2 ≤ n) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ) (U M : ℝ) (H : ℝ≥0),
      ContDiffOn ℝ 2 u (ball c (2 * R)) → (∀ x ∈ ball c (2 * R), Laplacian.laplacian u x = f x) →
      (∀ x ∈ ball c (2 * R), |u x| ≤ U) → (∀ y ∈ ball c (2 * R), |f y| ≤ M) →
      HolderOnWith H α f (ball c (2 * R)) →
      (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H)) ∧
      ∀ x ∈ ball c R, ∀ y ∈ ball c R,
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
          C * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
  obtain ⟨Ch, hCh, hharm⟩ := ball_harmonic_hessian_holder hn
  obtain ⟨Cw, hCw, hnewt⟩ := newtonianPotential_schauder hn hα0 hα1
  refine ⟨Ch * (1 + 8 * n) + Cw, by positivity, ?_⟩
  intro c R hR u f U M H hu hLap hU hM hH
  obtain ⟨w, hw_def⟩ : ∃ w, w = newtonianPotential n (ball c (2 * R)) f := ⟨_, rfl⟩
  obtain ⟨hw2, hwsup, hwhol, -, -⟩ := hnewt c R hR f M H hM hH
  rw [← hw_def] at hw2 hwsup hwhol
  have hB : IsOpen (ball c (2 * R)) := isOpen_ball
  have hR2 : 0 < 2 * R := by positivity
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (mem_ball_self hR2))
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU c (mem_ball_self hR2))
  have hαr0 : (0:ℝ) < α := hα0
  have hαr1 : (α:ℝ) < 1 := hα1
  -- Step 1 (Lemma 4.2): `Δw = f` on `B_{2R}`.
  have hwLap : ∀ x ∈ ball c (2 * R), Laplacian.laplacian w x = f x := by
    rw [hw_def]
    exact (newtonianPotential_contDiffOn_two hn hB isBounded_ball ⟨M, hM⟩ hα0 hα1.le
      (localHolder_of_holderOnWith_ball hH)).2.1
  -- Step 3: oscillation of `w` on `B_{2R}` from the gradient bound.
  have hfm : AEMeasurable f (volume.restrict (ball c (2 * R))) :=
    (hH.continuousOn hα0).aemeasurable measurableSet_ball
  have hDw : ∀ x ∈ ball c (2 * R), ‖fderiv ℝ w x‖ ≤ n * (2 * (2 * R)) * M := fun x hx => by
    rw [hw_def]; exact norm_fderiv_newtonianPotential_ball_le hn hR2 hfm hM (ball_subset_closedBall hx)
  have hw_at : ∀ x ∈ ball c (2 * R), ContDiffAt ℝ 2 w x := fun x hx => hw2.contDiffAt (hB.mem_nhds hx)
  have hu_at : ∀ x ∈ ball c (2 * R), ContDiffAt ℝ 2 u x := fun x hx => hu.contDiffAt (hB.mem_nhds hx)
  have hwd : ∀ x ∈ ball c (2 * R), DifferentiableAt ℝ w x := fun x hx =>
    (hw_at x hx).differentiableAt (by norm_num)
  have hwosc : ∀ x ∈ ball c (2 * R), |w x - w c| ≤ 8 * n * R ^ 2 * M := by
    intro x hx
    have hmv := (convex_ball c (2 * R)).norm_image_sub_le_of_norm_fderiv_le hwd hDw (mem_ball_self hR2) hx
    rw [Real.norm_eq_abs] at hmv
    have hxc : ‖x - c‖ ≤ 2 * R := by rw [← dist_eq_norm]; exact (mem_ball.mp hx).le
    have hK : 0 ≤ (n:ℝ) * (2 * (2 * R)) * M := by positivity
    calc |w x - w c| ≤ (n:ℝ) * (2 * (2 * R)) * M * ‖x - c‖ := hmv
      _ ≤ (n:ℝ) * (2 * (2 * R)) * M * (2 * R) := mul_le_mul_of_nonneg_left hxc hK
      _ = 8 * n * R ^ 2 * M := by ring
  -- Step 4: the harmonic part `h = u - (w - w(c))`.
  obtain ⟨h, hh_def⟩ : ∃ h : EuclideanSpace ℝ (Fin n) → ℝ, h = fun z => u z - w z + w c := ⟨_, rfl⟩
  have hh_at : ∀ x ∈ ball c (2 * R), ContDiffAt ℝ 2 h x := fun x hx => by
    rw [hh_def]; exact ((hu_at x hx).sub (hw_at x hx)).add contDiffAt_const
  have hhC : ContDiffOn ℝ 2 h (ball c (2 * R)) := fun x hx => (hh_at x hx).contDiffWithinAt
  have hhLap : ∀ y ∈ ball c (2 * R), Laplacian.laplacian h y = 0 := by
    intro y hy
    have hsub : ContDiffAt ℝ 2 (u - w) y := (hu_at y hy).sub (hw_at y hy)
    have hfun : h = (u - w) + fun _ => w c := by rw [hh_def]; rfl
    rw [hfun, hsub.laplacian_add contDiffAt_const, (hu_at y hy).laplacian_sub (hw_at y hy), hLap y hy,
      hwLap y hy]
    simp
  have hhb : ∀ y ∈ ball c (2 * R), |h y| ≤ U + 8 * n * R ^ 2 * M := by
    intro y hy
    have h1 := abs_le.mp (hU y hy)
    have h2 := abs_le.mp (hwosc y hy)
    rw [hh_def, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨hhsup, hhhol⟩ := hharm α hαr0 hαr1 h c R hR hhC hhLap _ hhb
  -- Step 5: `D²u = D²h + D²w` on `B_R`.
  have hdiff : ∀ x ∈ ball c R,
      fderiv ℝ (fderiv ℝ u) x = fderiv ℝ (fderiv ℝ h) x + fderiv ℝ (fderiv ℝ w) x := by
    intro x hx
    have hx2 : x ∈ ball c (2 * R) := ball_subset_ball (by linarith) hx
    have hfirst : ∀ y ∈ ball c (2 * R), fderiv ℝ u y = (fderiv ℝ h + fderiv ℝ w) y := by
      intro y hy
      have hu_eq : u = fun z => (h + w) z - w c := by
        funext z; rw [hh_def]; simp only [Pi.add_apply]; ring
      rw [hu_eq, fderiv_sub_const, fderiv_add ((hh_at y hy).differentiableAt (by norm_num))
        ((hw_at y hy).differentiableAt (by norm_num))]
      rfl
    have hev : fderiv ℝ u =ᶠ[𝓝 x] fderiv ℝ h + fderiv ℝ w :=
      Filter.eventually_of_mem (hB.mem_nhds hx2) hfirst
    rw [hev.fderiv_eq]
    exact fderiv_add (((hh_at x hx2).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      (((hw_at x hx2).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  -- Step 6: combine the two estimates.
  have hRinv2 : (R⁻¹) ^ 2 = R ^ (-(2:ℝ)) := by
    rw [Real.rpow_neg hR.le, Real.rpow_two, inv_pow]
  have hRinvα : (R⁻¹) ^ ((2:ℝ) + α) = R ^ (-(2:ℝ) - α) := by
    rw [Real.inv_rpow hR.le, show -(2:ℝ) - α = -((2:ℝ) + α) by ring, Real.rpow_neg hR.le]
  have hRα : R ^ (-(2:ℝ) - α) * R ^ 2 = R ^ (-(α:ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hR]; congr 1; ring
  have hR2' : R ^ (-(2:ℝ)) * R ^ 2 = 1 := by
    rw [← Real.rpow_two, ← Real.rpow_add hR]; simp
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hHr : (0:ℝ) ≤ H := H.coe_nonneg
  have hA2 : 0 ≤ R ^ (-(2:ℝ)) := Real.rpow_nonneg hR.le _
  have hAα : 0 ≤ R ^ (-(α:ℝ)) := Real.rpow_nonneg hR.le _
  have hA2α : 0 ≤ R ^ (-(2:ℝ) - α) := Real.rpow_nonneg hR.le _
  have hRαH : 0 ≤ R ^ (α:ℝ) * H := mul_nonneg (Real.rpow_nonneg hR.le _) hHr
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have hx2 : x ∈ closedBall c R := ball_subset_closedBall hx
    rw [hdiff x hx]
    have e1 : Ch * (R⁻¹) ^ 2 * (U + 8 * n * R ^ 2 * M) =
        Ch * (U * R ^ (-(2:ℝ))) + 8 * n * Ch * M := by
      rw [hRinv2]; linear_combination (8 * n * Ch * M) * hR2'
    calc ‖fderiv ℝ (fderiv ℝ h) x + fderiv ℝ (fderiv ℝ w) x‖
        ≤ ‖fderiv ℝ (fderiv ℝ h) x‖ + ‖fderiv ℝ (fderiv ℝ w) x‖ := ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ Ch * (R⁻¹) ^ 2 * (U + 8 * n * R ^ 2 * M) + Cw * (M + R ^ (α:ℝ) * H) :=
          add_le_add (hhsup x hx) (hwsup x hx2)
      _ ≤ (Ch * (1 + 8 * n) + Cw) * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H) := by
          rw [e1]
          have hUA : 0 ≤ U * R ^ (-(2:ℝ)) := mul_nonneg hU0 hA2
          nlinarith [mul_nonneg (mul_nonneg hn0 hCh.le) hUA, mul_nonneg hCw.le hUA,
            mul_nonneg (mul_nonneg hn0 hCh.le) hRαH, mul_nonneg hCh.le hRαH, mul_nonneg hCh.le hM0,
            mul_nonneg hCw.le hM0, mul_nonneg hCw.le hRαH]
  · have hx2 : x ∈ closedBall c R := ball_subset_closedBall hx
    have hy2 : y ∈ closedBall c R := ball_subset_closedBall hy
    rw [hdiff x hx, hdiff y hy]
    set t := ‖x - y‖ ^ (α:ℝ) with ht
    have ht0 : 0 ≤ t := Real.rpow_nonneg (norm_nonneg _) _
    have e1 : Ch * (R⁻¹) ^ ((2:ℝ) + α) * (U + 8 * n * R ^ 2 * M) =
        Ch * (U * R ^ (-(2:ℝ) - α)) + 8 * n * Ch * (M * R ^ (-(α:ℝ))) := by
      rw [hRinvα, ← hRα]; ring
    have hsplit : fderiv ℝ (fderiv ℝ h) x + fderiv ℝ (fderiv ℝ w) x -
        (fderiv ℝ (fderiv ℝ h) y + fderiv ℝ (fderiv ℝ w) y) =
        (fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ h) y) +
          (fderiv ℝ (fderiv ℝ w) x - fderiv ℝ (fderiv ℝ w) y) := by abel
    rw [hsplit]
    have hUA : 0 ≤ U * R ^ (-(2:ℝ) - α) := mul_nonneg hU0 hA2α
    have hMA : 0 ≤ M * R ^ (-(α:ℝ)) := mul_nonneg hM0 hAα
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ h) y‖ +
          ‖fderiv ℝ (fderiv ℝ w) x - fderiv ℝ (fderiv ℝ w) y‖ := ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ Ch * (R⁻¹) ^ ((2:ℝ) + α) * (U + 8 * n * R ^ 2 * M) * t +
          Cw * (M * R ^ (-(α:ℝ)) + H) * t := add_le_add (hhhol x hx y hy) (hwhol x hx2 y hy2)
      _ ≤ (Ch * (1 + 8 * n) + Cw) * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * t := by
          rw [e1]
          apply le_of_sub_nonneg
          have key : 0 ≤ (8 * n * Ch * (U * R ^ (-(2:ℝ) - α)) + Cw * (U * R ^ (-(2:ℝ) - α)) +
              Ch * (M * R ^ (-(α:ℝ))) + Ch * (1 + 8 * n) * H) := by positivity
          have := mul_nonneg key ht0
          linear_combination this

end FunctionalInequalities.Analysis

import FunctionalInequalities.Analysis.Newtonian.First
import FunctionalInequalities.Analysis.Cutoff.Profile

/-!
# Smooth truncation of the Newtonian kernel

The truncation `truncatedNewtonianKernel n eps y = Γ(y) (1 - smoothTransition (2 - ‖y‖ / eps))` of the
kernel of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001
(ISBN 3-540-41160-7), (2.12), used to approximate the singular integrals of Lemmas 4.1–4.2 and (4.15):

* `truncatedNewtonianKernel_eq_zero`, `truncatedNewtonianKernel_eq_of_far`: it vanishes on the ball
  of radius `eps` and coincides with `Γ` outside the ball of radius `2 eps`;
* `contDiff_truncatedNewtonianKernel`: for `n ≥ 2` and `eps > 0` it is globally `C^∞`.
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace FunctionalInequalities.Analysis

/-- The actual normalized scalar kernel with its singularity cut out: it vanishes on
`‖y‖ ≤ eps` and equals `Γ` on `2 eps ≤ ‖y‖`. The cutoff profile is
`s ↦ smoothTransition (2 - s)` from `Analysis/Cutoff/Profile.lean`. -/
def truncatedNewtonianKernel (n : ℕ) (eps : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  newtonianKernel n y*(1-Real.smoothTransition (2-‖y‖/eps))

theorem truncatedNewtonianKernel_eq_zero {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    (y : EuclideanSpace ℝ (Fin n)) (hy : ‖y‖ ≤ eps) : truncatedNewtonianKernel n eps y = 0 := by
  have hq : ‖y‖/eps ≤ 1 := (div_le_one heps).mpr hy
  have hp : Real.smoothTransition (2-‖y‖/eps)=1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp only [truncatedNewtonianKernel,hp,sub_self,mul_zero]

theorem truncatedNewtonianKernel_eq_of_far {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    (y : EuclideanSpace ℝ (Fin n)) (hy : 2*eps ≤ ‖y‖) :
    truncatedNewtonianKernel n eps y = newtonianKernel n y := by
  have hq : 2 ≤ ‖y‖/eps := (le_div_iff₀ heps).mpr hy
  have hp : Real.smoothTransition (2-‖y‖/eps)=0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp only [truncatedNewtonianKernel,hp,sub_zero,mul_one]

/-- The truncated scalar kernel is globally smooth for each positive
cutoff radius. `Γ` itself is only asserted smooth off `0`. -/
theorem contDiff_truncatedNewtonianKernel {n : ℕ} (hn : 2 ≤ n)
    {eps : ℝ} (heps : 0 < eps) : ContDiff ℝ ∞ (truncatedNewtonianKernel n eps) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : truncatedNewtonianKernel n eps =ᶠ[𝓝 (0:EuclideanSpace ℝ (Fin n))] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds (0:EuclideanSpace ℝ (Fin n)) heps] with y hy
      have hyr : ‖y‖ < eps := by simpa only [mem_ball,dist_zero_right] using hy
      exact truncatedNewtonianKernel_eq_zero heps y hyr.le
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hp : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2-s)) :=
      FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff.1
    have hr : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖/eps) x :=
      (contDiffAt_norm ℝ hx).div_const eps
    exact (contDiffAt_newtonianKernel hn x hx ∞).mul
      (contDiffAt_const.sub (hp.contDiffAt.comp x hr))

end FunctionalInequalities.Analysis

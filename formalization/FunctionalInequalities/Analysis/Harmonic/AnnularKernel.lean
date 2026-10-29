import FunctionalInequalities.Analysis.Newtonian.Truncation.Basic
import FunctionalInequalities.Analysis.Newtonian.Kernel.Harmonic
import FunctionalInequalities.Analysis.IteratedDerivative.Affine
import FunctionalInequalities.Analysis.BakryEmery.Calculus

/-!
# The smooth annular reproducing kernel

Supporting the harmonic part of the interior estimates of Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Theorem 4.6, p. 60, and the
derivative estimates for harmonic functions, Theorem 2.10 / (2.31). For `n ≥ 2` (including the
logarithmic planar kernel) and `ε > 0`:

* `annularKernel n ε = Δ (truncatedNewtonianKernel n ε)`, the Laplacian of the fundamental solution
  `Γ` of GT (2.12) with its singularity smoothly cut out;
* `contDiff_annularKernel`: it is globally `C^∞`;
* `annularKernel_eq_zero_near`, `annularKernel_eq_zero_far`, `tsupport_annularKernel_subset`: it
  vanishes on `‖x‖ < ε` (the truncation is `0` there) and on `‖x‖ > 2ε` (the truncation is `Γ`
  there and `ΔΓ = 0` off the origin), so its support lies in the annulus `ε ≤ ‖x‖ ≤ 2ε`;
* `hasCompactSupport_annularKernel`, `integrable_annularKernel`: it is compactly supported and
  integrable.

The sign is the one of `Γ`, normalized so that `Γ ⋆ Δu = u` (`compact_C2_newtonian_representation`);
the reproducing property itself is proved in `Harmonic/CompactReproduction`. No mean-value property
is used.
-/
noncomputable section
open Set Metric MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery

/-- Smooth annular kernel: the Laplacian of the truncated fundamental solution, with the same
normalization as `Γ` (so that `Γ ⋆ Δu = u`). -/
def annularKernel (n : ℕ) (ε : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  Laplacian.laplacian (truncatedNewtonianKernel n ε)

theorem contDiff_annularKernel {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (annularKernel n ε) := by
  exact contDiff_laplacian (m := ∞) (contDiff_truncatedNewtonianKernel hn hε) (by
    change (↑(⊤ : ℕ∞) + ↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    exact le_top)

theorem annularKernel_eq_zero_near {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < ε) : annularKernel n ε x = 0 := by
  have heq : truncatedNewtonianKernel n ε =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball 0 ε from by simpa using hx)] with y hy
    have hyr : ‖y‖ < ε := by simpa only [mem_ball, dist_zero_right] using hy
    exact truncatedNewtonianKernel_eq_zero hε y hyr.le
  have h := (laplacian_congr_nhds heq).self_of_nhds
  simpa only [annularKernel, Pi.zero_apply, laplacian_const] using h

theorem annularKernel_eq_zero_far {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin n)) (hx : 2 * ε < ‖x‖) : annularKernel n ε x = 0 := by
  have heq : truncatedNewtonianKernel n ε =ᶠ[𝓝 x] newtonianKernel n := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact truncatedNewtonianKernel_eq_of_far hε y hy.le
  have h := (laplacian_congr_nhds heq).self_of_nhds
  have hx0 : x ≠ 0 := by
    intro he
    rw [he, norm_zero] at hx
    linarith
  exact h.trans (laplacian_newtonianKernel_eq_zero hn x hx0)

theorem tsupport_annularKernel_subset {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    tsupport (annularKernel n ε) ⊆ {x | ε ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * ε} := by
  apply closure_minimal
  · intro x hx
    constructor
    · by_contra h
      exact hx (annularKernel_eq_zero_near hε x (lt_of_not_ge h))
    · by_contra h
      exact hx (annularKernel_eq_zero_far hn hε x (lt_of_not_ge h))
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

theorem hasCompactSupport_annularKernel {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (annularKernel n ε) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * ε)).of_isClosed_subset
    (isClosed_tsupport _)
  intro x hx
  simpa only [mem_closedBall, dist_zero_right] using (tsupport_annularKernel_subset hn hε hx).2

theorem integrable_annularKernel {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    Integrable (annularKernel n ε) volume :=
  (contDiff_annularKernel hn hε).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_annularKernel hn hε)
end FunctionalInequalities.Analysis

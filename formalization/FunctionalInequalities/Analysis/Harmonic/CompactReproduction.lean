import FunctionalInequalities.Analysis.Laplacian.GreenSymmetry
import FunctionalInequalities.Analysis.Harmonic.AnnularKernel
import FunctionalInequalities.Analysis.Newtonian.Potential.Representation

/-!
# Annular reproduction of compactly supported functions harmonic near a point

Supporting the harmonic part of the interior estimates of Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Theorem 4.6, p. 60:

* `compact_harmonic_reproduces`: for `n ≥ 2` (including the planar logarithmic kernel), `ε > 0`, a
  compactly supported `u ∈ C²(ℝⁿ)` and a point `x` such that `Δu = 0` on the ball `‖x - y‖ < 2ε`,
  the integrand `annularKernel n ε (x - ·) * u` is integrable and
  `u x = ∫ annularKernel n ε (x - y) * u y dy`.

The proof starts from the Newtonian representation (4.15) `u x = ∫ Γ(x - y) Δu(y) dy`
(`compact_C2_newtonian_representation`), replaces `Γ` by its truncation (they differ only where
`Δu = 0`), and moves the Laplacian onto the truncated kernel with `integral_mul_laplacian_symm`. No
reproducing formula or mean-value property is assumed.
-/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

/-- A compact C² function whose actual Laplacian vanishes on the ball of radius `2ε` about `x` is
reproduced at `x` by the smooth annular kernel. This includes the planar logarithmic kernel. -/
theorem compact_harmonic_reproduces {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (x : EuclideanSpace ℝ (Fin n))
    (hzero : ∀ y, ‖x - y‖ < 2 * ε → Laplacian.laplacian u y = 0) :
    Integrable (fun y => annularKernel n ε (x - y) * u y) volume ∧
    u x = ∫ y, annularKernel n ε (x - y) * u y := by
  have hg2 : ContDiff ℝ 2 (truncatedNewtonianKernel n ε) :=
    (contDiff_truncatedNewtonianKernel hn hε).of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ 2 (fun y => truncatedNewtonianKernel n ε (x - y)) :=
    hg2.comp (contDiff_const.sub contDiff_id)
  have hLap (y : EuclideanSpace ℝ (Fin n)) :
      Laplacian.laplacian (fun z => truncatedNewtonianKernel n ε (x - z)) y =
        annularKernel n ε (x - y) := by
    simpa [annularKernel, sub_eq_add_neg] using
      (laplacian_affine (truncatedNewtonianKernel n ε) x (-1) y)
  have hpoint (y : EuclideanSpace ℝ (Fin n)) :
      newtonianKernel n (x - y) * Laplacian.laplacian u y =
        truncatedNewtonianKernel n ε (x - y) * Laplacian.laplacian u y := by
    by_cases hy : 2 * ε ≤ ‖x - y‖
    · rw [truncatedNewtonianKernel_eq_of_far hε (x - y) hy]
    · rw [hzero y (lt_of_not_ge hy), mul_zero, mul_zero]
  have hi : Integrable (fun y => annularKernel n ε (x - y) * u y) volume :=
    (((contDiff_annularKernel hn hε).continuous.comp
      (continuous_const.sub continuous_id)).mul hu.continuous).integrable_of_hasCompactSupport hc.mul_left
  refine ⟨hi, ?_⟩
  calc
    u x = ∫ y, newtonianKernel n (x - y) * Laplacian.laplacian u y :=
      (compact_C2_newtonian_representation hn hu hc x).2
    _ = ∫ y, truncatedNewtonianKernel n ε (x - y) * Laplacian.laplacian u y :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∫ y, u y * Laplacian.laplacian
        (fun z => truncatedNewtonianKernel n ε (x - z)) y :=
      integral_mul_laplacian_symm hu hc hg
    _ = ∫ y, annularKernel n ε (x - y) * u y := by
      apply integral_congr_ae (Eventually.of_forall _)
      intro y
      rw [hLap]
      exact mul_comm _ _
end FunctionalInequalities.Analysis

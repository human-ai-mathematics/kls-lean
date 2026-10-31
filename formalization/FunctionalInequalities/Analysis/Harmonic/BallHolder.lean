module

public import FunctionalInequalities.Analysis.Harmonic.LocalHolder
public import Mathlib.Tactic.Abel

/-!
# Scaled Hessian Hölder bounds for harmonic functions on balls

The harmonic part of the interior Hölder estimate of Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Theorem 4.6, p. 60, at
an arbitrary centre and radius, from the derivative estimates of Theorem 2.10 / (2.31):

* `ball_harmonic_hessian_holder`: for `n ≥ 2` there is `C > 0`, chosen before `α, h, c, R, M`, such
  that for every `0 < α < 1`, `R > 0` and `h ∈ C²(B(c, 2R))` with `Δh = 0` and `|h| ≤ M` on
  `B(c, 2R)`, on `B(c, R)`:
  `‖D²h x‖ ≤ C R⁻² M` and `‖D²h x - D²h y‖ ≤ C R^{-(2+α)} M ‖x - y‖^α`.

The proof rescales `z ↦ h (c + R • z)` to the unit statement `local_harmonic_hessian_holder`
(`Harmonic/LocalHolder`), using `laplacian_affine`, `derivative_cap_transfer` and
`norm_hessian_difference_affine` from `IteratedDerivative/Affine`. Only the harmonic contribution
to GT Theorem 4.6 is proved here; the Newtonian-potential estimate is GT Theorem 4.5
(`Newtonian/CompactPoisson`). The constant is not GT's explicit one.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

private theorem norm_iterated_two {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ 2 h x‖ = ‖fderiv ℝ (fderiv ℝ h) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

/-- `R⁻²` point bounds and `R^{-(2+α)}` Hölder Hessian bounds on `B(c, R)` for a `C²` harmonic
function on `B(c, 2R)`. The positive constant is selected before `α, h, c, R, M`. -/
theorem ball_harmonic_hessian_holder {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α < 1 →
      ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ) (c : EuclideanSpace ℝ (Fin n))
        (R : ℝ), 0 < R →
      ContDiffOn ℝ 2 h (ball c (2 * R)) →
      (∀ y ∈ ball c (2 * R), Laplacian.laplacian h y = 0) →
      ∀ (M : ℝ), (∀ y ∈ ball c (2 * R), |h y| ≤ M) →
      (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C * (R⁻¹) ^ 2 * M) ∧
      ∀ x ∈ ball c R, ∀ y ∈ ball c R,
        ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ h) y‖ ≤
          C * (R⁻¹) ^ (2 + α) * M * ‖x - y‖ ^ α := by
  obtain ⟨C, hC, hunit⟩ := local_harmonic_hessian_holder hn
  refine ⟨C, hC, ?_⟩
  intro α hα hα1 h c R hR hh hLap M hb
  let H := fun z : EuclideanSpace ℝ (Fin n) => h (c + R • z)
  have hmaps : MapsTo (fun z : EuclideanSpace ℝ (Fin n) => c + R • z) (ball 0 2)
      (ball c (2 * R)) := by
    intro z hz
    have hz' : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR]
    exact (mul_lt_mul_of_pos_left hz' hR).trans_eq (mul_comm R 2)
  have hH : ContDiffOn ℝ 2 H (ball 0 2) :=
    hh.comp ((contDiff_const.add (contDiff_id.const_smul R)).contDiffOn) hmaps
  have hHLap : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, Laplacian.laplacian H z = 0 := by
    intro z hz
    rw [show Laplacian.laplacian H z = R ^ 2 • Laplacian.laplacian h (c + R • z) from
      laplacian_affine h c R z, hLap _ (hmaps hz), smul_zero]
  have hHb : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 2, |H z| ≤ M :=
    fun z hz => hb _ (hmaps hz)
  have hs := hunit α hα hα1 H hH hHLap M hHb
  have hpoint := derivative_cap_transfer h c hR (ρ := 1) (B := C * M) 2
    (fun z hz => by simpa only [norm_iterated_two] using hs.1 z hz)
  refine ⟨?_, ?_⟩
  · intro x hx
    have hhx : x ∈ ball c (R * 1) := by simpa only [mul_one] using hx
    simpa only [norm_iterated_two, mul_assoc, mul_comm, mul_left_comm] using hpoint x hhx
  · intro x hx y hy
    let z := R⁻¹ • (x - c)
    let w := R⁻¹ • (y - c)
    have hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      inverse_affine_mem_ball c x hR (by simpa only [mul_one] using hx)
    have hw : w ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      inverse_affine_mem_ball c y hR (by simpa only [mul_one] using hy)
    have hcoord (q : EuclideanSpace ℝ (Fin n)) : c + R • (R⁻¹ • (q - c)) = q := by
      rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
    have hnorm : ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ h) y‖ =
        R⁻¹ ^ 2 * ‖fderiv ℝ (fderiv ℝ H) z - fderiv ℝ (fderiv ℝ H) w‖ := by
      have ha := norm_hessian_difference_affine h c R z w
      change ‖fderiv ℝ (fderiv ℝ H) z - fderiv ℝ (fderiv ℝ H) w‖ = _ at ha
      dsimp [z, w] at ha
      rw [hcoord x, hcoord y, abs_of_pos hR] at ha
      rw [ha, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hR.ne', one_pow, one_mul]
    have hdist : ‖z - w‖ = R⁻¹ * ‖x - y‖ := by
      dsimp [z, w]
      rw [← smul_sub, show (x - c) - (y - c) = x - y by abel,
        norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    calc
      ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ h) y‖ =
          R⁻¹ ^ 2 * ‖fderiv ℝ (fderiv ℝ H) z - fderiv ℝ (fderiv ℝ H) w‖ := hnorm
      _ ≤ R⁻¹ ^ 2 * (C * M * ‖z - w‖ ^ α) :=
        mul_le_mul_of_nonneg_left (hs.2 z hz w hw) (sq_nonneg _)
      _ = C * (R⁻¹) ^ (2 + α) * M * ‖x - y‖ ^ α := by
        rw [hdist, Real.mul_rpow (inv_nonneg.mpr hR.le) (norm_nonneg _),
          Real.rpow_add (inv_pos.mpr hR)]
        norm_num only [Real.rpow_ofNat]
        ring
end FunctionalInequalities.Analysis

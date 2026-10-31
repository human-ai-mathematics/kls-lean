module

public import FunctionalInequalities.Analysis.LogRadial.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Normal derivative of the CNS barrier profile at a flat boundary point (CNS1984 Lemma 5.1, p. 386)

At a flat point (`p x = 0`, `q x = 0`) with a positive shift `β`, the radial/log profile
`φ = (√S + (p - β) - ε q log S) / 2`, `S = (p - β)² + q²`, has `S(x) = β² > 0`, so it is `C^∞` there
(the
singular set `S = 0` is away). Its value is `0`, and its derivative in a normal direction `v`
(`p v = 0`, `q v = 1`) is `-ε log β`. This is the profile part of the CNS identity `hₙ(0) = -D - α ε
log β`.

* `flat_log_radial_profile_normal`: for arbitrary real normed `G` and continuous linear functionals
  `p`, `q`, via
  the shared producers `contDiffAt_log_radial_profile_of_pos` and
  `hasFDerivAt_log_radial_profile_of_pos`.
* `tangent_log_radial_profile_normal_at_zero`: in `ℝ^{m+1}`, `p = ⟨ζ, ·⟩` with `ζ` tangent (`ζₙ =
  0`),
  `q` the last coordinate, at `0` in the direction `eₙ`.
-/

@[expose] public section

noncomputable section
open Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- On the flat hyperplane the constructed profile is exactly the positive part,
including its singular set; no positive-radius hypothesis is needed. -/
theorem log_radial_profile_flat_value {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) (β ε : ℝ) {x : G} (hqx : q x = 0) :
    (Real.sqrt ((p x - β) ^ 2 + (q x) ^ 2) + (p x - β) -
          ε * q x * Real.log ((p x - β) ^ 2 + (q x) ^ 2)) /
        2 =
      max (p x - β) 0 := by
  rw [hqx]
  simp only [zero_pow (by decide : 2 ≠ 0), add_zero, mul_zero, zero_mul, sub_zero,
    Real.sqrt_sq_eq_abs]
  rcases le_total 0 (p x - β) with h | h
  · rw [abs_of_nonneg h, max_eq_left h]
    ring
  · rw [abs_of_nonpos h, max_eq_right h]
    ring

theorem flat_log_radial_profile_normal {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) {β : ℝ} (hβ : 0 < β) (ε : ℝ) {x v : G} (hpx : p x = 0) (hqx : q x = 0)
    (hpv : p v = 0) (hqv : q v = 1) :
    let φ : G → ℝ := fun y =>
      (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
          ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) /
        2
    ContDiffAt ℝ ∞ φ x ∧ φ x = 0 ∧ (fderiv ℝ φ x) v = -ε * Real.log β := by
  dsimp only
  have hS2 : (p x - β) ^ 2 + (q x) ^ 2 = β ^ 2 := by
    rw [hpx, hqx]
    ring
  have hS : 0 < (p x - β) ^ 2 + (q x) ^ 2 := by
    rw [hS2]
    exact pow_pos hβ 2
  refine ⟨contDiffAt_log_radial_profile_of_pos p q β ε hS, ?_, ?_⟩
  · simpa only [hpx, zero_sub, max_eq_right (neg_nonpos.mpr hβ.le)] using
      log_radial_profile_flat_value p q β ε hqx
  · rw [(hasFDerivAt_log_radial_profile_of_pos p q β ε hS).fderiv]
    simp [hpx, hqx, hpv, hqv]
    ring

theorem tangent_log_radial_profile_normal_at_zero {m : ℕ}
    (zeta : EuclideanSpace ℝ (Fin (m + 1))) (hztan : zeta (Fin.last m) = 0) {β : ℝ} (hβ : 0 < β)
    (ε : ℝ) :
    let φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun y =>
      (Real.sqrt (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last m)) ^ 2) +
            ((∑ i, zeta i * y i) - β) -
          ε * y (Fin.last m) *
            Real.log (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last m)) ^ 2)) /
        2
    ContDiffAt ℝ ∞ φ 0 ∧
      φ 0 = 0 ∧ (fderiv ℝ φ 0) (EuclideanSpace.single (Fin.last m) 1) = -ε * Real.log β := by
  set p : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ := innerSL ℝ zeta with hpdef
  set q : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last m) with hqdef
  have hpy : ∀ y, p y = ∑ i, zeta i * y i := fun y => by
    simp [hpdef, PiLp.inner_apply, mul_comm]
  have hqy : ∀ y, q y = y (Fin.last m) := fun _ => rfl
  have hpv : p (EuclideanSpace.single (Fin.last m) 1) = 0 := by
    rw [hpy]
    simp [hztan]
  have hqv : q (EuclideanSpace.single (Fin.last m) 1) = 1 := by simp [hqdef]
  have h :=
    flat_log_radial_profile_normal p q hβ ε (x := 0) (v := EuclideanSpace.single (Fin.last m) 1)
      (by simp) (by simp) hpv hqv
  simp only [hpy, hqy] at h
  exact h

end FunctionalInequalities.Analysis

end

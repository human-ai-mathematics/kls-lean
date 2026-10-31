module

public import FunctionalInequalities.Analysis.OrthonormalPair
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual radius of the tangent-normal barrier profile

For CNS1984 Lemma5.1 p386, the unit tangent and the last normal generate
Bessel control and hence the shifted two-coordinate radius bound. No
independent coordinate coupling or radius bound is assumed. Ambient m+2>=2.
-/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace
namespace FunctionalInequalities.Analysis

/-- The actual shifted planar radius is bounded by ambient norm plus shift. -/
theorem tangent_normal_radius_le {m : ℕ} (zeta : EuclideanSpace ℝ (Fin (m + 2)))
    (hznorm : ‖zeta‖ = 1) (hztan : zeta (Fin.last (m + 1)) = 0) (β : ℝ)
    (x : EuclideanSpace ℝ (Fin (m + 2))) :
    Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2) ≤ ‖x‖ + |β| := by
  let e : EuclideanSpace ℝ (Fin (m + 2)) := EuclideanSpace.single (Fin.last (m + 1)) 1
  have he : ‖e‖ = 1 := by simp [e]
  have horth : ⟪zeta, e⟫ = 0 := by
    dsimp only [e]
    rw [EuclideanSpace.inner_single_right]
    simp [hztan]
  have hp : ⟪zeta, x⟫ = ∑ i, zeta i * x i := by simp [PiLp.inner_apply, mul_comm]
  have hq : ⟪e, x⟫ = x (Fin.last (m + 1)) := by
    dsimp only [e]
    rw [EuclideanSpace.inner_single_left]
    simp
  have hb := orthogonal_pair_inner_sq_le hznorm he horth x
  rw [hp, hq] at hb
  let y : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(∑ i, zeta i * x i), x (Fin.last (m + 1))]
  let b : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 β
  have hny : ‖y‖ ^ 2 = (∑ i, zeta i * x i) ^ 2 + (x (Fin.last (m + 1))) ^ 2 := by
    simp [y, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hynorm : ‖y‖ ≤ ‖x‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
  have hnb : ‖b‖ = |β| := by simp [b]
  have hr : Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2) = ‖y - b‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (y - b))]
    congr 1
    simp [y, b, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [hr]
  exact (norm_sub_le y b).trans (add_le_add hynorm hnb.le)

end FunctionalInequalities.Analysis

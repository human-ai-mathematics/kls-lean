module

public import FunctionalInequalities.Analysis.LogRadial.Gradient

/-!
# Clients of the barrier profile first derivative bound

* `scalar_profile_gradient_client`: on `ℝ` with `p = 0`, `q = id`, `β = 0`, `ε = 1` at `x = 1`, the
  profile is
  `(√(y²) - y log y²) / 2` and the generic bound gives `‖DΦ(1)‖ ≤ 4`. The first-derivative producer
  gives the
  actual derivative of the log piece `-y log y²` at `1`: `-2 • id`.
* `off_axis_gradient_client`: ambient `ℝ²` (`m = 1`), `ζ = e₀`, `β = 0`, `x = (1, 1)`, `ε = 1/24`:
  the ambient
  bound `2 + (|log 2| + 2)/24`.
* `ambient_line_gradient_client`: ambient `ℝ¹` (`m = 0`), `ζ = 0`, `β = 0`, `ε = 1`, `x = (1)`: the
  ambient bound `4`.
-/

@[expose] public section

noncomputable section
open Filter
open scoped Topology

namespace FunctionalInequalities.Analysis.LogRadialGradientClient

open FunctionalInequalities.Analysis

/-- **Scalar profile at `1`.** -/
theorem scalar_profile_gradient_client :
    ‖fderiv ℝ (fun y : ℝ => (Real.sqrt (y ^ 2) - y * Real.log (y ^ 2)) / 2) 1‖ ≤ 4 ∧
      HasFDerivAt (fun y : ℝ => -y * Real.log (y ^ 2)) ((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
        1 := by
  have hq1 : (0 : ℝ) < (ContinuousLinearMap.id ℝ ℝ) 1 := by simp
  have h :=
    fderiv_log_radial_profile_norm_le (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) (by simp)
      ContinuousLinearMap.norm_id_le 0 1 zero_le_one hq1
  have hfun :
    (fun y : ℝ =>
        (Real.sqrt (((0 : ℝ →L[ℝ] ℝ) y - 0) ^ 2 + ((ContinuousLinearMap.id ℝ ℝ) y) ^ 2) +
              ((0 : ℝ →L[ℝ] ℝ) y - 0) -
            1 * (ContinuousLinearMap.id ℝ ℝ) y *
              Real.log (((0 : ℝ →L[ℝ] ℝ) y - 0) ^ 2 + ((ContinuousLinearMap.id ℝ ℝ) y) ^ 2)) /
          2) =
      fun y : ℝ => (Real.sqrt (y ^ 2) - y * Real.log (y ^ 2)) / 2 := by
    funext y
    simp
  rw [hfun] at h
  refine ⟨h.trans (le_of_eq (by norm_num)), ?_⟩
  obtain ⟨hL, -⟩ :=
    (hasFDerivAt_log_radial_barrier (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) 0
        hq1).self_of_nhds
  have hLfun :
    (fun y : ℝ =>
        -((ContinuousLinearMap.id ℝ ℝ) y) *
          Real.log (((0 : ℝ →L[ℝ] ℝ) y - 0) ^ 2 + ((ContinuousLinearMap.id ℝ ℝ) y) ^ 2)) =
      fun y : ℝ => -y * Real.log (y ^ 2) := by
    funext y
    simp
  rw [hLfun] at hL
  refine hL.congr_fderiv ?_
  ext
  simp

/-- **Ambient `ℝ²`, tangent `e₀`, off-axis point `(1, 1)`.** -/
theorem off_axis_gradient_client :
    ‖fderiv ℝ
          (fun y : EuclideanSpace ℝ (Fin 2) =>
            (Real.sqrt
                    (((∑ i, (WithLp.toLp 2 ![(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) i * y i) -
                          0) ^
                        2 +
                      (y 1) ^ 2) +
                  ((∑ i, (WithLp.toLp 2 ![(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) i * y i) -
                    0) -
                1 / 24 * y 1 *
                  Real.log
                    (((∑ i, (WithLp.toLp 2 ![(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) i * y i) -
                          0) ^
                        2 +
                      (y 1) ^ 2)) /
              2)
          (WithLp.toLp 2 ![1, 1])‖ ≤
      2 + 1 / 24 * (|Real.log 2| + 2) := by
  have hz : ‖(WithLp.toLp 2 ![(1 : ℝ), 0] : EuclideanSpace ℝ (Fin (1 + 1)))‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two]
  have hx : 0 < (WithLp.toLp 2 ![(1 : ℝ), 1] : EuclideanSpace ℝ (Fin (1 + 1))) (Fin.last 1) := by
    simp
  have h :=
    tangent_normal_log_radial_profile_fderiv_norm_le (m := 1) (WithLp.toLp 2 ![(1 : ℝ), 0]) hz 0
      (1 / 24) (by norm_num) hx
  have e :
    ((∑ i,
              (WithLp.toLp 2 ![(1 : ℝ), 0] : EuclideanSpace ℝ (Fin (1 + 1))) i *
                (WithLp.toLp 2 ![(1 : ℝ), 1] : EuclideanSpace ℝ (Fin (1 + 1))) i) -
            0) ^
          2 +
        ((WithLp.toLp 2 ![(1 : ℝ), 1] : EuclideanSpace ℝ (Fin (1 + 1))) (Fin.last 1)) ^ 2 =
      2 := by
    simp [Fin.sum_univ_two]
    norm_num
  rw [e] at h
  exact h

/-- **Ambient `ℝ¹`, `ζ = 0`, point `(1)`.** -/
theorem ambient_line_gradient_client :
    ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 1) =>
      (Real.sqrt (((∑ i, (0 : EuclideanSpace ℝ (Fin 1)) i * y i) - 0) ^ 2 + (y 0) ^ 2) +
        ((∑ i, (0 : EuclideanSpace ℝ (Fin 1)) i * y i) - 0) - 1 * y 0 *
          Real.log (((∑ i, (0 : EuclideanSpace ℝ (Fin 1)) i * y i) - 0) ^ 2 + (y 0) ^ 2)) / 2)
      (WithLp.toLp 2 ![1])‖ ≤ 4 := by
  have hx : 0 < (WithLp.toLp 2 ![(1 : ℝ)] : EuclideanSpace ℝ (Fin (0 + 1))) (Fin.last 0) := by simp
  have h := tangent_normal_log_radial_profile_fderiv_norm_le (m := 0)
    (0 : EuclideanSpace ℝ (Fin (0 + 1))) (by simp) 0 1 zero_le_one hx
  have e : ((∑ i, (0 : EuclideanSpace ℝ (Fin (0 + 1))) i *
      (WithLp.toLp 2 ![(1 : ℝ)] : EuclideanSpace ℝ (Fin (0 + 1))) i) - 0) ^ 2 +
      ((WithLp.toLp 2 ![(1 : ℝ)] : EuclideanSpace ℝ (Fin (0 + 1))) (Fin.last 0)) ^ 2 = 1 := by
    simp
  rw [e, Real.log_one] at h
  exact h.trans (le_of_eq (by norm_num))

end FunctionalInequalities.Analysis.LogRadialGradientClient

#print axioms FunctionalInequalities.Analysis.LogRadialGradientClient.scalar_profile_gradient_client
#print axioms FunctionalInequalities.Analysis.LogRadialGradientClient.off_axis_gradient_client
#print axioms FunctionalInequalities.Analysis.LogRadialGradientClient.ambient_line_gradient_client

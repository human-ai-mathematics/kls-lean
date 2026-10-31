module

public import FunctionalInequalities.Analysis.LogRadial.Boundary

/-!
# Clients of the flat-point profile normal derivative

* `scalar_flat_normal_client`: on `ℝ` with `p = 0`, `q = id`, `β = 2`, `ε = 1`, at `x = 0` in
  direction `v = 1`:
  the profile is smooth at `0`, vanishes there, and its normal derivative is `-log 2`.
* `ambient_line_flat_normal_client`: ambient `ℝ¹` (`m = 0`), `ζ = 0`, `β = 2`, `ε = 1`.
* `tangent_plane_flat_normal_client`: ambient `ℝ²` (`m = 1`), the tangent `ζ = e₀`, `β = 3`, `ε =
  1/24`:
  normal derivative `-(1/24) log 3`.
* `fin_zero_first_derivative_client`: on the one-point space `ℝ⁰` with `p = q = 0` and `β = 1`, `S =
  1 > 0`, so the
  generic first-derivative producer applies at every point. There is no normal direction in `ℝ⁰`, so
  no
  normal-derivative claim is made there.
-/

@[expose] public section

noncomputable section
open Filter
open scoped Topology ContDiff

namespace FunctionalInequalities.Analysis.FlatBarrierNormalClient

open FunctionalInequalities.Analysis

/-- **Scalar profile at `0`, shift `2`.** -/
theorem scalar_flat_normal_client :
    let φ : ℝ → ℝ := fun y =>
      (Real.sqrt (((0 : ℝ →L[ℝ] ℝ) y - 2) ^ 2 + ((ContinuousLinearMap.id ℝ ℝ) y) ^ 2) +
            ((0 : ℝ →L[ℝ] ℝ) y - 2) -
          1 * (ContinuousLinearMap.id ℝ ℝ) y *
            Real.log (((0 : ℝ →L[ℝ] ℝ) y - 2) ^ 2 + ((ContinuousLinearMap.id ℝ ℝ) y) ^ 2)) /
        2
    ContDiffAt ℝ ∞ φ 0 ∧ φ 0 = 0 ∧ (fderiv ℝ φ 0) 1 = -Real.log 2 := by
  have h :=
    flat_log_radial_profile_normal (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) (β := 2)
      (by norm_num) 1 (x := 0) (v := 1) (by simp) (by simp) (by simp) (by simp)
  intro φ
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2]
  ring

/-- **Ambient `ℝ¹`, `ζ = 0`.** -/
theorem ambient_line_flat_normal_client :
    let φ : EuclideanSpace ℝ (Fin (0 + 1)) → ℝ := fun y =>
      (Real.sqrt
              (((∑ i, (0 : EuclideanSpace ℝ (Fin (0 + 1))) i * y i) - 2) ^ 2 +
                (y (Fin.last 0)) ^ 2) +
            ((∑ i, (0 : EuclideanSpace ℝ (Fin (0 + 1))) i * y i) - 2) -
          1 * y (Fin.last 0) *
            Real.log
              (((∑ i, (0 : EuclideanSpace ℝ (Fin (0 + 1))) i * y i) - 2) ^ 2 +
                (y (Fin.last 0)) ^ 2)) /
        2
    ContDiffAt ℝ ∞ φ 0 ∧
      φ 0 = 0 ∧ (fderiv ℝ φ 0) (EuclideanSpace.single (Fin.last 0) 1) = -1 * Real.log 2 :=
  tangent_log_radial_profile_normal_at_zero (m := 0) 0 (by simp) (by norm_num) 1

/-- **Ambient `ℝ²`, tangent `ζ = e₀`, shift `3`.** -/
theorem tangent_plane_flat_normal_client :
    let zeta : EuclideanSpace ℝ (Fin (1 + 1)) := WithLp.toLp 2 ![1, 0]
    let φ : EuclideanSpace ℝ (Fin (1 + 1)) → ℝ := fun y =>
      (Real.sqrt (((∑ i, zeta i * y i) - 3) ^ 2 + (y (Fin.last 1)) ^ 2) +
            ((∑ i, zeta i * y i) - 3) -
          1 / 24 * y (Fin.last 1) *
            Real.log (((∑ i, zeta i * y i) - 3) ^ 2 + (y (Fin.last 1)) ^ 2)) /
        2
    ContDiffAt ℝ ∞ φ 0 ∧
      φ 0 = 0 ∧
        (fderiv ℝ φ 0) (EuclideanSpace.single (Fin.last 1) 1) = -(1 / 24) * Real.log 3 := by
  intro zeta
  have hztan : zeta (Fin.last 1) = 0 := by simp [zeta]
  exact tangent_log_radial_profile_normal_at_zero (m := 1) zeta hztan (by norm_num) (1 / 24)

/--
**The one-point space `ℝ⁰`**, `p = q = 0`, `β = 1`: the first-derivative producer applies (`S = 1 >
0`). -/
theorem fin_zero_first_derivative_client (x : EuclideanSpace ℝ (Fin 0)) :
    ∀ᶠ y in 𝓝 x,
      HasFDerivAt
          (fun y : EuclideanSpace ℝ (Fin 0) =>
            -((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) *
              Real.log
                (((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y - 1) ^ 2 +
                  ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) ^ 2))
          ((-((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y)) •
              ((((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y - 1) ^ 2 +
                    ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) ^ 2)⁻¹ •
                ((2 * ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y - 1)) •
                    (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) +
                  (2 * (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) •
                    (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ))) +
            Real.log
                (((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y - 1) ^ 2 +
                  ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) ^ 2) •
              (-(0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ)))
          y ∧
        HasFDerivAt
          (fun y : EuclideanSpace ℝ (Fin 0) =>
            Real.sqrt
              (((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y - 1) ^ 2 +
                ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) ^ 2))
          ((1 /
              (2 *
                Real.sqrt
                  (((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y - 1) ^ 2 +
                    ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) ^ 2))) •
            ((2 * ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y - 1)) •
                (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) +
              (2 * (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) •
                (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ)))
          y :=
  hasFDerivAt_log_radial_barrier_of_pos 0 0 1 (by norm_num)

end FunctionalInequalities.Analysis.FlatBarrierNormalClient

#print axioms FunctionalInequalities.Analysis.FlatBarrierNormalClient.scalar_flat_normal_client
#print axioms
  FunctionalInequalities.Analysis.FlatBarrierNormalClient.ambient_line_flat_normal_client
#print axioms
  FunctionalInequalities.Analysis.FlatBarrierNormalClient.tangent_plane_flat_normal_client
#print axioms
  FunctionalInequalities.Analysis.FlatBarrierNormalClient.fin_zero_first_derivative_client

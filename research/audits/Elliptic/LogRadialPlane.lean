module

public import FunctionalInequalities.Analysis.LogRadial.Operator
public import examples.EllipticDrift

/-!
# Clients of the two-plane barrier operator margin

Both clients use the skew family `A = [[1, k], [-k, 1]]` with an ARBITRARY real `k`. It is not
symmetric for
`k ≠ 0`, but its quadratic form is exactly `‖v‖²`, so `ℓ = Λ = 1`. They use `ε = 1/24`, and the main
theorem is
applied:

* `skew_off_axis_client`: `β = 0` at the off-axis point `x = (1, 1)`, with margin `1 / (4 √2)`.
* `skew_shifted_axis_client`: `β = 1` at `x = (1, 2)`, the point directly above the shifted axis (`s
  = 0`), with
  margin `1 / 8`.
-/

@[expose] public section

noncomputable section
open scoped ContDiff

namespace FunctionalInequalities.Analysis.PlaneBarrierOperatorClient

open FunctionalInequalities.Analysis

/-- The skew coefficient has quadratic form `‖v‖²`. -/
private lemma skew_quadratic (k : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (∑ i, ∑ j, (!![1, k; -k, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j * v i * v j) = ‖v‖ ^ 2 := by
  simpa only [CNSCoefficientScopeAudit.coefficient] using
    CNSCoefficientScopeAudit.quadratic_identity k v


private lemma skew_bounds (k : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    1 * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, (!![1, k; -k, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j * v i * v j) ∧
      (∑ i, ∑ j, (!![1, k; -k, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j * v i * v j) ≤ 1 * ‖v‖ ^ 2 := by
  rw [skew_quadratic, one_mul]
  exact ⟨le_rfl, le_rfl⟩

/-- **Off-axis point `(1, 1)`, `β = 0`, arbitrary skew `k`.** -/
theorem skew_off_axis_client (k : ℝ) :
    let φ : EuclideanSpace ℝ (Fin 2) → ℝ := fun y =>
      (Real.sqrt ((y 0 - 0) ^ 2 + (y 1) ^ 2) + (y 0 - 0) -
        1 / 24 * y 1 * Real.log ((y 0 - 0) ^ 2 + (y 1) ^ 2)) / 2
    ContDiffAt ℝ ∞ φ (WithLp.toLp 2 ![1, 1]) ∧
      1 / (4 * Real.sqrt 2) ≤
        Matrix.trace ((!![1, k; -k, 1] : Matrix (Fin 2) (Fin 2) ℝ) *
          ((Matrix.of fun i j => fderiv ℝ (fderiv ℝ φ) (WithLp.toLp 2 ![1, 1])
            (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) :
            Matrix (Fin 2) (Fin 2) ℝ)) := by
  intro φ
  have h := plane_log_radial_barrier_trace_lower (!![1, k; -k, 1] : Matrix (Fin 2) (Fin 2) ℝ)
    (ell := 1) (Λ := 1) (ε := 1 / 24) one_pos one_pos (by norm_num) (by norm_num) (skew_bounds k) 0
    (x := WithLp.toLp 2 ![1, 1]) (by simp)
  have e : ((WithLp.toLp 2 ![(1 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) 0 - 0) ^ 2 +
      ((WithLp.toLp 2 ![(1 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) 1) ^ 2 = 2 := by
    simp
    norm_num
  refine ⟨h.1, ?_⟩
  calc 1 / (4 * Real.sqrt 2)
      = 1 / (4 * Real.sqrt (((WithLp.toLp 2 ![(1 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) 0 - 0) ^ 2 +
          ((WithLp.toLp 2 ![(1 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) 1) ^ 2)) := by rw [e]
    _ ≤ _ := h.2

/-- **Shifted axis `β = 1`, point `(1, 2)` above it, arbitrary skew `k`.** -/
theorem skew_shifted_axis_client (k : ℝ) :
    let φ : EuclideanSpace ℝ (Fin 2) → ℝ := fun y =>
      (Real.sqrt ((y 0 - 1) ^ 2 + (y 1) ^ 2) + (y 0 - 1) -
          1 / 24 * y 1 * Real.log ((y 0 - 1) ^ 2 + (y 1) ^ 2)) /
        2
    ContDiffAt ℝ ∞ φ (WithLp.toLp 2 ![1, 2]) ∧
      1 / 8 ≤
        Matrix.trace
          ((!![1, k; -k, 1] : Matrix (Fin 2) (Fin 2) ℝ) *
            ((Matrix.of fun i j =>
                fderiv ℝ (fderiv ℝ φ) (WithLp.toLp 2 ![1, 2]) (EuclideanSpace.single i (1 : ℝ))
                  (EuclideanSpace.single j (1 : ℝ))) :
              Matrix (Fin 2) (Fin 2) ℝ)) := by
  intro φ
  have h :=
    plane_log_radial_barrier_trace_lower (!![1, k; -k, 1] : Matrix (Fin 2) (Fin 2) ℝ) (ell := 1)
      (Λ := 1) (ε := 1 / 24) one_pos one_pos (by norm_num) (by norm_num) (skew_bounds k) 1 (x :=
      WithLp.toLp 2 ![1, 2]) (by simp)
  have e :
    1 /
        (4 *
          Real.sqrt
            (((WithLp.toLp 2 ![(1 : ℝ), 2] : EuclideanSpace ℝ (Fin 2)) 0 - 1) ^ 2 +
              ((WithLp.toLp 2 ![(1 : ℝ), 2] : EuclideanSpace ℝ (Fin 2)) 1) ^ 2)) =
      1 / 8 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp
    norm_num [h4]
  refine ⟨h.1, ?_⟩
  rw [← e]
  exact h.2

end FunctionalInequalities.Analysis.PlaneBarrierOperatorClient

#print axioms FunctionalInequalities.Analysis.PlaneBarrierOperatorClient.skew_off_axis_client
#print axioms FunctionalInequalities.Analysis.PlaneBarrierOperatorClient.skew_shifted_axis_client

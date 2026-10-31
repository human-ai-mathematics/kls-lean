module

public import FunctionalInequalities.Analysis.LogRadial.Bounds
public import FunctionalInequalities.Analysis.LogRadial.Boundary
public import FunctionalInequalities.Analysis.Elliptic.Barrier

@[expose] public section

noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities.Analysis.BarrierValuesAudit

lemma actual_nonzero_profile_value :
    0 ≤ ((1 / 2 : ℝ) + 3 / 10 - (1 / 4) * (4 / 10) * Real.log ((1 / 2 : ℝ) ^ 2)) / 2 ∧
      ((1 / 2 : ℝ) + 3 / 10 - (1 / 4) * (4 / 10) * Real.log ((1 / 2 : ℝ) ^ 2)) / 2 ≤ 3 / 4 := by
  have h :=
    log_radial_profile_value_bounds (s := (3 / 10 : ℝ)) (y := (4 / 10 : ℝ)) (r := (1 / 2 : ℝ))
      (ε := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hu :=
    log_radial_profile_value_le_radius_add (s := (3 / 10 : ℝ)) (y := (4 / 10 : ℝ)) (r :=
      (1 / 2 : ℝ)) (ε := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  exact ⟨h.1, by norm_num at hu ⊢; exact hu⟩

lemma true_fin_zero_flat_value (x : EuclideanSpace ℝ (Fin 0)) :
    (Real.sqrt
              (((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) x - 2) ^ 2 +
                ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) x) ^ 2) +
            ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) x - 2) -
          7 * (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) x *
            Real.log
              (((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) x - 2) ^ 2 +
                ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) x) ^ 2)) /
        2 =
      0 := by
  calc
    _ = max ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) x - 2) 0 :=
      log_radial_profile_flat_value (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) 0 2 7 (x := x)
        (by simp)
    _ = 0 := by norm_num

lemma actual_curved_line :
    (1 / 4 : ℝ) ^ 2 ≤ (1 / 4 : ℝ) + (1 / 4 : ℝ) ^ 2 - (1 + 1) * (1 / 4 : ℝ) ^ 2 := by
  let x : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (1 / 4 : ℝ)
  have hn : ‖x‖ = (1 / 4 : ℝ) := by simp [x]
  have h :=
    halfball_polynomial_curved_lower (m := 0) (E := (1 : ℝ)) (δ := (1 / 4 : ℝ)) (by norm_num)
      (by norm_num) x hn (by norm_num [x])
  simpa [x] using h

lemma actual_curved_plane : (1 / 4 : ℝ) ^ 2 ≤ 73 / 400 := by
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(3 / 20 : ℝ), 1 / 5]
  have hn2 : ‖x‖ ^ 2 = (1 / 4 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [x, Fin.sum_univ_two]
  have hn : ‖x‖ = (1 / 4 : ℝ) := by nlinarith [norm_nonneg x]
  have h :=
    halfball_polynomial_curved_lower (m := 1) (E := (1 : ℝ)) (δ := (1 / 4 : ℝ)) (by norm_num)
      (by norm_num) x hn (by norm_num [x, Fin.last])
  calc
    (1 / 4 : ℝ) ^ 2 ≤ x (Fin.last 1) + ‖x‖ ^ 2 - (1 + 1) * (x (Fin.last 1)) ^ 2 := h
    _ = 73 / 400 := by norm_num [x, hn, Fin.last]

end FunctionalInequalities.Analysis.BarrierValuesAudit
#print axioms FunctionalInequalities.Analysis.BarrierValuesAudit.actual_nonzero_profile_value
#print axioms FunctionalInequalities.Analysis.BarrierValuesAudit.true_fin_zero_flat_value
#print axioms FunctionalInequalities.Analysis.BarrierValuesAudit.actual_curved_line

#print axioms FunctionalInequalities.Analysis.BarrierValuesAudit.actual_curved_plane

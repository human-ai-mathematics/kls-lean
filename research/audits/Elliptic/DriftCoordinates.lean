module

public import FunctionalInequalities.Analysis.EuclideanCoordinates
@[expose] public section

noncomputable section
namespace FunctionalInequalities.Analysis.DriftCoordinatesAudit
lemma actual_arbitrary_codomain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] F) :
    L (WithLp.toLp 2 ![(3 : ℝ), -4]) =
      (3 : ℝ) • L (EuclideanSpace.single 0 1) + (-4 : ℝ) • L (EuclideanSpace.single 1 1) := by
  simpa [Fin.sum_univ_two] using clm_apply_eq_sum_single L (WithLp.toLp 2 ![(3 : ℝ), -4])
lemma actual_nonzero_drift_bound :
    ‖(WithLp.toLp 2 ![(3 : ℝ), -4] : EuclideanSpace ℝ (Fin 2))‖ ≤ 8 := by
  have h :=
    norm_le_card_mul_of_coord_bound (WithLp.toLp 2 ![(3 : ℝ), -4]) 4
      (fun i => by fin_cases i <;> norm_num)
  norm_num at h ⊢
  exact h
lemma true_empty_coordinates {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin 0) →L[ℝ] F) (x : EuclideanSpace ℝ (Fin 0)) (M : ℝ) :
    L x = 0 ∧ ‖x‖ ≤ 0 * M := by
  have he := clm_apply_eq_sum_single L x
  have hn := norm_le_card_mul_of_coord_bound x M (fun i => Fin.elim0 i)
  exact ⟨by simpa using he, by simpa using hn⟩
end FunctionalInequalities.Analysis.DriftCoordinatesAudit
#print axioms FunctionalInequalities.Analysis.DriftCoordinatesAudit.actual_arbitrary_codomain
#print axioms FunctionalInequalities.Analysis.DriftCoordinatesAudit.actual_nonzero_drift_bound
#print axioms FunctionalInequalities.Analysis.DriftCoordinatesAudit.true_empty_coordinates

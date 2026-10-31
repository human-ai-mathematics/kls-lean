module

public import FunctionalInequalities.Analysis.Convex.Section.Growth

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace LetwinSectionVolumeBoundaryAudit
open FunctionalInequalities.Analysis

/-- The zero-dimensional boundary is admitted, without a hidden n>0 premise. -/
theorem zero_dimensional_section {A : ℝ} (hA : 1 ≤ A) {h : ℝ} :
    (volume : Measure (EuclideanSpace ℝ (Fin 0))) {_z | (0 : ℝ) < A * h} ≤
      (volume : Measure (EuclideanSpace ℝ (Fin 0))) {_z | (0 : ℝ) < h} := by
  have hh := section_volume_mul_le (n := 0) (u := fun _ => (0 : ℝ))
    (convexOn_const (0 : ℝ) convex_univ) 0 0 (h := h) hA
  simpa using hh

/-- Flat positive-height sections have infinite volume; the ENNReal statement
handles this case without a hidden finite-volume or cancellation premise. -/
theorem unbounded_flat_section {A : ℝ} (hA : 1 ≤ A) :
    (volume : Measure (EuclideanSpace ℝ (Fin 1))) {_z | (0 : ℝ) < A} = ⊤ ∧
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) {_z | (0 : ℝ) < A} ≤
        ENNReal.ofReal A * (volume : Measure (EuclideanSpace ℝ (Fin 1))) Set.univ := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  constructor
  · simp only [hAp, Set.ofPred_true]
    exact measure_univ_of_isAddLeftInvariant volume
  · have hh := section_volume_mul_le (n := 1) (u := fun _ => (0 : ℝ))
      (convexOn_const (0 : ℝ) convex_univ) 0 0 (h := 1) hA
    simpa using hh
end LetwinSectionVolumeBoundaryAudit
#print axioms FunctionalInequalities.Analysis.section_volume_mul_le
#print axioms LetwinSectionVolumeBoundaryAudit.zero_dimensional_section
#print axioms LetwinSectionVolumeBoundaryAudit.unbounded_flat_section

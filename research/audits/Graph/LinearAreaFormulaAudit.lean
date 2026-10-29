import FunctionalInequalities.Analysis.Vector.LinearAreaFormula
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the normalized linear area formula and affine fibres

Step one of the codimension-`m` coarea program.  Checked here: the linear area formula survives the
change from Mathlib's raw `μH` to this repository's `KLS.hausdorffNormalized` with the norm
determinant as the **exact** volume factor; a linear isometric embedding has unit factor; and a
translated, isometrically embedded slice carries **exactly** Lebesgue measure on its parameter
space, with no residual normalization constant.

The last statement is the fibre bookkeeping of the codimension-`m` formula: its right-hand integral
runs over translates of `ker L`, whose dimension is `n - m` when `L` is surjective, and this client
records that dimension count too.

**No coarea formula and no `C¹` area formula are proved**, here or in the audited module.
-/

noncomputable section

open Set MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal

namespace LinearAreaFormulaAudit

variable {H V W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ V] in
/-- The normalized linear area formula, restated. -/
theorem area_formula (L : H →ₗ[ℝ] V) (s : Set H) :
    hausdorffNormalized V (Module.finrank ℝ H) (L '' s)
      = ENNReal.ofReal (LinearMap.normDet L) * hausdorffNormalized H (Module.finrank ℝ H) s :=
  hausdorffNormalized_image_linearMap L s

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V] in
/-- Isometric embeddings have unit volume factor. -/
theorem isometry_factor_one (ι : H →ₗᵢ[ℝ] V) : LinearMap.normDet (ι : H →ₗ[ℝ] V) = 1 :=
  normDet_linearIsometry ι

/-- **The fibre statement**: a translated isometric slice carries exactly Lebesgue measure, with no
leftover constant on either side. -/
theorem affine_slice_is_lebesgue (x₀ : V) (ι : H →ₗᵢ[ℝ] V) (s : Set H) :
    hausdorffNormalized V (Module.finrank ℝ H) ((fun y => x₀ + ι y) '' s)
      = (volume : Measure H) s :=
  hausdorffNormalized_image_affine x₀ ι s

/-- The same for the fibres of a linear map, which are translates of its kernel. -/
theorem fiber_is_lebesgue (L : V →ₗ[ℝ] W) (x₀ : V) (s : Set (LinearMap.ker L)) :
    hausdorffNormalized V (Module.finrank ℝ (LinearMap.ker L))
        ((fun y : LinearMap.ker L => x₀ + (y : V)) '' s)
      = (volume : Measure (LinearMap.ker L)) s :=
  hausdorffNormalized_fiber L x₀ s

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W] in
/-- **The fibre dimension is the codimension**: for a surjective map the kernel has dimension
`n - m`, so the measure used above is the one the codimension-`m` coarea formula calls for. -/
theorem fiber_dimension (L : V →ₗ[ℝ] W) (hL : Function.Surjective L) :
    Module.finrank ℝ (LinearMap.ker L) = Module.finrank ℝ V - Module.finrank ℝ W := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.2 hL, finrank_top] at h
  omega

/-! ### Boundary cases -/

/-- Top dimension: the identity recovers the already proved normalized/volume identity, so the new
formula is consistent with the existing normalization. -/
theorem top_dimension (s : Set V) :
    hausdorffNormalized V (Module.finrank ℝ V) ((LinearMap.id : V →ₗ[ℝ] V) '' s)
      = (volume : Measure V) s := by
  rw [area_formula, LinearMap.normDet_id, ENNReal.ofReal_one, one_mul,
    hausdorffNormalized_finrank_eq_volume]

/-- No positive-dimension hypothesis is hidden: a zero-dimensional parameter space is inside the
statement. -/
theorem zero_dimensional_slice (x₀ : V) (ι : EuclideanSpace ℝ (Fin 0) →ₗᵢ[ℝ] V)
    (s : Set (EuclideanSpace ℝ (Fin 0))) :
    hausdorffNormalized V (Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)))
        ((fun y => x₀ + ι y) '' s)
      = (volume : Measure (EuclideanSpace ℝ (Fin 0))) s :=
  affine_slice_is_lebesgue x₀ ι s

omit [FiniteDimensional ℝ V] in
/-- A degenerate map collapses positive-dimensional volume: the factor is `0`. -/
theorem degenerate_map [Nontrivial H] (s : Set H) :
    hausdorffNormalized V (Module.finrank ℝ H) ((0 : H →ₗ[ℝ] V) '' s)
      = ENNReal.ofReal (LinearMap.normDet (0 : H →ₗ[ℝ] V))
          * hausdorffNormalized H (Module.finrank ℝ H) s :=
  area_formula 0 s

end LinearAreaFormulaAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.KLS.hausdorffNormalized_image_linearMap
#print axioms FunctionalInequalities.KLS.adjoint_apply_linearIsometry
#print axioms FunctionalInequalities.KLS.normDet_linearIsometry
#print axioms FunctionalInequalities.KLS.hausdorffNormalized_image_linearIsometry
#print axioms FunctionalInequalities.KLS.hausdorffNormalized_image_affine
#print axioms FunctionalInequalities.KLS.hausdorffNormalized_fiber
#print axioms LinearAreaFormulaAudit.area_formula
#print axioms LinearAreaFormulaAudit.isometry_factor_one
#print axioms LinearAreaFormulaAudit.affine_slice_is_lebesgue
#print axioms LinearAreaFormulaAudit.fiber_is_lebesgue
#print axioms LinearAreaFormulaAudit.fiber_dimension
#print axioms LinearAreaFormulaAudit.top_dimension
#print axioms LinearAreaFormulaAudit.zero_dimensional_slice
#print axioms LinearAreaFormulaAudit.degenerate_map

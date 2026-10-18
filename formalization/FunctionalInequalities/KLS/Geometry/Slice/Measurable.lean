import FunctionalInequalities.Analysis.Hausdorff.SurfaceSlicing

/-! # Measurability of weighted level-set integrals

`Analysis.aemeasurable_lintegral_levelSet` is the full-space specialization of
`KLS.aemeasurable_setLIntegral_inter_levelSet`. Its statement retains `CompleteSpace V`.
The proof uses the measurable Eilenberg majorant, null slicing, compact-slice measurability
and the Borel-slice version in `Analysis/Hausdorff/SurfaceSlicing.lean` and
`Analysis/Hausdorff/Content.lean`. It needs no SFinite hypothesis on the codimension-one
surface measure, which is not SFinite in positive ambient dimension.

This module supplies measurability. The coarea equality is in
`KLS/Geometry/Coarea/Lipschitz.lean`; `KLS/Geometry/Coarea/LocallyLipschitz.lean` extends
both conclusions to locally Lipschitz functions. Sharp Sard is in `Analysis/Sard/Sharp.lean`. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace FunctionalInequalities

universe u

namespace Analysis

section Coarea

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

-- The section variables are kept so that the published interface is unchanged; the proof needs
-- neither completeness nor, through `KLS.surfaceMeasure`, finite-dimensionality at this point, so
-- the linter is silenced instead of the signature being narrowed by `omit`.
set_option linter.unusedSectionVars false in
/-- The level-set integrals of a measurable weight against the normalized surface measure form a
Lebesgue-measurable function of the level. -/
theorem aemeasurable_lintegral_levelSet {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) := by
  have h := KLS.aemeasurable_setLIntegral_inter_levelSet (S := Set.univ) hu.continuous
    hu.lipschitzOnWith MeasurableSet.univ hg
  simpa using h

end Coarea

end Analysis

end FunctionalInequalities

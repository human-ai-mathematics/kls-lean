import FunctionalInequalities.KLS.Geometry.SurfaceSlicing

/-! # Measurability of weighted level-set integrals

`Analysis.aemeasurable_lintegral_levelSet` migrated here from `KLS/WIP/AnalyticPrerequisites.lean`,
where it was a direct hole, with a **byte-identical `pp.all` signature**: the same universe, the
same six instance arguments in the same order (`CompleteSpace V` included, although the proof does
not use it), the same implicit binders `u`, `K`, `g`, the same hypothesis names `hu`, `hg`, and the
same conclusion.  Only its proof is new, and it no longer depends on `sorryAx`.  The module is free
of `sorry` and of transitive `sorryAx`.

The proof is `KLS.aemeasurable_setLIntegral_inter_levelSet` (obligation `L5` of the weighted coarea
route) at `S = Set.univ`, which is itself built from the measurable Eilenberg majorant (`L1`), null
slicing (`L2`), compact-slice measurability (`L3`) and the Borel version (`L4`) of
`KLS/Geometry/SurfaceSlicing.lean` and `Analysis/HausdorffContent.lean`.  No parametric-integral
theorem is used, so the codimension-one surface measure is never assumed `SFinite`, which it is not
in positive dimension.

The declaration keeps the `FunctionalInequalities.Analysis` namespace because its published name
must not change, while the file sits under `KLS/Geometry/` because the statement names
`KLS.surfaceMeasure` and is therefore not part of the KLS-independent `Analysis/` layer; the
work-in-progress file it replaces made the same choice.

This module supplies measurability. The equality
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` is proved separately in
`KLS/Geometry/LipschitzCoarea.lean`; `LocallyLipschitzCoarea` extends both conclusions to locally
Lipschitz functions. The sharp `C^(finrank)` `Analysis.sard` remains the direct hole in
`KLS/WIP/AnalyticPrerequisites.lean`. -/

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

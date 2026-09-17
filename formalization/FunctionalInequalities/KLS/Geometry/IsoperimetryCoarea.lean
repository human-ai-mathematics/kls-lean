import FunctionalInequalities.KLS.Geometry.SmoothCoarea

/-! # Weighted coarea for a `C¹` Lipschitz function

`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` migrated here from
`KLS/WIP/CheegerInfimum.lean`, where it was a direct hole, with a **byte-identical `pp.all`
signature**: the same universe, the same seven instance arguments in the same order
(`CompleteSpace V` and `SecondCountableTopology V` included, although the proof uses neither), the
same implicit binders `u`, `K`, `g`, the same hypothesis names `hu`, `hK`, `hg`, and the same
conclusion.  Only its proof is new, and it no longer depends on `sorryAx`.  The module is free of
`sorry` and of transitive `sorryAx`.

The proof is `KLS.coarea_of_contDiff` (obligation `L11`) at `S = Set.univ`.  The `LipschitzWith`
hypothesis `hK` is **not used**: the declaration already assumes `ContDiff ℝ 1 u`, and `L11` needs
no Lipschitz bound.  `L11` in turn is `L9` on the open regular set glued to `L10` on the closed
critical set, over the Mathlib-only analytic layer of `Analysis/`.

The declaration keeps the `FunctionalInequalities.KLS.Isoperimetry` namespace because its published
name must not change, while the file sits under `KLS/Geometry/` beside the coarea layer it consumes;
`KLS/Geometry/LevelSetMeasurable.lean` made the same choice.

The formula here retains its original `C¹` and Lipschitz hypotheses. The more general
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`, assuming only global Lipschitz
continuity, is proved separately in `LipschitzCoarea` from L12 and the compact-set Whitney
construction L6/L6a/L7. `LocallyLipschitzCoarea` proves the locally Lipschitz extension L13.
The sharp `C^(finrank)` `Analysis.sard` remains a direct hole in
`KLS/WIP/AnalyticPrerequisites.lean`. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.KLS

universe u

section Coarea

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

namespace Isoperimetry

-- The section variables and the hypothesis name `hK` are kept so that the published interface is
-- unchanged: the proof needs neither completeness, nor second countability, nor the Lipschitz
-- bound, so the two linters are silenced instead of the signature being narrowed by `omit` or the
-- hypothesis being renamed to `_`.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Weighted coarea formula for a `C¹` Lipschitz function on `V`, with Lebesgue measure on `V`
and the normalized surface measure `ℋ^{n-1}` on the level sets. -/
theorem lintegral_enorm_gradient_mul_eq_lintegral_levelSet {u : V → ℝ} (hu : ContDiff ℝ 1 u)
    {K : ℝ≥0} (hK : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  have h := (coarea_of_contDiff (S := Set.univ) (u := u) (g := g) hu MeasurableSet.univ hg).2
  simpa using h

end Isoperimetry

end Coarea

end FunctionalInequalities.KLS

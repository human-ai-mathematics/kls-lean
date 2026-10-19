import FunctionalInequalities.KLS.Geometry.Coarea.Smooth

/-! # Weighted coarea for a `C¹` Lipschitz function

`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` is the full-space
specialization of `KLS.coarea_of_contDiff`. The statement retains `CompleteSpace V`,
`SecondCountableTopology V` and its Lipschitz hypothesis, although the C¹ coarea proof
needs no Lipschitz bound. Regular-domain coarea and critical-slice nullity give the formula.

The globally Lipschitz formula is proved in `KLS/Geometry/Coarea/Lipschitz.lean` from exact
C¹ pieces and Whitney extension; `KLS/Geometry/Coarea/LocallyLipschitz.lean` gives its local
extension. The sharp finite-regularity Sard theorem is in `Analysis/Sard/Sharp.lean`.
These coarea formulas concern almost-everywhere slice measures, not critical-value nullity. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.KLS

universe u

section Coarea


namespace Isoperimetry

-- The ambient structure and the Lipschitz-bound name `hK` are retained in this interface.
-- The unused explicit bound keeps its local unused-variable exception.
set_option linter.unusedVariables false in
/-- Weighted coarea formula for a `C¹` Lipschitz function on `V`, with Lebesgue measure on `V`
and the normalized surface measure `ℋ^{n-1}` on the level sets. -/
theorem lintegral_enorm_gradient_mul_eq_lintegral_levelSet
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {u : V → ℝ} (hu : ContDiff ℝ 1 u)
    {K : ℝ≥0} (hK : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  have h := (coarea_of_contDiff (S := Set.univ) (u := u) (g := g) hu MeasurableSet.univ hg).2
  simpa using h

end Isoperimetry

end Coarea

end FunctionalInequalities.KLS

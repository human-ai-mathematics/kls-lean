module

public import FunctionalInequalities.Analysis.Coarea.Isoperimetry
public import FunctionalInequalities.Analysis.Coarea.Lipschitz
public import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
public import FunctionalInequalities.Analysis.Sard.Sharp

/-!
# Scope audit for the `C¹` weighted coarea formula

`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (in
`Analysis/Coarea/Isoperimetry.lean`) is proved from the global `C¹` weighted coarea formula
`KLS.coarea_of_contDiff` at `S = Set.univ`.

The **Lipschitz** formula `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`, which
assumes no `C¹` regularity, is proved in `Analysis/Coarea/Lipschitz.lean` from the Lipschitz
weighted coarea formula `KLS.coarea_of_lipschitz`.  The `C¹` result audited above is only its
specialization and does not imply it — it is `KLS.coarea_of_lipschitz` that does.

Also imported, so that all reports below come from a single consistent environment:

* the sharp `C^(finrank)` `Analysis.sard` (in `Analysis/Sard/Sharp.lean`).
* the two Cheeger comparisons `KLS.Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le` and
  `KLS.Isoperimetry.smoothConstant_le_minkowskiConstant`, together with the equality
  `KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant` that follows from them (in
  `KLS/Geometry/Cheeger/Equality.lean`).
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal ContDiff

namespace IsoperimetryCoareaAudit

/-- The `C¹` statement, restated verbatim and discharged through **named** arguments, so a
renamed binder or a reordered hypothesis would fail to elaborate here. -/
theorem client_isoperimetry_coarea :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {u : V → ℝ}, ContDiff ℝ 1 u → ∀ {K : ℝ≥0}, LipschitzWith K u →
      ∀ {g : V → ℝ≥0∞}, Measurable g →
      ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
        ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ _ u hu K hK g hg
  exact Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
    (u := u) (K := K) (g := g) hu hK hg

/-- The **Lipschitz** formula, restated verbatim and discharged through **named** arguments. -/
theorem client_lipschitz_coarea_statement :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
      {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ∀ {g : V → ℝ≥0∞}, Measurable g →
      ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
        ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hK g hg
  exact Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (u := u) (K := K) (g := g) hK hg

end IsoperimetryCoareaAudit

/-! ### Axiom audit -/

#print axioms
  FunctionalInequalities.KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
#print axioms IsoperimetryCoareaAudit.client_isoperimetry_coarea
#print axioms FunctionalInequalities.Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
#print axioms IsoperimetryCoareaAudit.client_lipschitz_coarea_statement
#print axioms FunctionalInequalities.Analysis.sard
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_le_minkowskiConstant
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant

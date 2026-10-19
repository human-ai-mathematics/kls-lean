import FunctionalInequalities.Analysis.Coarea.Isoperimetry
import FunctionalInequalities.Analysis.Coarea.Lipschitz
import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.Analysis.Sard.Sharp
-- 2026-09-19: `Analysis.sard` is proved in `Analysis/Sard/Sharp.lean`; the former `KLS/WIP/AnalyticPrerequisites.lean` is deleted, and this client now imports the proved module.
-- 2026-09-19: both Cheeger-infimum holes are proved in `KLS/Geometry/Cheeger/Equality.lean`; the former `KLS/WIP/CheegerInfimum.lean` is deleted, and this client now imports the proved module.

/-!
# Scope audit for the migrated `C¹` weighted coarea formula

`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` has moved out of
`KLS/WIP/CheegerInfimum.lean` into the hole-free `Analysis/Coarea/Isoperimetry.lean` with a
**byte-identical `pp.all` signature** (recorded in `build/audit/iso-signature-before.log` and
`build/audit/iso-signature-after.log`), and is now proved from obligation `L11`
(`KLS.coarea_of_contDiff`) at `S = Set.univ`.  Its axiom report below therefore no longer contains
`sorryAx`.

This client imports the new module **and both** work-in-progress files, so the reports come from a
single consistent environment: the migrated name resolves to exactly one declaration, and every
obligation that is still open reports `sorryAx` from that same environment.

**Updated on 2026-09-16.** The **Lipschitz** formula
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`, which assumes no `C¹` regularity,
has since been proved through `L12` and migrated out of `KLS/WIP/AnalyticPrerequisites.lean` into
`Analysis/Coarea/Lipschitz.lean` with a byte-identical `pp.all` signature.  That import was
added here, so the two reports naming it below no longer contain `sorryAx`; the clients and their
statements are unchanged.  The `C¹` result audited above is still only its specialization and
still does not imply it — it is `L12` that does.

Still open, and kept explicit here:

* the sharp `C^(finrank)` `Analysis.sard`, with `Analysis.ae_forall_fderiv_ne_zero`.
* the two Cheeger comparisons `KLS.Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le` and
  `KLS.Isoperimetry.smoothConstant_le_minkowskiConstant`, the only remaining holes of
  `KLS/WIP/CheegerInfimum.lean`, together with the equality
  `KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant` that inherits from them.
-/

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal ContDiff

namespace IsoperimetryCoareaAudit

/-- The migrated statement, restated verbatim and discharged through **named** arguments, so a
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

/-- The **Lipschitz** formula, restated verbatim and discharged through **named** arguments.  Its
report carried `sorryAx` while the declaration was a hole in the work-in-progress file; it is
clean now that the declaration has been migrated and proved, and the restatement itself has not
been altered. -/
theorem client_lipschitz_coarea_statement :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
      {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ∀ {g : V → ℝ≥0∞}, Measurable g →
      ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
        ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hK g hg
  exact Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (u := u) (K := K) (g := g) hK hg

end IsoperimetryCoareaAudit

/-! ### Axiom audit: the migrated result is clean, the remaining obligations are not -/

#print axioms FunctionalInequalities.KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
#print axioms IsoperimetryCoareaAudit.client_isoperimetry_coarea
#print axioms FunctionalInequalities.Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
#print axioms IsoperimetryCoareaAudit.client_lipschitz_coarea_statement
#print axioms FunctionalInequalities.Analysis.sard
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_le_minkowskiConstant
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant

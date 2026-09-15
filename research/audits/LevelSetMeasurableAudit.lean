import FunctionalInequalities.KLS.Geometry.LevelSetMeasurable
import FunctionalInequalities.KLS.WIP.AnalyticPrerequisites

/-!
# Scope audit for the migrated level-set measurability

`Analysis.aemeasurable_lintegral_levelSet` has moved out of `KLS/WIP/AnalyticPrerequisites.lean`
into the hole-free `KLS/Geometry/LevelSetMeasurable.lean` with a **byte-identical `pp.all`
signature** (recorded in `build/audit/migration-signature-before.log` and
`build/audit/migration-signature-after.log`), and is now proved from obligation `L5`
(`KLS.aemeasurable_setLIntegral_inter_levelSet`).  Its axiom report below therefore no longer
contains `sorryAx`.

This client imports **both** the new module and the work-in-progress file, so the reports below are
a single consistent environment: the migrated name resolves to exactly one declaration, and the
obligations that are still open there report `sorryAx` from the same environment.

The **equality** is untouched: `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` is
still a direct hole, as is the sharp `C^(finrank)` `Analysis.sard`, and
`Analysis.ae_forall_fderiv_ne_zero` still inherits `sorryAx` from the latter.  Both boundaries are
kept explicit here.
-/

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal

namespace LevelSetMeasurableAudit

/-- The migrated statement, restated verbatim and discharged through **named** arguments, so a
renamed binder or a reordered hypothesis would fail to elaborate here. -/
theorem client_aemeasurable_lintegral_levelSet :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
      {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ∀ {g : V → ℝ≥0∞}, Measurable g →
      AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
        (volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  exact Analysis.aemeasurable_lintegral_levelSet (u := u) (K := K) (g := g) hu hg

/-- The equality is still open: this client only restates it, it does not prove it. -/
theorem client_coarea_statement :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
      {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ∀ {g : V → ℝ≥0∞}, Measurable g →
      ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
        ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  exact Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (u := u) (K := K) (g := g) hu hg

end LevelSetMeasurableAudit

/-! ### Axiom audit: the migrated result is clean, the remaining obligations are not -/

#print axioms FunctionalInequalities.Analysis.aemeasurable_lintegral_levelSet
#print axioms LevelSetMeasurableAudit.client_aemeasurable_lintegral_levelSet
#print axioms FunctionalInequalities.Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
#print axioms LevelSetMeasurableAudit.client_coarea_statement
#print axioms FunctionalInequalities.Analysis.sard
#print axioms FunctionalInequalities.Analysis.ae_forall_fderiv_ne_zero

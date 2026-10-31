module

public import FunctionalInequalities.Analysis.Hausdorff.Slice.Measurable
public import FunctionalInequalities.Analysis.Coarea.Lipschitz
public import FunctionalInequalities.Analysis.Sard.Sharp

/-!
# Scope audit for level-set measurability

`Analysis.aemeasurable_lintegral_levelSet` (in `Analysis/Hausdorff/Slice/Measurable.lean`) is
proved from the weighted slice measurability `KLS.aemeasurable_setLIntegral_inter_levelSet`.

The **equality** `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (in
`Analysis/Coarea/Lipschitz.lean`) is proved from the Lipschitz weighted coarea formula
`KLS.coarea_of_lipschitz` at `S = Set.univ`.

The sharp `C^(finrank)` `Analysis.sard` (in `Analysis/Sard/Sharp.lean`) and its consequence
`Analysis.ae_forall_fderiv_ne_zero` are imported as well, so that all reports below come from a
single consistent environment.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal

namespace LevelSetMeasurableAudit

/-- The measurability statement, restated verbatim and discharged through **named** arguments,
so a renamed binder or a reordered hypothesis would fail to elaborate here. -/
theorem client_aemeasurable_lintegral_levelSet :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
      {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ∀ {g : V → ℝ≥0∞}, Measurable g →
      AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
        (volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  exact Analysis.aemeasurable_lintegral_levelSet (u := u) (K := K) (g := g) hu hg

/-- The equality, restated verbatim and discharged through **named** arguments, so a renamed
binder or a reordered hypothesis would fail to elaborate here. -/
theorem client_coarea_statement :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
      {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ∀ {g : V → ℝ≥0∞}, Measurable g →
      ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
        ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  exact Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (u := u) (K := K) (g := g) hu hg

end LevelSetMeasurableAudit

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.Analysis.aemeasurable_lintegral_levelSet
#print axioms LevelSetMeasurableAudit.client_aemeasurable_lintegral_levelSet
#print axioms FunctionalInequalities.Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
#print axioms LevelSetMeasurableAudit.client_coarea_statement
#print axioms FunctionalInequalities.Analysis.sard
#print axioms FunctionalInequalities.Analysis.ae_forall_fderiv_ne_zero

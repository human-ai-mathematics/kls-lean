import FunctionalInequalities.KLS.Geometry.LipschitzCoarea
import FunctionalInequalities.KLS.Geometry.LevelSetMeasurable
import FunctionalInequalities.KLS.Geometry.IsoperimetryCoarea
import FunctionalInequalities.Analysis.Sard.Sharp
import FunctionalInequalities.KLS.Geometry.CheegerEquality
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2
-- 2026-09-19: `Analysis.sard` is proved in `Analysis/Sard/Sharp.lean`; the former `KLS/WIP/AnalyticPrerequisites.lean` is deleted, and this client now imports the proved module.
-- 2026-09-19: both Cheeger-infimum holes are proved in `KLS/Geometry/CheegerEquality.lean`; the former `KLS/WIP/CheegerInfimum.lean` is deleted, and this client now imports the proved module.

/-!
# Scope audit for the migrated Lipschitz weighted coarea formula (`T2`)

`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` has moved out of
`KLS/WIP/AnalyticPrerequisites.lean`, where it was a direct hole, into the hole-free
`KLS/Geometry/LipschitzCoarea.lean`, beside the `L12` theorem `KLS.coarea_of_lipschitz` that
proves it at `S = Set.univ`.  The migration is signature-preserving:

* the `pp.all` type printed before the migration from an environment importing the
  work-in-progress file and after it from an environment importing the new module is
  **byte-identical** (`build/audit/t2-migration/signature-before.raw`,
  `build/audit/t2-migration/signature-after.raw`);
* the stored universe parameter is `u` in both, and the binder names and binder kinds agree,
  up to the module tag inside the inaccessible anonymous instance binders
  (`build/audit/t2-migration/binders-before.raw`, `binders-after.raw`).

The universe, the six instance arguments in their original order — `CompleteSpace V` included,
which is what the statement's `gradient` elaborates against — the implicit binders `u`, `K`, `g`,
the hypothesis names `hu` and `hg`, the `LipschitzWith` hypothesis, the `KLS.surfaceMeasure`
normalization and the unrestricted `ℝ≥0∞` weight are all unchanged.  No `C¹`, positive-dimension,
finite-volume, integrability or `SFinite` hypothesis was added, and no compatibility alias was
introduced.  Only its proof is new, and it no longer depends on `sorryAx`.

This client imports the new module **and both** work-in-progress files, so every report below
comes from a single consistent environment and each migrated name resolves to exactly one
declaration.

Still open, and kept explicit here: the sharp `C^(finrank)` `Analysis.sard`, whose statement and
proof are untouched in `KLS/WIP/AnalyticPrerequisites.lean`, with its consequence
`Analysis.ae_forall_fderiv_ne_zero`; and the two Cheeger comparisons of
`KLS/WIP/CheegerInfimum.lean` with the equality that inherits from them.
-/

noncomputable section

open Set MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal ContDiff

namespace LipschitzCoareaMigrationAudit

/-- The migrated declaration, restated verbatim and discharged through **named** arguments, so a
renamed binder, a reordered hypothesis or a dropped instance would fail to elaborate here. -/
theorem client_migrated_t2 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
      {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ∀ {g : V → ℝ≥0∞}, Measurable g →
      ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
        ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  exact Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (u := u) (K := K) (g := g) hu hg

/-- The **original `T2` proposition**, reproduced with the binder shape of the weighted coarea
route record, discharged through the migrated entry point rather than through `L12` directly.
This is an independent client: it names no intermediate obligation. -/
theorem original_T2 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}
    (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  exact Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet hu hg

/-- `L12` itself, restated and discharged, so that the source of the migrated proof is audited in
the same environment.  The set, the weight and the Lipschitz constant stay arbitrary. -/
theorem client_L12 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {K : ℝ≥0} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ S u K g hu hS hg
  exact KLS.coarea_of_lipschitz (S := S) (u := u) (K := K) (g := g) hu hS hg

/-- The migrated equality and the previously migrated measurability half now combine into the
original two-part coarea conclusion without naming `L5` or `L12`. -/
theorem client_both_halves {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) :=
  ⟨Analysis.aemeasurable_lintegral_levelSet hu hg,
    Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet hu hg⟩

/-- The migrated entry point applies to a function that is genuinely not `C¹`, on the whole of an
unbounded space, with an arbitrary measurable weight. -/
theorem norm_not_contDiff (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ¬ DifferentiableAt ℝ (fun x : ℝ ↦ ‖x‖) 0 ∧
      ∫⁻ x, ‖gradient (fun x : ℝ ↦ ‖x‖) x‖ₑ * g x =
        ∫⁻ t, ∫⁻ y in {x : ℝ | ‖x‖ = t}, g y ∂(KLS.surfaceMeasure ℝ) :=
  ⟨not_differentiableAt_norm_zero ℝ,
    Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet lipschitzWith_one_norm hg⟩

/-- An identically infinite weight is inside the migrated statement's range. -/
theorem infinite_weight {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∫⁻ x, ‖gradient u x‖ₑ * (∞ : ℝ≥0∞) ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ _y in {x | u x = t}, (∞ : ℝ≥0∞) ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) :=
  Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (g := fun _ ↦ ∞) hu measurable_const

/-- No positive-dimension hypothesis is hidden in the migrated entry point. -/
theorem zero_dimension {u : EuclideanSpace ℝ (Fin 0) → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : EuclideanSpace ℝ (Fin 0) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure (EuclideanSpace ℝ (Fin 0))) :=
  Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet hu hg

/-- The `C¹` specialization that was migrated in the previous round still type-checks against the
same environment, and is unchanged by this migration. -/
theorem client_contDiff_specialization {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] {u : V → ℝ} (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) :=
  Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (u := u) (K := K) (g := g)
    hu hK hg

end LipschitzCoareaMigrationAudit

/-! ### Axiom audit

The migrated declaration, its `L12` source, the previously migrated neighbours and every client
above use only the three standard axioms.  The Sard hole and the two Cheeger comparisons still
report `sorryAx`; they were not touched. -/

#print axioms FunctionalInequalities.Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
#print axioms FunctionalInequalities.KLS.coarea_of_lipschitz
#print axioms FunctionalInequalities.Analysis.aemeasurable_lintegral_levelSet
#print axioms FunctionalInequalities.KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
#print axioms LipschitzCoareaMigrationAudit.client_migrated_t2
#print axioms LipschitzCoareaMigrationAudit.original_T2
#print axioms LipschitzCoareaMigrationAudit.client_L12
#print axioms LipschitzCoareaMigrationAudit.client_both_halves
#print axioms LipschitzCoareaMigrationAudit.norm_not_contDiff
#print axioms LipschitzCoareaMigrationAudit.infinite_weight
#print axioms LipschitzCoareaMigrationAudit.zero_dimension
#print axioms LipschitzCoareaMigrationAudit.client_contDiff_specialization
#print axioms FunctionalInequalities.Analysis.sard
#print axioms FunctionalInequalities.Analysis.ae_forall_fderiv_ne_zero
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_le_minkowskiConstant

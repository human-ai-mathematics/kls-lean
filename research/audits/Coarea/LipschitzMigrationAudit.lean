import FunctionalInequalities.Analysis.Coarea.Lipschitz
import FunctionalInequalities.Analysis.Hausdorff.Slice.Measurable
import FunctionalInequalities.Analysis.Coarea.Isoperimetry
import FunctionalInequalities.Analysis.Sard.Sharp
import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the Lipschitz weighted coarea formula

`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (in `Analysis/Coarea/Lipschitz.lean`)
is the Lipschitz weighted coarea formula `KLS.coarea_of_lipschitz` at `S = Set.univ`.  Its statement
is target `T2` of `research/audits/Coarea/WeightedRouteStatements.lean`, with the stored universe
parameter `u`.

The universe, the six instance arguments in their original order — `CompleteSpace V` included,
which is what the statement's `gradient` elaborates against — the implicit binders `u`, `K`, `g`,
the hypothesis names `hu` and `hg`, the `LipschitzWith` hypothesis, the `KLS.surfaceMeasure`
normalization and the unrestricted `ℝ≥0∞` weight are those of the original target.  No `C¹`,
positive-dimension, finite-volume, integrability or `SFinite` hypothesis is assumed.

Also imported, so that every report below comes from a single consistent environment: the sharp
`C^(finrank)` `Analysis.sard` (in `Analysis/Sard/Sharp.lean`) with its consequence
`Analysis.ae_forall_fderiv_ne_zero`, and the two Cheeger comparisons with the equality that
follows from them (in `KLS/Geometry/Cheeger/Equality.lean`).
-/

noncomputable section

open Set MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal ContDiff

namespace LipschitzCoareaMigrationAudit

/-- The Lipschitz coarea equality, restated verbatim and discharged through **named** arguments,
so a renamed binder, a reordered hypothesis or a dropped instance would fail to elaborate here. -/
theorem client_migrated_t2 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
      {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ∀ {g : V → ℝ≥0∞}, Measurable g →
      ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
        ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  exact Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (u := u) (K := K) (g := g) hu hg

/-- The **original target `T2`** of `Coarea/WeightedRouteStatements.lean`, reproduced with its
binder shape there, discharged through
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` rather than through
`KLS.coarea_of_lipschitz` directly.  This is an independent client: it names no intermediate
obligation. -/
theorem original_T2 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}
    (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  exact Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet hu hg

/-- The Lipschitz weighted coarea formula `KLS.coarea_of_lipschitz` itself, restated and
discharged, so that the source of the proof above is audited in the same environment.  The set,
the weight and the Lipschitz constant stay arbitrary. -/
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

section InnerProduct

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

section FiniteDimensional

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The equality and the measurability half `Analysis.aemeasurable_lintegral_levelSet` combine
into the two-part coarea conclusion without naming `KLS.aemeasurable_setLIntegral_inter_levelSet`
or `KLS.coarea_of_lipschitz`. -/
theorem client_both_halves
    {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) :=
  ⟨Analysis.aemeasurable_lintegral_levelSet hu hg,
    Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet hu hg⟩

/-- The equality applies to a function that is genuinely not `C¹`, on the whole of an
unbounded space, with an arbitrary measurable weight. -/
theorem norm_not_contDiff (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ¬ DifferentiableAt ℝ (fun x : ℝ ↦ ‖x‖) 0 ∧
      ∫⁻ x, ‖gradient (fun x : ℝ ↦ ‖x‖) x‖ₑ * g x =
        ∫⁻ t, ∫⁻ y in {x : ℝ | ‖x‖ = t}, g y ∂(KLS.surfaceMeasure ℝ) :=
  ⟨not_differentiableAt_norm_zero ℝ,
    Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet lipschitzWith_one_norm hg⟩

/-- An identically infinite weight is inside the statement's range. -/
theorem infinite_weight
    {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∫⁻ x, ‖gradient u x‖ₑ * (∞ : ℝ≥0∞) ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ _y in {x | u x = t}, (∞ : ℝ≥0∞) ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) :=
  Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (g := fun _ ↦ ∞) hu measurable_const

end FiniteDimensional

/-- No positive-dimension hypothesis is hidden in the equality. -/
theorem zero_dimension {u : EuclideanSpace ℝ (Fin 0) → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : EuclideanSpace ℝ (Fin 0) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure (EuclideanSpace ℝ (Fin 0))) :=
  Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet hu hg

/-- The `C¹` specialization `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
type-checks in the same environment. -/
theorem client_contDiff_specialization [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] {u : V → ℝ} (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) :=
  Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (u := u) (K := K) (g := g)
    hu hK hg

end InnerProduct

end LipschitzCoareaMigrationAudit

/-! ### Axiom audit

The Lipschitz coarea equality, its source `KLS.coarea_of_lipschitz`, the neighbouring
measurability and `C¹` statements and every client above use only the three standard axioms.  The
reports of `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero` and the two Cheeger comparisons
are recorded from the same environment. -/

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

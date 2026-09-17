import FunctionalInequalities.KLS.Geometry.LocallyLipschitzCoarea
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the locally Lipschitz weighted coarea formula (`L13`)

`KLS.coarea_of_locallyLipschitz` drops every global hypothesis on `u` except local Lipschitz
continuity.  This client checks three things in one environment:

* the statement itself, restated verbatim and proved;
* that it is a **common generalization** of the two theorems it is built from — the `L12`
  statement (`LipschitzWith K u`) and the `L11` statement (`ContDiff ℝ 1 u`) are both re-derived
  from it alone, without naming `coarea_of_lipschitz` or `coarea_of_contDiff`;
* that the generalization is **strict**: `x ↦ x² + ‖x‖` is locally Lipschitz, is proved here to be
  neither globally Lipschitz for any constant nor differentiable at `0`, so it is outside the
  reach of both earlier theorems, and the coarea formula is proved for it.

Boundary clients cover an identically infinite weight and a zero-dimensional space.  This module
imports no work-in-progress file, and all reports below use only `propext`, `Classical.choice` and
`Quot.sound`.
-/

noncomputable section

open Set MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal ContDiff

namespace LocallyLipschitzCoareaAudit

/-- **L13** restated verbatim and discharged through **named** arguments. -/
theorem original_L13 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    LocallyLipschitz u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ S u g hu hS hg
  exact KLS.coarea_of_locallyLipschitz (S := S) (u := u) (g := g) hu hS hg

/-- The `L12` statement is recovered from `L13` alone: a global Lipschitz bound is one way to be
locally Lipschitz.  `coarea_of_lipschitz` is **not** named in this proof. -/
theorem recovers_L12 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {K : ℝ≥0} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ S u K g hu hS hg
  exact KLS.coarea_of_locallyLipschitz hu.locallyLipschitz hS hg

/-- The `L11` statement is recovered from `L13` alone: a `C¹` function is locally Lipschitz.
`coarea_of_contDiff` is **not** named in this proof, and no Lipschitz bound appears. -/
theorem recovers_L11 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    ContDiff ℝ 1 u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ S u g hu hS hg
  exact KLS.coarea_of_locallyLipschitz hu.locallyLipschitz hS hg

/-! ### The generalization is strict -/

/-- The witness: `x ↦ x² + ‖x‖` on the line. -/
private def witness : ℝ → ℝ := fun x ↦ x ^ 2 + ‖x‖

theorem witness_locallyLipschitz : LocallyLipschitz witness :=
  ((contDiff_id (𝕜 := ℝ) (n := 1)).pow 2).locallyLipschitz.add
    (lipschitzWith_one_norm (E := ℝ)).locallyLipschitz

/-- The witness is **not** globally Lipschitz, for any constant: `L12` does not apply to it. -/
theorem witness_not_lipschitz : ¬ ∃ K : ℝ≥0, LipschitzWith K witness := by
  rintro ⟨K, hK⟩
  have hpos : (0:ℝ) < (K : ℝ) + 1 := by positivity
  have h := hK.dist_le_mul ((K : ℝ) + 1) 0
  simp only [witness, Real.dist_eq, Real.norm_eq_abs, sub_zero, abs_of_nonneg hpos.le, abs_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ((K:ℝ)+1)^2 + ((K:ℝ)+1))] at h
  nlinarith [K.coe_nonneg]

/-- The witness is **not** differentiable at `0`, so it is not `C¹`: `L11` does not apply to it. -/
theorem witness_not_differentiableAt : ¬ DifferentiableAt ℝ witness 0 := by
  intro h
  have hpow : DifferentiableAt ℝ (fun x : ℝ ↦ x ^ 2) 0 := (differentiable_id.pow 2).differentiableAt
  have heq : (fun x : ℝ ↦ ‖x‖) = fun x : ℝ ↦ witness x - x ^ 2 := by
    funext x
    simp only [witness, add_sub_cancel_left]
  have hnorm : DifferentiableAt ℝ (fun x : ℝ ↦ ‖x‖) 0 := by
    rw [heq]
    exact h.sub hpow
  exact not_differentiableAt_norm_zero ℝ hnorm

/-- `L13` proves the coarea formula for a function that neither `L11` nor `L12` covers. -/
theorem witness_coarea {S : Set ℝ} (hS : MeasurableSet S) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in S, ‖gradient witness x‖ₑ * g x) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | witness x = t}, g y ∂(KLS.surfaceMeasure ℝ) :=
  (KLS.coarea_of_locallyLipschitz witness_locallyLipschitz hS hg).2

/-! ### Boundary clients -/

/-- An identically infinite weight is inside the statement's range. -/
theorem infinite_weight {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {S : Set V} {u : V → ℝ}
    (hu : LocallyLipschitz u) (hS : MeasurableSet S) :
    (∫⁻ x in S, ‖gradient u x‖ₑ * (∞ : ℝ≥0∞) ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ _y in S ∩ {x | u x = t}, (∞ : ℝ≥0∞) ∂(KLS.surfaceMeasure V)
        ∂(volume : Measure ℝ) :=
  (KLS.coarea_of_locallyLipschitz (g := fun _ ↦ ∞) hu hS measurable_const).2

/-- No positive-dimension hypothesis is hidden in the statement. -/
theorem zero_dimension {u : EuclideanSpace ℝ (Fin 0) → ℝ} (hu : LocallyLipschitz u)
    {S : Set (EuclideanSpace ℝ (Fin 0))} (hS : MeasurableSet S)
    {g : EuclideanSpace ℝ (Fin 0) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure (EuclideanSpace ℝ (Fin 0))) :=
  (KLS.coarea_of_locallyLipschitz hu hS hg).2

end LocallyLipschitzCoareaAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.KLS.coarea_of_locallyLipschitz
#print axioms LocallyLipschitzCoareaAudit.original_L13
#print axioms LocallyLipschitzCoareaAudit.recovers_L12
#print axioms LocallyLipschitzCoareaAudit.recovers_L11
#print axioms LocallyLipschitzCoareaAudit.witness_locallyLipschitz
#print axioms LocallyLipschitzCoareaAudit.witness_not_lipschitz
#print axioms LocallyLipschitzCoareaAudit.witness_not_differentiableAt
#print axioms LocallyLipschitzCoareaAudit.witness_coarea
#print axioms LocallyLipschitzCoareaAudit.infinite_weight
#print axioms LocallyLipschitzCoareaAudit.zero_dimension

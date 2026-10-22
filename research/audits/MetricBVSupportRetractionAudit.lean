import FunctionalInequalities.Analysis.MetricBV.Basic
import FunctionalInequalities.Analysis.MetricBV.Finite
import FunctionalInequalities.Analysis.MetricBV.Transport

/-! Independent full-signature clients for the perimeter equality under a nonexpansive retraction
onto a full-mass measurable subset: the nonexpansive-composition slope bound (with a collapsing
map), the reverse inequality and the equality, and the genuine proper retract
`Set.projIcc 0 1 : ℝ → Icc 0 1` for the uniform law on `[0, 1]`, the two-atom law
`(δ₀ + δ₁)/2`, and the zero measure. Consequences beyond an alias: finiteness and vanishing of
the perimeter transfer between the space and the trace. This is a structural retraction theorem;
it is not `closedSupportLaw` equality for arbitrary supports, nor the closed convex projection,
nor an identification of `intrinsicHalfConstant`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVSupportRetractionAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

section StructuredSpace

variable {X Y : Type*}
variable [MetricSpace X] [MetricSpace Y]

theorem slopeComposition {r : X → Y}
    (hr : LipschitzWith 1 r) (g : Y → ℝ) (x : X) :
    FunctionalInequalities.Energy.LocalSlope.apply (g ∘ r) x ≤
      FunctionalInequalities.Energy.LocalSlope.apply g (r x) := by
  exact FunctionalInequalities.Energy.LocalSlope.apply_comp_le_of_lipschitzWith_one hr g x

/-- A fully collapsing nonexpansive map: the bound holds, and the composed slope is zero. -/
theorem collapsedSlope (y₀ : Y) (g : Y → ℝ)
    (x : X) :
    FunctionalInequalities.Energy.LocalSlope.apply (g ∘ fun _ : X => y₀) x ≤
        FunctionalInequalities.Energy.LocalSlope.apply g y₀ ∧
      FunctionalInequalities.Energy.LocalSlope.apply (g ∘ fun _ : X => y₀) x = 0 :=
  ⟨FunctionalInequalities.Energy.LocalSlope.apply_comp_le_of_lipschitzWith_one
      ((LipschitzWith.const y₀).weaken zero_le_one) g x,
    FunctionalInequalities.Energy.LocalSlope.apply_const (g y₀) x⟩

end StructuredSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem retractionLe (ν : Measure X) [IsFiniteMeasure ν] {s : Set X} (hs : MeasurableSet s)
    (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r) (hrs : ∀ z : s, r z = z)
    (B : Set X) :
    perimeter ν B ≤ perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) := by
  exact perimeter_le_comap_subtype_of_retraction ν hs hfull hr hrs B

theorem retractionEq (ν : Measure X) [IsFiniteMeasure ν] {s : Set X} (hs : MeasurableSet s)
    (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r) (hrs : ∀ z : s, r z = z)
    (B : Set X) :
    perimeter ν B = perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) := by
  exact perimeter_eq_comap_subtype_of_retraction ν hs hfull hr hrs B

/-- The requested form, with `B` measurable. -/
theorem retractionEqMeasurable (ν : Measure X) [IsFiniteMeasure ν] {s : Set X}
    (hs : MeasurableSet s) (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r)
    (hrs : ∀ z : s, r z = z) {B : Set X} (_hB : MeasurableSet B) :
    perimeter ν B = perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) := by
  exact perimeter_eq_comap_subtype_of_retraction ν hs hfull hr hrs B

/-- Finiteness of the perimeter transfers in both directions. -/
theorem finiteTransfer (ν : Measure X) [IsFiniteMeasure ν] {s : Set X} (hs : MeasurableSet s)
    (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r) (hrs : ∀ z : s, r z = z)
    (B : Set X) :
    perimeter ν B < ⊤ ↔
      perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) < ⊤ := by
  rw [perimeter_eq_comap_subtype_of_retraction ν hs hfull hr hrs B]

/-- Zero trace perimeter forces zero ambient perimeter (the reverse direction). -/
theorem zeroTransfer (ν : Measure X) [IsFiniteMeasure ν] {s : Set X} (hs : MeasurableSet s)
    (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r) (hrs : ∀ z : s, r z = z)
    {B : Set X}
    (h0 : perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) = 0) :
    perimeter ν B = 0 :=
  le_antisymm ((perimeter_le_comap_subtype_of_retraction ν hs hfull hr hrs B).trans_eq h0) bot_le

/-- The genuine proper nonexpansive retraction `projIcc 0 1` of `ℝ` onto `[0, 1]`. -/
theorem projIccRetraction :
    LipschitzWith 1 (Set.projIcc (0 : ℝ) 1 zero_le_one) ∧
      (∀ z : Set.Icc (0 : ℝ) 1, Set.projIcc (0 : ℝ) 1 zero_le_one z = z) ∧
      (2 : ℝ) ∉ Set.Icc (0 : ℝ) 1 :=
  ⟨LipschitzWith.projIcc zero_le_one, Set.projIcc_val zero_le_one, by norm_num⟩

/-- The uniform law on `[0, 1]`: perimeters on `ℝ` equal perimeters of traces on `[0, 1]`. -/
theorem uniformInterval (B : Set ℝ) :
    perimeter ((volume : Measure ℝ).restrict (Set.Icc 0 1)) B =
      perimeter (((volume : Measure ℝ).restrict (Set.Icc 0 1)).comap
        (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)) ((Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) ⁻¹' B) := by
  refine perimeter_eq_comap_subtype_of_retraction _ measurableSet_Icc ?_
    (LipschitzWith.projIcc zero_le_one) (Set.projIcc_val zero_le_one) B
  rw [Measure.restrict_apply measurableSet_Icc.compl]
  simp

/-- The two-atom law `(δ₀ + δ₁)/2`, whose atoms lie in `[0, 1]`. -/
theorem twoAtomInterval (B : Set ℝ) :
    perimeter ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac 1)) B =
      perimeter (((2 : ℝ≥0∞)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac 1)).comap
        (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)) ((Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) ⁻¹' B) := by
  have : IsFiniteMeasure ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac 1)) := by
    refine ⟨?_⟩
    simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 two_pos) (by norm_num)
  refine perimeter_eq_comap_subtype_of_retraction _ measurableSet_Icc ?_
    (LipschitzWith.projIcc zero_le_one) (Set.projIcc_val zero_le_one) B
  have h0 : (0 : ℝ) ∉ (Set.Icc (0 : ℝ) 1)ᶜ := by simp
  have h1 : (1 : ℝ) ∉ (Set.Icc (0 : ℝ) 1)ᶜ := by simp
  simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Icc.compl]
  rw [Set.indicator_of_notMem h0, Set.indicator_of_notMem h1]
  simp

/-- The zero measure. -/
theorem zeroMeasure (B : Set ℝ) :
    perimeter (0 : Measure ℝ) B =
      perimeter ((0 : Measure ℝ).comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))
        ((Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) ⁻¹' B) :=
  perimeter_eq_comap_subtype_of_retraction _ measurableSet_Icc (by simp)
    (LipschitzWith.projIcc zero_le_one) (Set.projIcc_val zero_le_one) B

#print axioms slopeComposition
#print axioms collapsedSlope
#print axioms retractionLe
#print axioms retractionEq
#print axioms retractionEqMeasurable
#print axioms finiteTransfer
#print axioms zeroTransfer
#print axioms projIccRetraction
#print axioms uniformInterval
#print axioms twoAtomInterval
#print axioms zeroMeasure

end MetricBVSupportRetractionAudit

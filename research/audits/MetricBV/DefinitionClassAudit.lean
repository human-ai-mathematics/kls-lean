module

public import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski
public import FunctionalInequalities.KLS.Geometry.Perimeter.TestClassRelaxation

/-! Strict proof client: ADMG Theorem 3.6 and Lemma 2.1 stated against the paper's own
Definition 3.3 class, i.e. globally Lipschitz approximants with unrestricted values/supports and
global `L¹(ν)` convergence (`lipschitzRelaxation`), rather than the bounded-support test
perimeter, by composing the Minkowski identities with
`lipschitzRelaxation_eq_perimeter_of_measure_lt_top`. Both sides are written as the unfolded infima.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace MetricBVDefinitionClassAudit
open FunctionalInequalities
open FunctionalInequalities.KLS.MetricBV
open FunctionalInequalities.KLS.Isoperimetry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Theorem 3.6, lower relaxed content, with the Definition 3.3 infimum on the right. -/
theorem theorem36_lower (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    (⨅ A : MinkowskiApproximatingSequence ν B,
        liminf (fun n => minkowskiContent ν (A.1 n)) atTop) =
      ⨅ f : LipschitzApproximatingSequence ν B,
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  (relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded ν hν hB hνB).trans
    (lipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB).symm

/-- Theorem 3.6, upper relaxed content, with the Definition 3.3 infimum on the right. -/
theorem theorem36_upper (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    (⨅ A : MinkowskiApproximatingSequence ν B,
        liminf (fun n => upperMinkowskiContent ν (A.1 n)) atTop) =
      ⨅ f : LipschitzApproximatingSequence ν B,
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  (relaxedUpperMinkowskiContent_eq_perimeter_of_finite_on_bounded ν hν hB hνB).trans
    (lipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB).symm

/-- Lemma 2.1, first clause (2.2), for every Borel measure at a measurable finite-mass target. -/
theorem lemma21_bound (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    (⨅ A : MinkowskiApproximatingSequence ν B,
        liminf (fun n => upperMinkowskiContent ν (A.1 n)) atTop) ≤ minkowskiContent ν B :=
  relaxedUpperMinkowskiContent_le_minkowskiContent_of_measure_lt_top ν hB hνB

/-- Lemma 2.1, second clause, at the paper's standing measure scope. -/
theorem lemma21_equality (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    relaxedMinkowskiContent ν B = relaxedUpperMinkowskiContent ν B :=
  (relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent_of_finite_on_bounded ν hν hB hνB).symm

/-- The Definition 3.3 infimum is bounded by the lower content of the target itself
(Theorem 3.6 first claim, `M₋(A) ≥ Per(A)`), for every Borel measure. -/
theorem definitionClass_le_content (ν : Measure X) {B : Set X} (hB : MeasurableSet B)
    (hνB : ν B < ⊤) : lipschitzRelaxation ν B ≤ minkowskiContent ν B :=
  (lipschitzRelaxation_le_perimeter ν B).trans
    (perimeter_le_minkowskiContent_of_measure_lt_top ν hB hνB)

end MetricBVDefinitionClassAudit

#print axioms MetricBVDefinitionClassAudit.theorem36_lower
#print axioms MetricBVDefinitionClassAudit.theorem36_upper
#print axioms MetricBVDefinitionClassAudit.lemma21_bound
#print axioms MetricBVDefinitionClassAudit.lemma21_equality
#print axioms MetricBVDefinitionClassAudit.definitionClass_le_content

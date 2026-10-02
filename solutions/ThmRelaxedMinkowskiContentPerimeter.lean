import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski
import FunctionalInequalities.KLS.Geometry.Perimeter.TestClassRelaxation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lean certificate: `thm:relaxed-minkowski-content-perimeter`

Ambrosio–Di Marino–Gigli, *Perimeter as relaxed Minkowski content in metric measure spaces*
(arXiv:1603.08412v1), Theorem 3.6, stated against the paper's own Definition 3.3. Let `(V, d)` be
a metric space with its Borel σ-algebra and `ν` a Borel measure that is finite on bounded Borel
sets (the paper's standing assumption). For every Borel set `B` with `ν B < ∞`, the relaxed
lower Minkowski content equals the perimeter of Definition 3.3:

`inf { liminf_h M₋(A_h) : A_h → B in ν-measure } = inf { liminf_h ∫ |∇f_h| dν : f_h ∈ Lip(V), f_h → 1_B in L¹(ν) }`,

where `M₋(A) = liminf_{r ↓ 0} (ν(A^r) − ν(A)) / r` with open `r`-enlargements, `|∇f|` is the
local slope (zero at isolated points), the approximating sets are measurable and both infima are
`⊤` for an empty class. The certificate composes the identification of the relaxed lower content
with the bounded-support perimeter and the identification of the Definition 3.3 relaxation with
the same perimeter.

`upper` gives the same identity for the relaxed upper content, which together with the certificate
is the second clause of the paper's Lemma 2.1. These are equalities of relaxation infima; no
pointwise identity between Minkowski content and perimeter of an individual set is claimed.
-/

noncomputable section

open MeasureTheory Filter FunctionalInequalities FunctionalInequalities.KLS

namespace Solutions.ThmRelaxedMinkowskiContentPerimeter

variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]

/-- ADMG Theorem 3.6: under a Borel measure finite on bounded Borel sets, the relaxed lower
Minkowski content of a measurable finite-mass set equals its Definition 3.3 perimeter. -/
theorem certificate (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    MetricBV.relaxedMinkowskiContent ν B = MetricBV.lipschitzRelaxation ν B :=
  (MetricBV.relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded ν hν hB hνB).trans
    (MetricBV.lipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB).symm

/-- The relaxed upper Minkowski content equals the same Definition 3.3 perimeter. -/
theorem upper (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    MetricBV.relaxedUpperMinkowskiContent ν B = MetricBV.lipschitzRelaxation ν B :=
  (MetricBV.relaxedUpperMinkowskiContent_eq_perimeter_of_finite_on_bounded ν hν hB hνB).trans
    (MetricBV.lipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB).symm

/-- Both sides written as the unfolded infima of the paper. -/
example (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    (⨅ A : MetricBV.MinkowskiApproximatingSequence ν B,
        liminf (fun n => Isoperimetry.minkowskiContent ν (A.1 n)) atTop) =
      ⨅ f : MetricBV.LipschitzApproximatingSequence ν B,
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  certificate ν hν hB hνB

/-- Lemma 2.1, second clause, at the paper's standing measure scope. -/
example (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    MetricBV.relaxedMinkowskiContent ν B = MetricBV.relaxedUpperMinkowskiContent ν B :=
  (certificate ν hν hB hνB).trans (upper ν hν hB hνB).symm

/-- Typed application: every finite Borel measure is finite on bounded Borel sets. -/
example (ν : Measure V) [IsFiniteMeasure ν] {B : Set V} (hB : MeasurableSet B) :
    MetricBV.relaxedMinkowskiContent ν B = MetricBV.lipschitzRelaxation ν B :=
  certificate ν (fun s _ _ => measure_lt_top ν s) hB (measure_lt_top ν B)

/-- Typed application: Lebesgue measure on a Euclidean space, an infinite measure. -/
example (n : ℕ) {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B)
    (hνB : (volume : Measure (EuclideanSpace ℝ (Fin n))) B < ⊤) :
    MetricBV.relaxedMinkowskiContent volume B = MetricBV.lipschitzRelaxation volume B :=
  certificate volume (fun _ hs _ => hs.measure_lt_top) hB hνB

/--
info: 'Solutions.ThmRelaxedMinkowskiContentPerimeter.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmRelaxedMinkowskiContentPerimeter.certificate

/--
info: 'Solutions.ThmRelaxedMinkowskiContentPerimeter.upper'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmRelaxedMinkowskiContentPerimeter.upper

/--
info: 'FunctionalInequalities.KLS.MetricBV.relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.MetricBV.relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded

/--
info: 'FunctionalInequalities.KLS.MetricBV.lipschitzRelaxation_eq_perimeter_of_measure_lt_top'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.MetricBV.lipschitzRelaxation_eq_perimeter_of_measure_lt_top

end Solutions.ThmRelaxedMinkowskiContentPerimeter

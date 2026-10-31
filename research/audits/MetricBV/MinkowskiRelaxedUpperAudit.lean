module

public import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Independent full-signature clients for the identity: the relaxed upper Minkowski content over
the existing measurable approximating class equals the metric BV perimeter.  Checks: both
inequalities and the identity for an arbitrary target; equality with the relaxed lower content
and the termwise order between them; the `⊤` and `0` characterizations; the empty class (relaxed
upper content `⊤`, infinite perimeter); the constant-sequence bound by the upper content of a
measurable set; the bound by a convergent sequence of the class; the empty set, the full set and
a measurable null set (perimeter `0`, hence relaxed upper content `0`); the exact infinite
boundary; and the uniform law on `[0, 1]` with the null target `{0}`.  Not claimed: pointwise
equality of the upper content and the perimeter, Cheeger-quotient identifications. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace MinkowskiRelaxedUpperAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem identity (ν : ProbabilityMeasure V) (B : Set V) :
    relaxedUpperMinkowskiContent (ν : Measure V) B = perimeter (ν : Measure V) B :=
  relaxedUpperMinkowskiContent_eq_perimeter (ν : Measure V) B

theorem bothInequalities (ν : ProbabilityMeasure V) (B : Set V) :
    perimeter (ν : Measure V) B ≤ relaxedUpperMinkowskiContent (ν : Measure V) B ∧
      relaxedUpperMinkowskiContent (ν : Measure V) B ≤ perimeter (ν : Measure V) B :=
  ⟨perimeter_le_relaxedUpperMinkowskiContent (ν : Measure V) B,
    relaxedUpperMinkowskiContent_le_perimeter (ν : Measure V) B⟩

theorem lowerAndUpperRelaxations (ν : ProbabilityMeasure V) (B : Set V) :
    relaxedMinkowskiContent (ν : Measure V) B ≤ relaxedUpperMinkowskiContent (ν : Measure V) B ∧
      relaxedUpperMinkowskiContent (ν : Measure V) B = relaxedMinkowskiContent (ν : Measure V) B :=
  ⟨relaxedMinkowskiContent_le_relaxedUpperMinkowskiContent (ν : Measure V) B,
    relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent (ν : Measure V) B⟩

omit [BorelSpace V] in
/-- The definition is over the same class: any member bounds the relaxed upper content. -/
theorem memberBound (ν : ProbabilityMeasure V) (B : Set V)
    (A : MinkowskiApproximatingSequence (ν : Measure V) B) :
    relaxedUpperMinkowskiContent (ν : Measure V) B ≤
      liminf (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (A.1 n)) atTop :=
  relaxedUpperMinkowskiContent_le_liminf (ν : Measure V) B A

theorem topAndZero (ν : ProbabilityMeasure V) (B : Set V) :
    (relaxedUpperMinkowskiContent (ν : Measure V) B = ⊤ ↔ perimeter (ν : Measure V) B = ⊤) ∧
      (relaxedUpperMinkowskiContent (ν : Measure V) B = 0 ↔ perimeter (ν : Measure V) B = 0) :=
  ⟨relaxedUpperMinkowskiContent_eq_top_iff (ν : Measure V) B,
    relaxedUpperMinkowskiContent_eq_zero_iff (ν : Measure V) B⟩

/-- Empty class: relaxed upper content `⊤` and infinite perimeter (conditional on emptiness; no
empty class is constructed). -/
theorem emptyClass (ν : ProbabilityMeasure V) (B : Set V)
    [IsEmpty (MinkowskiApproximatingSequence (ν : Measure V) B)] :
    relaxedUpperMinkowskiContent (ν : Measure V) B = ⊤ ∧ perimeter (ν : Measure V) B = ⊤ :=
  ⟨relaxedUpperMinkowskiContent_eq_top_of_isEmpty (ν : Measure V) B,
    perimeter_eq_top_of_isEmpty (ν : Measure V) B⟩

/--
Constant sequence: the relaxed upper content of a measurable set is at most its upper content,
hence so is the perimeter. -/
theorem constantSequence (ν : ProbabilityMeasure V) {B : Set V} (hB : MeasurableSet B) :
    relaxedUpperMinkowskiContent (ν : Measure V) B ≤
        Isoperimetry.upperMinkowskiContent (ν : Measure V) B ∧
      perimeter (ν : Measure V) B ≤ Isoperimetry.upperMinkowskiContent (ν : Measure V) B :=
  ⟨relaxedUpperMinkowskiContent_le_upperMinkowskiContent (ν : Measure V) hB,
    (relaxedUpperMinkowskiContent_eq_perimeter (ν : Measure V) B) ▸
      relaxedUpperMinkowskiContent_le_upperMinkowskiContent (ν : Measure V) hB⟩

theorem convergentSequence (ν : ProbabilityMeasure V) {B : Set V} {A : ℕ → Set V}
    (hA : ∀ n, MeasurableSet (A n))
    (hconv :
      Tendsto
        (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V))
        atTop (𝓝 0))
    {c : ENNReal}
    (hlim :
      Tendsto (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (A n)) atTop (𝓝 c)) :
    relaxedUpperMinkowskiContent (ν : Measure V) B ≤ c ∧ perimeter (ν : Measure V) B ≤ c :=
  ⟨relaxedUpperMinkowskiContent_le_of_tendsto (ν : Measure V) hA hconv hlim,
    (relaxedUpperMinkowskiContent_eq_perimeter (ν : Measure V) B) ▸
      relaxedUpperMinkowskiContent_le_of_tendsto (ν : Measure V) hA hconv hlim⟩

/-- The upper recovery sets realize the infimum at finite perimeter. -/
theorem realizedByRecovery (ν : ProbabilityMeasure V) {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) :
    liminf
        (fun n =>
          Isoperimetry.upperMinkowskiContent (ν : Measure V)
            (upperRecoverySet (ν : Measure V) hB n))
        atTop =
      relaxedUpperMinkowskiContent (ν : Measure V) B := by
  rw [relaxedUpperMinkowskiContent_eq_perimeter]
  exact (tendsto_upperMinkowskiContent_upperRecoverySet (ν : Measure V) hB).liminf_eq

theorem emptySet (ν : ProbabilityMeasure V) :
    relaxedUpperMinkowskiContent (ν : Measure V) (∅ : Set V) = 0 := by
  rw [relaxedUpperMinkowskiContent_eq_perimeter, perimeter_empty]

theorem fullSet (ν : ProbabilityMeasure V) :
    relaxedUpperMinkowskiContent (ν : Measure V) (univ : Set V) = 0 := by
  rw [relaxedUpperMinkowskiContent_eq_perimeter]
  have := perimeter_compl_of_isFiniteMeasure (ν : Measure V) (∅ : Set V)
  rwa [compl_empty, perimeter_empty] at this

/-- A measurable `ν`-null set: relaxed upper content `0`, through the constant zero test
sequence (client-local computation of the perimeter). -/
theorem nullSet (ν : ProbabilityMeasure V) {B : Set V} (hB : MeasurableSet B)
    (h0 : (ν : Measure V) B = 0) : relaxedUpperMinkowskiContent (ν : Measure V) B = 0 := by
  rw [relaxedUpperMinkowskiContent_eq_perimeter]
  have hdist : indicatorDistance (ν : Measure V) Test.zero B = 0 := by
    have hpt : ∀ x, ‖(Test.zero : Test V) x - B.indicator (1 : V → ℝ) x‖ₑ =
        B.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      intro x
      by_cases hx : x ∈ B
      · simp [Test.zero, hx]
      · simp [Test.zero, hx]
    unfold indicatorDistance
    simp_rw [hpt]
    rw [lintegral_indicator hB, setLIntegral_const, one_mul, h0]
  refine le_antisymm ?_ bot_le
  have h := perimeter_le_sequence (ν : Measure V) B ⟨fun _ => Test.zero, by simp [hdist]⟩
  simpa using h

/-- The exact infinite boundary through the identity: at infinite perimeter every member of the
class has `liminf` of upper contents `⊤`. -/
theorem infiniteBoundary (ν : ProbabilityMeasure V) {B : Set V}
    (hB : perimeter (ν : Measure V) B = ⊤) (A : MinkowskiApproximatingSequence (ν : Measure V) B) :
    liminf (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (A.1 n)) atTop = ⊤ :=
  top_le_iff.mp (hB ▸ (perimeter_le_relaxedUpperMinkowskiContent (ν : Measure V) B).trans
    (relaxedUpperMinkowskiContent_le_liminf (ν : Measure V) B A))

/-! ### The uniform law on `[0, 1]` with the null target `{0}` -/

def uniformInterval : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Icc 0 1), ⟨by simp⟩⟩

theorem uniform_singleton : (uniformInterval : Measure ℝ) {0} = 0 := by
  simp only [uniformInterval, ProbabilityMeasure.coe_mk]
  rw [Measure.restrict_apply (measurableSet_singleton 0)]
  exact measure_mono_null inter_subset_left (Real.volume_singleton)

theorem uniformNullTarget :
    relaxedUpperMinkowskiContent (uniformInterval : Measure ℝ) {0} = 0 ∧
      relaxedUpperMinkowskiContent (uniformInterval : Measure ℝ) {0} =
        relaxedMinkowskiContent (uniformInterval : Measure ℝ) {0} :=
  ⟨nullSet uniformInterval (measurableSet_singleton 0) uniform_singleton,
    relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent (uniformInterval : Measure ℝ) {0}⟩

#print axioms identity
#print axioms bothInequalities
#print axioms lowerAndUpperRelaxations
#print axioms memberBound
#print axioms topAndZero
#print axioms emptyClass
#print axioms constantSequence
#print axioms convergentSequence
#print axioms realizedByRecovery
#print axioms emptySet
#print axioms fullSet
#print axioms nullSet
#print axioms infiniteBoundary
#print axioms uniformNullTarget

end MinkowskiRelaxedUpperAudit

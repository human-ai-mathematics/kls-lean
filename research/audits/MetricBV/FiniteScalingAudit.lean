import FunctionalInequalities.Analysis.MetricBV.Scaling
import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Independent full-signature clients for the content chain at finite Borel measures, scaling of
costs, indicator distances, approximating classes, perimeter and both contents by a nonnegative
real scalar, the zero measure, the exact infinite-perimeter branch under scaling, normalization
of a finite nonzero measure, the probability instances through the coercion, a non-unit-mass atom
and the empty/full sets.  Scalars are `ℝ≥0` (finite by type); the zero scalar is treated
separately where the statement needs `c ≠ 0`.  Not claimed: the finite-measure recovery and
relaxed identities, infinite total mass. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace MetricBVFiniteScalingAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV
open FunctionalInequalities.KLS.Isoperimetry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The chain at a finite Borel measure (no probability normalization). -/
theorem finiteSignatures (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} (hB : MeasurableSet B) :
    perimeter ν B ≤ minkowskiContent ν B ∧ minkowskiContent ν B ≤ upperMinkowskiContent ν B ∧
      (∫⁻ s in Ioo 0 1, upperMinkowskiContent ν (thickening s B) ≤
        ν (thickening 1 B) - ν B) ∧
      relaxedMinkowskiContent ν B ≤ relaxedUpperMinkowskiContent ν B ∧
      perimeter ν B ≤ relaxedUpperMinkowskiContent ν B :=
  ⟨perimeter_le_minkowskiContent ν hB, minkowskiContent_le_upperMinkowskiContent ν B,
    setLIntegral_upperMinkowskiContent_thickening_le ν B 1,
    relaxedMinkowskiContent_le_relaxedUpperMinkowskiContent ν B,
    perimeter_le_relaxedUpperMinkowskiContent ν B⟩

/-- Every scaling law at a nonzero nonnegative real scalar, for an arbitrary measure and set. -/
theorem scaling (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure X) (B : Set X) (f : Test X) :
    cost (c • ν) f = c * cost ν f ∧
      indicatorDistance (c • ν) f B = c * indicatorDistance ν f B ∧
      perimeter (c • ν) B = c * perimeter ν B ∧
      minkowskiContent (c • ν) B = c * minkowskiContent ν B ∧
      upperMinkowskiContent (c • ν) B = c * upperMinkowskiContent ν B ∧
      relaxedMinkowskiContent (c • ν) B = c * relaxedMinkowskiContent ν B ∧
      relaxedUpperMinkowskiContent (c • ν) B = c * relaxedUpperMinkowskiContent ν B ∧
      ∀ s, thickeningMass (c • ν) B s = c * thickeningMass ν B s :=
  ⟨cost_smul c ν f, indicatorDistance_smul c ν f B, perimeter_smul c hc ν B,
    minkowskiContent_smul c ν B, upperMinkowskiContent_smul c ν B,
    relaxedMinkowskiContent_smul c hc ν B, relaxedUpperMinkowskiContent_smul c hc ν B,
    thickeningMass_smul c ν B⟩

/-- The approximating classes transport in both directions (`c ≠ 0` for the inverse). -/
def transportBV (c : ℝ≥0) {ν : Measure X} {B : Set X} (f : ApproximatingSequence ν B) :
    ApproximatingSequence (c • ν) B := f.smul c
def transportBVInv {c : ℝ≥0} (hc : c ≠ 0) {ν : Measure X} {B : Set X}
    (f : ApproximatingSequence (c • ν) B) : ApproximatingSequence ν B := f.smulInv hc
def transportMink (c : ℝ≥0) {ν : Measure X} {B : Set X} (A : MinkowskiApproximatingSequence ν B) :
    MinkowskiApproximatingSequence (c • ν) B := A.smul c
def transportMinkInv {c : ℝ≥0} (hc : c ≠ 0) {ν : Measure X} {B : Set X}
    (A : MinkowskiApproximatingSequence (c • ν) B) : MinkowskiApproximatingSequence ν B :=
  A.smulInv hc

/-- The transported sequences keep their terms. -/
theorem transportTerms (c : ℝ≥0) (hc : c ≠ 0) {ν : Measure X} {B : Set X}
    (f : ApproximatingSequence ν B) (A : MinkowskiApproximatingSequence ν B) :
    (transportBV c f).1 = f.1 ∧ (transportBVInv hc (transportBV c f)).1 = f.1 ∧
      (transportMink c A).1 = A.1 ∧ (transportMinkInv hc (transportMink c A)).1 = A.1 :=
  ⟨rfl, rfl, rfl, rfl⟩

omit [BorelSpace X] in
/-- The zero scalar: both contents of `0 • ν` vanish (the scaling laws hold at `c = 0`), while
the perimeter law is stated for `c ≠ 0` only; the zero measure itself is treated below. -/
theorem zeroScalar (ν : Measure X) (B : Set X) :
    minkowskiContent ((0 : ℝ≥0) • ν) B = 0 ∧ upperMinkowskiContent ((0 : ℝ≥0) • ν) B = 0 := by
  constructor
  · rw [minkowskiContent_smul]; simp
  · rw [upperMinkowskiContent_smul]; simp

/-- The zero measure: all quantities vanish for every set and test. -/
theorem zeroMeasure (B : Set X) (f : Test X) :
    cost (0 : Measure X) f = 0 ∧ indicatorDistance (0 : Measure X) f B = 0 ∧
      perimeter (0 : Measure X) B = 0 ∧ minkowskiContent (0 : Measure X) B = 0 ∧
      upperMinkowskiContent (0 : Measure X) B = 0 ∧
      relaxedMinkowskiContent (0 : Measure X) B = 0 ∧
      relaxedUpperMinkowskiContent (0 : Measure X) B = 0 ∧
      ∀ s, thickeningMass (0 : Measure X) B s = 0 :=
  ⟨cost_zero_measure f, indicatorDistance_zero_measure f B, perimeter_zero_measure B,
    minkowskiContent_zero_measure B, upperMinkowskiContent_zero_measure B,
    relaxedMinkowskiContent_zero_measure B, relaxedUpperMinkowskiContent_zero_measure B,
    thickeningMass_zero_measure B⟩

/-- The exact infinite branch: infinite perimeter stays infinite under a nonzero scalar, and
finite perimeter stays finite. -/
theorem infiniteBranch (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure X) (B : Set X) :
    (perimeter ν B = ⊤ → perimeter (c • ν) B = ⊤) ∧
      (perimeter ν B < ⊤ → perimeter (c • ν) B < ⊤) := by
  have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [perimeter_smul c hc, h, ENNReal.mul_top hc']
  · rw [perimeter_smul c hc]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top h

/-- Normalization of a finite nonzero measure, with the perimeter and both contents expressed
through the probability normalization. -/
theorem normalization (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ ≠ 0) (B : Set X) :
    ∃ (c : ℝ≥0) (ν : ProbabilityMeasure X), c ≠ 0 ∧ μ = c • (ν : Measure X) ∧
      perimeter μ B = c * perimeter (ν : Measure X) B ∧
      minkowskiContent μ B = c * minkowskiContent (ν : Measure X) B ∧
      relaxedUpperMinkowskiContent μ B = c * relaxedUpperMinkowskiContent (ν : Measure X) B := by
  obtain ⟨c, ν, hc, hμc⟩ := exists_probability_smul μ hμ
  refine ⟨c, ν, hc, hμc, ?_, ?_, ?_⟩
  · rw [hμc, perimeter_smul c hc]
  · rw [hμc, minkowskiContent_smul]
  · rw [hμc, relaxedUpperMinkowskiContent_smul c hc]

/-- The probability statements at probability laws (through the coercion), including the
probability-only radius-mass bound. -/
theorem probabilityInstances (ν : ProbabilityMeasure X) (B : Set X) :
    relaxedUpperMinkowskiContent (ν : Measure X) B = perimeter (ν : Measure X) B ∧
      relaxedMinkowskiContent (ν : Measure X) B = perimeter (ν : Measure X) B ∧
      minkowskiContent ν B ≤ upperMinkowskiContent ν B ∧
      thickeningMass (ν : Measure X) B 1 ≤ 1 :=
  ⟨relaxedUpperMinkowskiContent_eq_perimeter (ν : Measure X) B,
    relaxedMinkowskiContent_eq_perimeter (ν : Measure X) B,
    minkowskiContent_le_upperMinkowskiContent (ν : Measure X) B,
    thickeningMass_le_one (ν : Measure X) B 1⟩

/-- Empty and full sets for a finite measure (complement symmetry) and under scaling. -/
theorem emptyAndFull (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure X) [IsFiniteMeasure ν] :
    perimeter (c • ν) (∅ : Set X) = 0 ∧ perimeter (c • ν) (univ : Set X) = 0 ∧
      perimeter ν (univ : Set X) = 0 := by
  have huniv : perimeter ν (univ : Set X) = 0 := by
    have := perimeter_compl_of_isFiniteMeasure ν (∅ : Set X)
    rwa [compl_empty, perimeter_empty] at this
  refine ⟨perimeter_empty _, ?_, huniv⟩
  rw [perimeter_smul c hc, huniv, mul_zero]

/-- A non-unit-mass atom: `2 • dirac x₀` has total mass `2`; the singleton has zero perimeter and
zero contents (zero increments of the atom, scaled). -/
theorem doubleAtom (x₀ : X) :
    ((2 : ℝ≥0) • Measure.dirac x₀) univ = 2 ∧
      perimeter ((2 : ℝ≥0) • Measure.dirac x₀) {x₀} = 0 ∧
      minkowskiContent ((2 : ℝ≥0) • Measure.dirac x₀) {x₀} = 0 ∧
      upperMinkowskiContent ((2 : ℝ≥0) • Measure.dirac x₀) {x₀} = 0 := by
  have hup : upperMinkowskiContent (Measure.dirac x₀) {x₀} = 0 :=
    upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (Measure.dirac x₀) fun r _ => by
      rw [Measure.dirac_apply_of_mem (mem_singleton x₀)]
      exact prob_le_one
  have hlow : minkowskiContent (Measure.dirac x₀) {x₀} = 0 :=
    le_antisymm ((minkowskiContent_le_upperMinkowskiContent _ _).trans_eq hup) bot_le
  have hper : perimeter (Measure.dirac x₀) {x₀} = 0 :=
    le_antisymm ((perimeter_le_minkowskiContent _ isClosed_singleton.measurableSet).trans_eq hlow)
      bot_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Measure.smul_apply, ENNReal.smul_def]
  · rw [perimeter_smul 2 two_ne_zero, hper, mul_zero]
  · rw [minkowskiContent_smul, hlow, mul_zero]
  · rw [upperMinkowskiContent_smul, hup, mul_zero]

#print axioms finiteSignatures
#print axioms scaling
#print axioms transportTerms
#print axioms zeroScalar
#print axioms zeroMeasure
#print axioms infiniteBranch
#print axioms normalization
#print axioms probabilityInstances
#print axioms emptyAndFull
#print axioms doubleAtom

end MetricBVFiniteScalingAudit

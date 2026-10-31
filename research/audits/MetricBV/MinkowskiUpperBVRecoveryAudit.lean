module

public import FunctionalInequalities.KLS.Geometry.Perimeter.UpperMinkowskiRecovery

/-! Independent full-signature clients for the upper Minkowski recovery of the metric BV
perimeter.  Checks: the recovery for an arbitrary target of finite perimeter (measurable
sets, indicator `L¹(ν)` convergence, upper contents tending to the perimeter); the explicit
recovery sets with their step bounds; termwise finiteness of the lower content of every lower
recovery set from the explicit quantitative bound; the thickening step lemma; the diagonal error
bound; the lower bound `perimeter ≤ liminf` of upper contents for every measurable `L¹`-convergent
sequence and every target; the exact infinite boundary (`liminf = ⊤` at infinite perimeter); the
empty set, the full set, a measurable null set and zero perimeter (contents tending to `0`); and
the uniform law on `[0, 1]` with the null target `{0}`.  Not claimed: any relaxation identity,
pointwise equality of contents and perimeter, recovery at infinite perimeter. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace MinkowskiUpperBVRecoveryAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

/-- The recovery for an arbitrary (not necessarily measurable) target of finite perimeter. -/
theorem recovery (ν : ProbabilityMeasure V) {B : Set V} (hB : perimeter (ν : Measure V) B < ⊤) :
    ∃ U : ℕ → Set V, (∀ n, MeasurableSet (U n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (U n)) atTop
        (𝓝 (perimeter (ν : Measure V) B)) :=
  exists_upperMinkowskiRecovery (ν : Measure V) hB

/-- The explicit sets: open, measurable, positive radii, step bounds and both limits. -/
theorem explicitSets (ν : ProbabilityMeasure V) {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) :
    (∀ n, 0 < upperRecoveryRadius (ν : Measure V) hB n) ∧
      (∀ n, IsOpen (upperRecoverySet (ν : Measure V) hB n)) ∧
        (∀ n, MeasurableSet (upperRecoverySet (ν : Measure V) hB n)) ∧
          (∀ n,
              Isoperimetry.upperMinkowskiContent (ν : Measure V)
                  (upperRecoverySet (ν : Measure V) hB n) ≤
                Isoperimetry.minkowskiContent (ν : Measure V)
                    (minkowskiRecoverySet (ν : Measure V) hB n) +
                  ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
            Tendsto
                (fun n =>
                  ∫⁻ x,
                    ‖(upperRecoverySet (ν : Measure V) hB n).indicator (1 : V → ℝ) x -
                        B.indicator 1 x‖ₑ ∂(ν : Measure V))
                atTop (𝓝 0) ∧
              Tendsto
                (fun n =>
                  Isoperimetry.upperMinkowskiContent (ν : Measure V)
                    (upperRecoverySet (ν : Measure V) hB n))
                atTop (𝓝 (perimeter (ν : Measure V) B)) :=
  ⟨upperRecoveryRadius_pos (ν : Measure V) hB, isOpen_upperRecoverySet (ν : Measure V) hB,
    measurableSet_upperRecoverySet (ν : Measure V) hB,
    upperMinkowskiContent_upperRecoverySet_le (ν : Measure V) hB,
    tendsto_indicator_upperRecoverySet (ν : Measure V) hB,
    tendsto_upperMinkowskiContent_upperRecoverySet (ν : Measure V) hB⟩

/-- Termwise finiteness of the lower contents of the lower recovery sets, from the explicit
quantitative bound. -/
theorem termwiseFiniteness (ν : ProbabilityMeasure V) {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) (n : ℕ) :
    Isoperimetry.minkowskiContent (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n) ≠ ⊤ :=
  minkowskiContent_minkowskiRecoverySet_ne_top (ν : Measure V) hB n

/-- The thickening step with prescribed slack: a radius whose thickening is `L¹`-close to `A`, with
upper content at most the lower content of `A` plus the slack. -/
theorem step (ν : ProbabilityMeasure V) {A : Set V} (hA : MeasurableSet A)
    (hfin : Isoperimetry.minkowskiContent (ν : Measure V) A ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℝ, 0 < s ∧
      ∫⁻ x, ‖(thickening s A).indicator (1 : V → ℝ) x - A.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        ENNReal.ofReal δ ∧
      Isoperimetry.upperMinkowskiContent (ν : Measure V) (thickening s A) ≤
        Isoperimetry.minkowskiContent (ν : Measure V) A + ENNReal.ofReal δ :=
  exists_thickening_approx (ν : Measure V) hA hfin hδ

/-- The diagonal error bound through the `n`-th lower recovery set. -/
theorem diagonalError (ν : ProbabilityMeasure V) {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) (n : ℕ) :
    ∫⁻ x,
        ‖(upperRecoverySet (ν : Measure V) hB n).indicator (1 : V → ℝ) x -
            B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) +
        ∫⁻ x,
          ‖(minkowskiRecoverySet (ν : Measure V) hB n).indicator (1 : V → ℝ) x -
              B.indicator 1 x‖ₑ ∂(ν : Measure V) :=
  lintegral_enorm_upperRecoverySet_sub_le (ν : Measure V) hB n

/-- Lower bound for every target and every measurable `L¹`-convergent sequence (no finiteness). -/
theorem lowerBound (ν : ProbabilityMeasure V) (B : Set V) {A : ℕ → Set V}
    (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    perimeter (ν : Measure V) B ≤
      liminf (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (A n)) atTop :=
  perimeter_le_liminf_upperMinkowskiContent (ν : Measure V) B hA hconv

/-- The exact infinite boundary. -/
theorem infiniteBoundary (ν : ProbabilityMeasure V) {B : Set V}
    (hB : perimeter (ν : Measure V) B = ⊤) {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    liminf (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (A n)) atTop = ⊤ :=
  liminf_upperMinkowskiContent_eq_top_of_perimeter_eq_top (ν : Measure V) hB hA hconv

/-- Zero perimeter: the recovered upper contents tend to `0`. -/
theorem zeroPerimeter (ν : ProbabilityMeasure V) {B : Set V}
    (h0 : perimeter (ν : Measure V) B = 0) :
    ∃ U : ℕ → Set V, (∀ n, MeasurableSet (U n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (U n)) atTop (𝓝 0) := by
  have hB : perimeter (ν : Measure V) B < ⊤ := h0 ▸ ENNReal.zero_lt_top
  obtain ⟨U, hU, hL1, hc⟩ := exists_upperMinkowskiRecovery (ν : Measure V) hB
  exact ⟨U, hU, hL1, h0 ▸ hc⟩

theorem emptySet (ν : ProbabilityMeasure V) :
    ∃ U : ℕ → Set V, (∀ n, MeasurableSet (U n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : V → ℝ) x - (∅ : Set V).indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (U n)) atTop (𝓝 0) :=
  zeroPerimeter ν (perimeter_empty (ν : Measure V))

/-- The full set has zero perimeter for a probability law (complement symmetry). -/
theorem fullSet (ν : ProbabilityMeasure V) :
    perimeter (ν : Measure V) (univ : Set V) = 0 ∧
      ∃ U : ℕ → Set V,
        (∀ n, MeasurableSet (U n)) ∧
          Tendsto
              (fun n =>
                ∫⁻ x,
                  ‖(U n).indicator (1 : V → ℝ) x -
                      (univ : Set V).indicator 1 x‖ₑ ∂(ν : Measure V))
              atTop (𝓝 0) ∧
            Tendsto (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (U n)) atTop
              (𝓝 0) := by
  have h0 : perimeter (ν : Measure V) (univ : Set V) = 0 := by
    have := perimeter_compl_of_isFiniteMeasure (ν : Measure V) (∅ : Set V)
    rwa [compl_empty, perimeter_empty] at this
  exact ⟨h0, zeroPerimeter ν h0⟩

/-- A measurable `ν`-null set has zero perimeter: the constant zero test sequence has zero cost
and indicator distance `ν B = 0`. -/
theorem perimeter_eq_zero_of_measure_eq_zero (ν : ProbabilityMeasure V) {B : Set V}
    (hB : MeasurableSet B) (h0 : (ν : Measure V) B = 0) : perimeter (ν : Measure V) B = 0 := by
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
  have h := perimeter_le_sequence (ν : Measure V) B
    ⟨fun _ => Test.zero, by simp [hdist]⟩
  simpa using h

theorem nullSet (ν : ProbabilityMeasure V) {B : Set V} (hB : MeasurableSet B)
    (h0 : (ν : Measure V) B = 0) :
    ∃ U : ℕ → Set V, (∀ n, MeasurableSet (U n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => Isoperimetry.upperMinkowskiContent (ν : Measure V) (U n)) atTop (𝓝 0) :=
  zeroPerimeter ν (perimeter_eq_zero_of_measure_eq_zero ν hB h0)

/-! ### The uniform law on `[0, 1]` with the null target `{0}` -/

def uniformInterval : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Icc 0 1), ⟨by simp⟩⟩

theorem uniform_singleton : (uniformInterval : Measure ℝ) {0} = 0 := by
  simp only [uniformInterval, ProbabilityMeasure.coe_mk]
  rw [Measure.restrict_apply (measurableSet_singleton 0)]
  exact measure_mono_null inter_subset_left (Real.volume_singleton)

theorem uniformNullTarget :
    perimeter (uniformInterval : Measure ℝ) {0} = 0 ∧
      ∃ U : ℕ → Set ℝ,
        (∀ n, MeasurableSet (U n)) ∧
          Tendsto
              (fun n =>
                ∫⁻ x,
                  ‖(U n).indicator (1 : ℝ → ℝ) x -
                      ({0} : Set ℝ).indicator 1 x‖ₑ ∂(uniformInterval : Measure ℝ))
              atTop (𝓝 0) ∧
            Tendsto
              (fun n => Isoperimetry.upperMinkowskiContent (uniformInterval : Measure ℝ) (U n))
              atTop (𝓝 0) :=
  ⟨perimeter_eq_zero_of_measure_eq_zero uniformInterval (measurableSet_singleton 0)
      uniform_singleton,
    nullSet uniformInterval (measurableSet_singleton 0) uniform_singleton⟩

#print axioms recovery
#print axioms explicitSets
#print axioms termwiseFiniteness
#print axioms step
#print axioms diagonalError
#print axioms lowerBound
#print axioms infiniteBoundary
#print axioms zeroPerimeter
#print axioms emptySet
#print axioms fullSet
#print axioms nullSet
#print axioms uniformNullTarget

end MinkowskiUpperBVRecoveryAudit

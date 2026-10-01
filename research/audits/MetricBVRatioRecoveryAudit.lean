import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski

/-! Independent full-signature clients for mass and symmetric-ratio recovery: mass continuity
under set-indicator `L¹` convergence, the eventual mass window `(0, 1)` of the Minkowski recovery
sets and convergence of their symmetric quotients `content / min (mass, 1 - mass)` and
`perimeter / min (mass, 1 - mass)` (the quotients of `minkowskiConstant` and
`symmetricConstant`). Boundary checks: mass `0` (masses converge, the ratio theorem is not
applied), the half-mass case without a branch, a concrete two-atom law `(δ₀ + δ₁)/2` on `ℝ` with
`B = Iic (1/2)` satisfying all hypotheses, and the zero-dimensional space, where no mass window
exists. No half-mass constraint on the recovery sets and no Cheeger equality is asserted. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVRatioRecoveryAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

theorem massBound {α : Type*} [MeasurableSpace α] (ν : Measure α) {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ν A ≤ ν B + ∫⁻ x, ‖A.indicator (1 : α → ℝ) x - B.indicator 1 x‖ₑ ∂ν := by
  exact measure_le_add_lintegral_indicator_sub ν hA hB

theorem massContinuity {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    {A : ℕ → Set α} {B : Set α} (hA : ∀ n, MeasurableSet (A n)) (hB : MeasurableSet B)
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : α → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    Tendsto (fun n => ν (A n)) atTop (𝓝 (ν B)) := by
  exact tendsto_measure_of_tendsto_indicator ν hA hB hconv

theorem ratioLemma {ι : Type*} {l : Filter ι} {a m : ι → ℝ≥0∞} {a₀ m₀ : ℝ≥0∞}
    (ha : Tendsto a l (𝓝 a₀)) (hm : Tendsto m l (𝓝 m₀)) (h0 : 0 < m₀) (h1 : m₀ < 1) :
    Tendsto (fun i => a i / min (m i) (1 - m i)) l (𝓝 (a₀ / min m₀ (1 - m₀))) := by
  exact tendsto_div_min_one_sub ha hm h0 h1

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem recoveryMass (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B)
    (hB : perimeter (ν : Measure V) B < ⊤) :
    Tendsto (fun n => (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n)) atTop
      (𝓝 ((ν : Measure V) B)) := by
  exact tendsto_measure_minkowskiRecoverySet ν hBm hB

theorem massWindow (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B)
    (hB : perimeter (ν : Measure V) B < ⊤) (h0 : 0 < (ν : Measure V) B)
    (h1 : (ν : Measure V) B < 1) :
    ∀ᶠ n in atTop, (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n) ∈ Set.Ioo 0 1 := by
  exact eventually_measure_minkowskiRecoverySet_mem_Ioo ν hBm hB h0 h1

theorem contentRatio (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B)
    (hB : perimeter (ν : Measure V) B < ⊤) (h0 : 0 < (ν : Measure V) B)
    (h1 : (ν : Measure V) B < 1) :
    Tendsto (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n) /
        min ((ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))
          (1 - (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))) atTop
      (𝓝 (perimeter (ν : Measure V) B / min ((ν : Measure V) B) (1 - (ν : Measure V) B))) := by
  exact tendsto_minkowskiContent_div_min_minkowskiRecoverySet ν hBm hB h0 h1

theorem perimeterRatio (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B)
    (hB : perimeter (ν : Measure V) B < ⊤) (h0 : 0 < (ν : Measure V) B)
    (h1 : (ν : Measure V) B < 1) :
    Tendsto (fun n => perimeter (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n) /
        min ((ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))
          (1 - (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))) atTop
      (𝓝 (perimeter (ν : Measure V) B / min ((ν : Measure V) B) (1 - (ν : Measure V) B))) := by
  exact tendsto_perimeter_div_min_minkowskiRecoverySet ν hBm hB h0 h1

/-- Half mass, without a branch: the limit is `perimeter B / 2⁻¹`. -/
theorem halfMass (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B)
    (hB : perimeter (ν : Measure V) B < ⊤) (hhalf : (ν : Measure V) B = 2⁻¹) :
    Tendsto (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n) /
        min ((ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))
          (1 - (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))) atTop
      (𝓝 (perimeter (ν : Measure V) B / 2⁻¹)) := by
  have h := tendsto_minkowskiContent_div_min_minkowskiRecoverySet ν hBm hB
    (by rw [hhalf]; exact ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
    (by rw [hhalf]; exact ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  rwa [hhalf, ENNReal.one_sub_inv_two, min_self] at h

/-- Mass `0`: the masses still converge (to `0`), but the ratio theorem is not applicable. -/
theorem massZero (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B)
    (hB : perimeter (ν : Measure V) B < ⊤) (hnull : (ν : Measure V) B = 0) :
    Tendsto (fun n => (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n)) atTop (𝓝 0) :=
  hnull ▸ tendsto_measure_minkowskiRecoverySet ν hBm hB

/-- Dimension zero: every mass is `0` or `1`, so no mass window exists. -/
theorem zeroDimensionalNoWindow (ν : ProbabilityMeasure (Fin 0 → ℝ)) (B : Set (Fin 0 → ℝ)) :
    ¬ (0 < (ν : Measure (Fin 0 → ℝ)) B ∧ (ν : Measure (Fin 0 → ℝ)) B < 1) := by
  rintro ⟨h0, h1⟩
  rcases Set.eq_empty_or_nonempty B with rfl | ⟨x, hx⟩
  · simp at h0
  · have hB : B = Set.univ := Set.eq_univ_of_forall fun y => by
      rwa [Subsingleton.elim y x]
    rw [hB, measure_univ] at h1
    exact lt_irrefl _ h1

/-- The two-atom law `(δ₀ + δ₁)/2` on `ℝ`. -/
def twoAtom : ProbabilityMeasure ℝ :=
  ⟨(2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1), ⟨by
    simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩⟩

theorem twoAtom_apply {S : Set ℝ} (hS : MeasurableSet S) (h0 : (0 : ℝ) ∈ S) (h1 : (1 : ℝ) ∉ S) :
    (twoAtom : Measure ℝ) S = 2⁻¹ := by
  change (((2 : ℝ≥0∞)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac 1) : Measure ℝ) S) =
    (2 : ℝ≥0∞)⁻¹
  simp [Measure.dirac_apply' _ hS, h0, h1]

/-- A concrete instance of all hypotheses: `B = Iic (1/2)` under the two-atom law has mass `1/2`
and zero Minkowski content (small thickenings miss the atom at `1`), hence zero BV perimeter, and
the symmetric content quotients of its recovery sets converge to `0`. -/
theorem twoAtomHalfLine :
    ∃ hB : perimeter (twoAtom : Measure ℝ) (Set.Iic (1 / 2)) < ⊤,
      MeasurableSet (Set.Iic (1 / 2 : ℝ)) ∧ (twoAtom : Measure ℝ) (Set.Iic (1 / 2)) = 2⁻¹ ∧
      Tendsto (fun n => Isoperimetry.minkowskiContent (twoAtom : Measure ℝ)
          (minkowskiRecoverySet (twoAtom : Measure ℝ) hB n) /
        min ((twoAtom : Measure ℝ) (minkowskiRecoverySet (twoAtom : Measure ℝ) hB n))
          (1 - (twoAtom : Measure ℝ) (minkowskiRecoverySet (twoAtom : Measure ℝ) hB n))) atTop (𝓝 0) := by
  set B : Set ℝ := Set.Iic (1 / 2) with hBdef
  have hBm : MeasurableSet B := measurableSet_Iic
  have hmass : (twoAtom : Measure ℝ) B = 2⁻¹ :=
    twoAtom_apply hBm (by norm_num [hBdef]) (by norm_num [hBdef])
  have hc : Isoperimetry.minkowskiContent (twoAtom : Measure ℝ) B = 0 := by
    refine le_antisymm ?_ bot_le
    refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with r hr
    have hsub : Metric.thickening r B ⊆ Set.Iio (1 / 2 + r) := fun x hx => by
      obtain ⟨z, hz, hdz⟩ := Metric.mem_thickening_iff.mp hx
      have hz' : z ≤ 1 / 2 := hz
      have := (abs_lt.mp (by simpa [Real.dist_eq] using hdz)).2
      show x < 1 / 2 + r
      linarith
    have hthick : (twoAtom : Measure ℝ) (Metric.thickening r B) ≤ 2⁻¹ :=
      (measure_mono hsub).trans (twoAtom_apply measurableSet_Iio
        (by simp only [Set.mem_Iio]; linarith [hr.1])
        (by simp only [Set.mem_Iio, not_lt]; linarith [hr.2])).le
    rw [hmass, tsub_eq_zero_of_le hthick, ENNReal.zero_div]
  have hp : perimeter (twoAtom : Measure ℝ) B = 0 :=
    le_antisymm ((perimeter_le_minkowskiContent (twoAtom : Measure ℝ) hBm).trans_eq hc) bot_le
  have hB : perimeter (twoAtom : Measure ℝ) B < ⊤ := hp ▸ ENNReal.zero_lt_top
  refine ⟨hB, hBm, hmass, ?_⟩
  have h := tendsto_minkowskiContent_div_min_minkowskiRecoverySet twoAtom hBm hB
    (by rw [hmass]; exact ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
    (by rw [hmass]; exact ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  rwa [hp, ENNReal.zero_div] at h

#print axioms massBound
#print axioms massContinuity
#print axioms ratioLemma
#print axioms recoveryMass
#print axioms massWindow
#print axioms contentRatio
#print axioms perimeterRatio
#print axioms halfMass
#print axioms massZero
#print axioms zeroDimensionalNoWindow
#print axioms twoAtomHalfLine

end MetricBVRatioRecoveryAudit

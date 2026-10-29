import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Metric-only full-signature clients for the Minkowski content chain on an arbitrary
metric space with a Borel probability measure (no normed-group, vector-space or dimension
structure).  Checks: the open-ball majorant (lower semicontinuous, measurable, near-neighbour
witness); the local-slope Minkowski coarea inequality; the one-sided bridge `perimeter ≤ lower
content ≤ upper content`; the integrated upper-content bound and the small-radius selection; the
recovery of measurable sets of finite lower content; the lower and upper recoveries of every set
of finite perimeter; both relaxed identities; the empty, full, zero, atomic and infinite
boundaries; and a non-vector-space example, the natural numbers with their discrete metric and a
Dirac law.  The probability scope is narrower than the locally finite scope of
Ambrosio--Di Marino--Gigli; nothing is claimed for finite or locally finite measures. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace MinkowskiMetricChainAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV
open FunctionalInequalities.KLS.Isoperimetry

section Generic

variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]

/-- The open-ball majorant on a metric space. -/
theorem openBallMajorant {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) {r : ℝ} (hr : 0 < r) :
    LowerSemicontinuous (openBallSup u r) ∧ Measurable (openBallSup u r) ∧
      (∀ x, u x ≤ openBallSup u r x ∧ openBallSup u r x ≤ u x + K * r) ∧
      ∀ t, thickening r {x : V | t ≤ u x} ⊆
        {x : V | u x < t ∧ t ≤ openBallSup u r x} ∪ {x : V | t ≤ u x} :=
  ⟨lowerSemicontinuous_openBallSup hK hr, measurable_openBallSup hK hr,
    fun x => ⟨le_openBallSup hK hr x, openBallSup_le_add hK hr x⟩,
    fun t => thickening_superlevel_subset_openBallSup hK r t⟩

/-- Minkowski coarea inequality with the local slope on a metric space. -/
theorem coarea (ν : ProbabilityMeasure V) {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent (ν : Measure V) {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply u x ∂(ν : Measure V) :=
  lintegral_minkowskiContent_superlevel_le_localSlope (ν : Measure V) hK

/-- `perimeter ≤ lower content ≤ upper content` for measurable sets. -/
theorem bridge (ν : ProbabilityMeasure V) {B : Set V} (hB : MeasurableSet B) :
    perimeter (ν : Measure V) B ≤ minkowskiContent (ν : Measure V) B ∧
      minkowskiContent (ν : Measure V) B ≤ upperMinkowskiContent (ν : Measure V) B :=
  ⟨perimeter_le_minkowskiContent (ν : Measure V) hB, minkowskiContent_le_upperMinkowskiContent (ν : Measure V) B⟩

omit [BorelSpace V] in
/-- Integrated upper-content bound and small-radius selection on a metric space. -/
theorem integratedAndSelection (ν : ProbabilityMeasure V) (B : Set V) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) :
    (∫⁻ s in Ioo 0 r, upperMinkowskiContent (ν : Measure V) (thickening s B) ≤
        (ν : Measure V) (thickening r B) - (ν : Measure V) B) ∧
      ∃ s ∈ Ioo 0 r, upperMinkowskiContent (ν : Measure V) (thickening s B) ≤
        ((ν : Measure V) (thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r +
          ENNReal.ofReal ε :=
  ⟨setLIntegral_upperMinkowskiContent_thickening_le (ν : Measure V) B r,
    exists_upperMinkowskiContent_thickening_le_div_add (ν : Measure V) B hr hε⟩

/-- Recovery of a measurable set of finite lower content on a metric space. -/
theorem finiteContentRecovery (ν : ProbabilityMeasure V) {B : Set V} (hB : MeasurableSet B)
    (hfin : minkowskiContent (ν : Measure V) B ≠ ⊤) :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      (∀ n, MeasurableSet (thickening (s n) B)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(thickening (s n) B).indicator (1 : V → ℝ) x -
        B.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) ∧
      limsup (fun n => upperMinkowskiContent (ν : Measure V) (thickening (s n) B)) atTop ≤
        minkowskiContent (ν : Measure V) B :=
  exists_upperRecovery (ν : Measure V) B hB hfin

/-- Lower and upper recoveries of every set of finite perimeter on a metric space. -/
theorem recoveries (ν : ProbabilityMeasure V) {B : Set V} (hB : perimeter (ν : Measure V) B < ⊤) :
    (∃ A : ℕ → Set V, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => minkowskiContent (ν : Measure V) (A n)) atTop (𝓝 (perimeter (ν : Measure V) B))) ∧
    ∃ U : ℕ → Set V, (∀ n, MeasurableSet (U n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => upperMinkowskiContent (ν : Measure V) (U n)) atTop (𝓝 (perimeter (ν : Measure V) B)) :=
  ⟨exists_minkowskiRecovery (ν : Measure V) hB, exists_upperMinkowskiRecovery (ν : Measure V) hB⟩

/-- Both relaxed identities for every set on a metric space. -/
theorem relaxedIdentities (ν : ProbabilityMeasure V) (B : Set V) :
    relaxedMinkowskiContent (ν : Measure V) B = perimeter (ν : Measure V) B ∧
      relaxedUpperMinkowskiContent (ν : Measure V) B = perimeter (ν : Measure V) B ∧
      relaxedUpperMinkowskiContent (ν : Measure V) B = relaxedMinkowskiContent (ν : Measure V) B :=
  ⟨relaxedMinkowskiContent_eq_perimeter (ν : Measure V) B, relaxedUpperMinkowskiContent_eq_perimeter (ν : Measure V) B,
    relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent (ν : Measure V) B⟩

theorem emptyAndFull (ν : ProbabilityMeasure V) :
    relaxedUpperMinkowskiContent (ν : Measure V) (∅ : Set V) = 0 ∧
      relaxedUpperMinkowskiContent (ν : Measure V) (univ : Set V) = 0 ∧ minkowskiContent (ν : Measure V) (∅ : Set V) = 0 := by
  refine ⟨?_, ?_, minkowskiContent_empty (ν : Measure V)⟩
  · rw [relaxedUpperMinkowskiContent_eq_perimeter, perimeter_empty]
  · rw [relaxedUpperMinkowskiContent_eq_perimeter]
    have := perimeter_compl_of_isFiniteMeasure (ν : Measure V) (∅ : Set V)
    rwa [compl_empty, perimeter_empty] at this

/-- Zero and infinite boundaries through the identities. -/
theorem zeroAndInfinite (ν : ProbabilityMeasure V) (B : Set V) :
    (relaxedUpperMinkowskiContent (ν : Measure V) B = 0 ↔ perimeter (ν : Measure V) B = 0) ∧
      (relaxedUpperMinkowskiContent (ν : Measure V) B = ⊤ ↔ perimeter (ν : Measure V) B = ⊤) ∧
      (perimeter (ν : Measure V) B = ⊤ → ∀ A : MinkowskiApproximatingSequence (ν : Measure V) B,
        liminf (fun n => upperMinkowskiContent (ν : Measure V) (A.1 n)) atTop = ⊤) :=
  ⟨relaxedUpperMinkowskiContent_eq_zero_iff (ν : Measure V) B, relaxedUpperMinkowskiContent_eq_top_iff (ν : Measure V) B,
    fun hB A => top_le_iff.mp (hB ▸ (perimeter_le_relaxedUpperMinkowskiContent (ν : Measure V) B).trans
      (relaxedUpperMinkowskiContent_le_liminf (ν : Measure V) B A))⟩

/-- An atom: the Dirac law at a point of an arbitrary metric space. Every positive thickening of
the point carries no extra mass, so both contents and the perimeter vanish. -/
theorem atom (x₀ : V) :
    let ν : ProbabilityMeasure V := ⟨Measure.dirac x₀, inferInstance⟩
    minkowskiContent (ν : Measure V) {x₀} = 0 ∧ upperMinkowskiContent (ν : Measure V) {x₀} = 0 ∧
      perimeter (ν : Measure V) {x₀} = 0 := by
  intro ν
  have h1 : (ν : Measure V) {x₀} = 1 := by
    simp [ν, Measure.dirac_apply_of_mem (mem_singleton x₀)]
  have hup : upperMinkowskiContent (ν : Measure V) {x₀} = 0 :=
    upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (ν : Measure V) fun r _ => by
      rw [h1]; exact prob_le_one
  have hlow : minkowskiContent (ν : Measure V) {x₀} = 0 :=
    le_antisymm ((minkowskiContent_le_upperMinkowskiContent (ν : Measure V) _).trans_eq hup) bot_le
  refine ⟨hlow, hup, le_antisymm ?_ bot_le⟩
  exact (perimeter_le_minkowskiContent (ν : Measure V) isClosed_singleton.measurableSet).trans_eq hlow

end Generic

/-! ### A non-vector-space example: the natural numbers with their discrete metric -/

/-- The Dirac law at `0` on `ℕ` (`dist m n = |m - n|`, not a vector space). -/
def natDirac : ProbabilityMeasure ℕ := ⟨Measure.dirac 0, inferInstance⟩

theorem natExample :
    minkowskiContent (natDirac : Measure ℕ) {0} = 0 ∧ upperMinkowskiContent (natDirac : Measure ℕ) {0} = 0 ∧
      perimeter (natDirac : Measure ℕ) {0} = 0 ∧
      relaxedUpperMinkowskiContent (natDirac : Measure ℕ) {0} = relaxedMinkowskiContent (natDirac : Measure ℕ) {0} ∧
      ∃ U : ℕ → Set ℕ, (∀ n, MeasurableSet (U n)) ∧
        Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : ℕ → ℝ) x - ({0} : Set ℕ).indicator 1 x‖ₑ
          ∂(natDirac : Measure ℕ)) atTop (𝓝 0) ∧
        Tendsto (fun n => upperMinkowskiContent (natDirac : Measure ℕ) (U n)) atTop (𝓝 0) := by
  obtain ⟨hlow, hup, hper⟩ := atom (V := ℕ) 0
  refine ⟨hlow, hup, hper, relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent _ _, ?_⟩
  obtain ⟨U, hU, hL1, hc⟩ := exists_upperMinkowskiRecovery (natDirac : Measure ℕ) (hper ▸ ENNReal.zero_lt_top)
  exact ⟨U, hU, hL1, hper ▸ hc⟩

/-- On `ℕ` the unit thickening of `{0}` is `{0}` itself: a genuinely non-vector-space feature
(the open unit ball is a single point). -/
theorem nat_thickening_one : thickening (1 : ℝ) ({0} : Set ℕ) = {0} := by
  rw [thickening_singleton]
  ext n
  simp only [mem_ball, mem_singleton_iff, Nat.dist_eq, Nat.cast_zero, sub_zero, Nat.abs_cast]
  exact_mod_cast Nat.lt_one_iff

#print axioms openBallMajorant
#print axioms coarea
#print axioms bridge
#print axioms integratedAndSelection
#print axioms finiteContentRecovery
#print axioms recoveries
#print axioms relaxedIdentities
#print axioms emptyAndFull
#print axioms zeroAndInfinite
#print axioms atom
#print axioms natExample
#print axioms nat_thickening_one

end MinkowskiMetricChainAudit

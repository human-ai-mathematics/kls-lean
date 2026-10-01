import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Independent full-signature clients for phase 29 / Stage B of the finite-measure run: the lower
and upper Minkowski recoveries with actual indicator `L¹(ν)` convergence and both relaxed
identities, for a finite Borel measure on an arbitrary metric space and an arbitrary target.
Cases: the lower bound along every measurable `L¹`-convergent sequence; the infinite-perimeter
branch (relaxed contents `⊤`, every member of the class has `liminf` `⊤`) and the empty class
(conditional; none is constructed); the zero measure with an arbitrary target and the empty
carrier; a non-unit atom on the non-vector metric space `ℕ`; empty and full sets; scaled
recovery consistency; and the old probability instances.  Source: Ambrosio--Di Marino--Gigli,
Theorem 3.6 in the finite-total-mass, global-`L¹` form; the locally finite scope of the article is
not claimed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace MetricBVFiniteRecoveryAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV
open FunctionalInequalities.KLS.Isoperimetry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Lower recovery at a finite Borel measure for an arbitrary target of finite perimeter. -/
theorem lowerRecovery (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} (hB : perimeter ν B < ⊤) :
    ∃ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν) atTop (𝓝 0) ∧
      Tendsto (fun n => minkowskiContent ν (A n)) atTop (𝓝 (perimeter ν B)) :=
  exists_minkowskiRecovery ν hB

/-- Upper recovery at a finite Borel measure for an arbitrary target of finite perimeter. -/
theorem upperRecovery (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} (hB : perimeter ν B < ⊤) :
    ∃ U : ℕ → Set X, (∀ n, MeasurableSet (U n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν) atTop (𝓝 0) ∧
      Tendsto (fun n => upperMinkowskiContent ν (U n)) atTop (𝓝 (perimeter ν B)) :=
  exists_upperMinkowskiRecovery ν hB

/-- Both relaxed identities and their equality, for every target. -/
theorem relaxedIdentities (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    relaxedMinkowskiContent ν B = perimeter ν B ∧
      relaxedUpperMinkowskiContent ν B = perimeter ν B ∧
      relaxedUpperMinkowskiContent ν B = relaxedMinkowskiContent ν B :=
  ⟨relaxedMinkowskiContent_eq_perimeter ν B, relaxedUpperMinkowskiContent_eq_perimeter ν B,
    relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent ν B⟩

/-- The lower bound along every measurable `L¹`-convergent sequence (lower and upper contents). -/
theorem lowerBoundAnySequence (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) {A : ℕ → Set X}
    (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => minkowskiContent ν (A n)) atTop ∧
      perimeter ν B ≤ liminf (fun n => upperMinkowskiContent ν (A n)) atTop :=
  ⟨perimeter_le_liminf_minkowskiContent ν hA hconv,
    perimeter_le_liminf_upperMinkowskiContent ν B hA hconv⟩

/-- The infinite-perimeter branch and the empty class. -/
theorem infiniteBranch (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    (relaxedMinkowskiContent ν B = ⊤ ↔ perimeter ν B = ⊤) ∧
      (relaxedUpperMinkowskiContent ν B = ⊤ ↔ perimeter ν B = ⊤) ∧
      (perimeter ν B = ⊤ → ∀ A : MinkowskiApproximatingSequence ν B,
        liminf (fun n => upperMinkowskiContent ν (A.1 n)) atTop = ⊤) ∧
      (IsEmpty (MinkowskiApproximatingSequence ν B) → perimeter ν B = ⊤) := by
  refine ⟨by rw [relaxedMinkowskiContent_eq_perimeter], relaxedUpperMinkowskiContent_eq_top_iff ν B,
    fun hB A => ?_, fun h => perimeter_eq_top_of_isEmpty ν B⟩
  exact top_le_iff.mp (hB ▸ (perimeter_le_relaxedUpperMinkowskiContent ν B).trans
    (relaxedUpperMinkowskiContent_le_liminf ν B A))

/-- The zero measure with an arbitrary target: zero perimeter, both relaxed contents zero, and the
recoveries apply (their contents tend to `0`). -/
theorem zeroMeasureArbitraryTarget (B : Set X) :
    perimeter (0 : Measure X) B = 0 ∧ relaxedMinkowskiContent (0 : Measure X) B = 0 ∧
      relaxedUpperMinkowskiContent (0 : Measure X) B = 0 ∧
      (∃ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) ∧
        Tendsto (fun n => minkowskiContent (0 : Measure X) (A n)) atTop (𝓝 0)) ∧
      ∃ U : ℕ → Set X, (∀ n, MeasurableSet (U n)) ∧
        Tendsto (fun n => upperMinkowskiContent (0 : Measure X) (U n)) atTop (𝓝 0) := by
  have h0 : perimeter (0 : Measure X) B = 0 := perimeter_zero_measure B
  have hB : perimeter (0 : Measure X) B < ⊤ := h0 ▸ ENNReal.zero_lt_top
  obtain ⟨A, hA, -, hAc⟩ := exists_minkowskiRecovery (0 : Measure X) hB
  obtain ⟨U, hU, -, hUc⟩ := exists_upperMinkowskiRecovery (0 : Measure X) hB
  exact ⟨h0, relaxedMinkowskiContent_zero_measure B, relaxedUpperMinkowskiContent_zero_measure B,
    ⟨A, hA, h0 ▸ hAc⟩, ⟨U, hU, h0 ▸ hUc⟩⟩

/-- The empty carrier: every measure is zero, so the identities hold with all values `0`. -/
theorem emptyCarrier (ν : Measure Empty) (B : Set Empty) :
    ν = 0 ∧ perimeter ν B = 0 ∧ relaxedUpperMinkowskiContent ν B = perimeter ν B := by
  have h := Measure.eq_zero_of_isEmpty ν
  subst h
  exact ⟨rfl, perimeter_zero_measure B, relaxedUpperMinkowskiContent_eq_perimeter 0 B⟩

/-- Empty and full sets at a finite measure. -/
theorem emptyAndFull (ν : Measure X) [IsFiniteMeasure ν] :
    perimeter ν (∅ : Set X) = 0 ∧ perimeter ν (univ : Set X) = 0 ∧
      relaxedUpperMinkowskiContent ν (∅ : Set X) = 0 ∧
      relaxedUpperMinkowskiContent ν (univ : Set X) = 0 := by
  have huniv : perimeter ν (univ : Set X) = 0 := by
    have := perimeter_compl_of_isFiniteMeasure ν (∅ : Set X)
    rwa [compl_empty, perimeter_empty] at this
  exact ⟨perimeter_empty ν, huniv, by rw [relaxedUpperMinkowskiContent_eq_perimeter, perimeter_empty],
    by rw [relaxedUpperMinkowskiContent_eq_perimeter, huniv]⟩

/-- Scaled recovery consistency: the upper recovery for `c • ν` recovers `c * perimeter ν B`, with
indicator convergence in `L¹(c • ν)`. -/
theorem scaledRecovery (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure X) [IsFiniteMeasure ν] {B : Set X}
    (hB : perimeter ν B < ⊤) :
    ∃ U : ℕ → Set X, (∀ n, MeasurableSet (U n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂(c • ν))
        atTop (𝓝 0) ∧
      Tendsto (fun n => upperMinkowskiContent (c • ν) (U n)) atTop (𝓝 (c * perimeter ν B)) := by
  have hB' : perimeter (c • ν) B < ⊤ := by
    rw [perimeter_smul c hc]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hB
  obtain ⟨U, hU, hL1, hc'⟩ := exists_upperMinkowskiRecovery (c • ν) hB'
  exact ⟨U, hU, hL1, by rwa [perimeter_smul c hc] at hc'⟩

/-- Old probability instances through the coercion (regression). -/
theorem probabilityInstances (ν : ProbabilityMeasure X) {B : Set X}
    (hB : perimeter (ν : Measure X) B < ⊤) :
    (∃ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => minkowskiContent (ν : Measure X) (A n)) atTop
        (𝓝 (perimeter (ν : Measure X) B))) ∧
      relaxedMinkowskiContent (ν : Measure X) B = perimeter (ν : Measure X) B := by
  obtain ⟨A, hA, -, hAc⟩ := exists_minkowskiRecovery (ν : Measure X) hB
  exact ⟨⟨A, hA, hAc⟩, relaxedMinkowskiContent_eq_perimeter (ν : Measure X) B⟩

/-! ### A non-unit atom on `ℕ` (a metric space that is not a vector space) -/

/-- The measure `3 • dirac 0` on `ℕ`, of total mass `3`. -/
def natAtom : Measure ℕ := (3 : ℝ≥0) • Measure.dirac 0

instance : IsFiniteMeasure natAtom := by
  unfold natAtom
  infer_instance

theorem natAtom_mass : natAtom univ = 3 := by
  simp [natAtom, Measure.smul_apply, ENNReal.smul_def]

/-- The singleton `{0}` under `natAtom`: zero perimeter and contents (zero increments of the
atom, scaled), so both recoveries and both identities hold with value `0`. -/
theorem natAtomSingleton :
    perimeter natAtom {0} = 0 ∧ minkowskiContent natAtom {0} = 0 ∧
      upperMinkowskiContent natAtom {0} = 0 ∧
      relaxedUpperMinkowskiContent natAtom {0} = relaxedMinkowskiContent natAtom {0} ∧
      ∃ U : ℕ → Set ℕ, (∀ n, MeasurableSet (U n)) ∧
        Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : ℕ → ℝ) x - ({0} : Set ℕ).indicator 1 x‖ₑ
          ∂natAtom) atTop (𝓝 0) ∧
        Tendsto (fun n => upperMinkowskiContent natAtom (U n)) atTop (𝓝 0) := by
  have hup : upperMinkowskiContent (Measure.dirac (0 : ℕ)) {0} = 0 :=
    upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (Measure.dirac 0) fun r _ => by
      rw [Measure.dirac_apply_of_mem (mem_singleton 0)]
      exact prob_le_one
  have hlow : minkowskiContent (Measure.dirac (0 : ℕ)) {0} = 0 :=
    le_antisymm ((minkowskiContent_le_upperMinkowskiContent _ _).trans_eq hup) bot_le
  have hper : perimeter (Measure.dirac (0 : ℕ)) {0} = 0 :=
    le_antisymm ((perimeter_le_minkowskiContent _ (measurableSet_singleton 0)).trans_eq hlow) bot_le
  have hper3 : perimeter natAtom {0} = 0 := by
    unfold natAtom; rw [perimeter_smul 3 three_ne_zero, hper, mul_zero]
  have hB : perimeter natAtom {0} < ⊤ := hper3 ▸ ENNReal.zero_lt_top
  obtain ⟨U, hU, hL1, hc⟩ := exists_upperMinkowskiRecovery natAtom hB
  refine ⟨hper3, ?_, ?_, relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent natAtom {0},
    U, hU, hL1, hper3 ▸ hc⟩
  · unfold natAtom; rw [minkowskiContent_smul, hlow, mul_zero]
  · unfold natAtom; rw [upperMinkowskiContent_smul, hup, mul_zero]

#print axioms lowerRecovery
#print axioms upperRecovery
#print axioms relaxedIdentities
#print axioms lowerBoundAnySequence
#print axioms infiniteBranch
#print axioms zeroMeasureArbitraryTarget
#print axioms emptyCarrier
#print axioms emptyAndFull
#print axioms scaledRecovery
#print axioms probabilityInstances
#print axioms natAtom_mass
#print axioms natAtomSingleton

end MetricBVFiniteRecoveryAudit

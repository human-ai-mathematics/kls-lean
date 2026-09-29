import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski

/-! Independent full-signature clients for the one-sided bridge "metric BV perimeter ≤ outer
Minkowski content" for a probability law and a measurable set. Checks: the plateau-ramp
interface (Lipschitz bound, boundary-safe slope bound, zero slope on the closure), the empty set,
top content, the zero-dimensional coordinate space, the atom on the boundary of a half-line (where
the naive ramp would cost `1/r` but the content is zero), and the consequences of finite
content (finite perimeter, closure mass, a recovery sequence). One inequality only; no
identification of the two quantities or of their Cheeger infima. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace MetricBVMinkowskiAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem bridge (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B) :
    perimeter (ν : Measure V) B ≤ Isoperimetry.minkowskiContent ν B := by
  exact perimeter_le_minkowskiContent ν hBm

theorem rampLipschitz {X : Type*} [MetricSpace X] (B : Set X) {s t : ℝ} (hst : s < t) :
    LipschitzWith (Real.toNNReal (t - s)⁻¹) (plateauRamp B s t) := by
  exact lipschitzWith_plateauRamp B hst

theorem rampSlope {X : Type*} [MetricSpace X] (B : Set X) {s t : ℝ} (hst : s < t) (x : X) :
    FunctionalInequalities.Energy.LocalSlope.apply (plateauRamp B s t) x ≤
      ((fun y => Metric.infDist y B) ⁻¹' Set.Icc s t).indicator
        (fun _ => ENNReal.ofReal (t - s)⁻¹) x := by
  exact apply_plateauRamp_le B hst x

/-- Boundary safety: the plateau ramp has zero slope at every point of the closure of `B`. -/
theorem rampSlopeZeroOnClosure {X : Type*} [MetricSpace X] {B : Set X} (hB : B.Nonempty)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) {x : X} (hx : x ∈ closure B) :
    FunctionalInequalities.Energy.LocalSlope.apply (plateauRamp B s t) x = 0 := by
  have h0 : Metric.infDist x B = 0 := (Metric.mem_closure_iff_infDist_zero hB).mp hx
  have hnot : x ∉ (fun y => Metric.infDist y B) ⁻¹' Set.Icc s t := by
    simp only [Set.mem_preimage, Set.mem_Icc, h0, not_and, not_le]
    intro h
    exact absurd h (not_le.mpr hs)
  have h := apply_plateauRamp_le B hst x
  rw [Set.indicator_of_notMem hnot] at h
  exact le_antisymm h bot_le

theorem emptySet (ν : ProbabilityMeasure V) :
    perimeter (ν : Measure V) ∅ ≤ Isoperimetry.minkowskiContent ν ∅ := by
  exact perimeter_le_minkowskiContent ν MeasurableSet.empty

/-- Top content: the bound is trivial and consistent. -/
theorem topContent (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B)
    (h : Isoperimetry.minkowskiContent ν B = ⊤) :
    perimeter (ν : Measure V) B ≤ ⊤ := by
  exact h ▸ perimeter_le_minkowskiContent ν hBm

/-- The zero-dimensional coordinate space `Fin 0 → ℝ`. -/
theorem zeroDimensional (ν : ProbabilityMeasure (Fin 0 → ℝ))
    {B : Set (Fin 0 → ℝ)} (hBm : MeasurableSet B) :
    perimeter (ν : Measure (Fin 0 → ℝ)) B ≤ Isoperimetry.minkowskiContent ν B ∧
      perimeter (ν : Measure (Fin 0 → ℝ)) B = 0 := by
  exact ⟨perimeter_le_minkowskiContent ν hBm, perimeter_eq_zero_of_subsingleton _ _⟩

/-- An atom on the boundary of the half-line `[0, ∞)`: the Minkowski content is zero, so the
metric BV perimeter is zero, although the naive distance ramp has slope `1/r` at `0`. -/
theorem diracHalfLine :
    perimeter (Measure.dirac (0 : ℝ)) (Set.Ici 0) = 0 := by
  let ν : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩
  have h1 : (ν : Measure ℝ) (Set.Ici 0) = 1 := by
    simp [ν, Measure.dirac_apply_of_mem (Set.mem_Ici.2 le_rfl : (0 : ℝ) ∈ Set.Ici 0)]
  have hzero : ∀ r : ℝ, ((ν : Measure ℝ) (Metric.thickening r (Set.Ici 0)) -
      (ν : Measure ℝ) (Set.Ici 0)) / ENNReal.ofReal r = 0 := fun r => by
    rw [h1, tsub_eq_zero_of_le prob_le_one, ENNReal.zero_div]
  have hc : Isoperimetry.minkowskiContent ν (Set.Ici 0) = 0 := by
    unfold Isoperimetry.minkowskiContent
    simp only [hzero, liminf_const]
  have h := perimeter_le_minkowskiContent ν (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ)))
  rw [hc] at h
  exact le_antisymm h bot_le

/-- Finite content yields finite perimeter, no extra closure mass, and a recovery sequence. -/
theorem finiteContent (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B)
    (h : Isoperimetry.minkowskiContent ν B < ⊤) :
    perimeter (ν : Measure V) B < ⊤ ∧ (ν : Measure V) (closure B) = (ν : Measure V) B ∧
      ∃ g : ApproximatingSequence (ν : Measure V) B,
        Tendsto (fun n => cost (ν : Measure V) (g.1 n)) atTop
          (𝓝 (perimeter (ν : Measure V) B)) := by
  have hp := (perimeter_le_minkowskiContent ν hBm).trans_lt h
  exact ⟨hp, Isoperimetry.measure_closure_eq_of_minkowskiContent_ne_top ν h.ne,
    exists_recoverySequence _ B hp⟩

#print axioms bridge
#print axioms rampLipschitz
#print axioms rampSlope
#print axioms rampSlopeZeroOnClosure
#print axioms emptySet
#print axioms topContent
#print axioms zeroDimensional
#print axioms diracHalfLine
#print axioms finiteContent

end MetricBVMinkowskiAudit

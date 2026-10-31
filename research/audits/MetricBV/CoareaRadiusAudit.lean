module

public import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Strict clients for the full right-radius-liminf chain of ADMG Lemma 3.2.
The middle quantity uses the genuine open-ball supremum and original measure;
no fixed sequence of radii or finite-total-mass hypothesis replaces it. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology
namespace MetricBVCoareaRadiusAudit
open FunctionalInequalities
open FunctionalInequalities.KLS.Isoperimetry
open FunctionalInequalities.KLS.MetricBV
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem fullChain (ν : Measure X) {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu : ∀ x, 0 ≤ u x) {δ : ℝ} (hδ : 0 < δ)
    (hfin : ν (thickening δ {x | 0 < u x}) < ⊤) :
    (∫⁻ t in Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν) (𝓝[>] 0)) ∧
    (liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν) (𝓝[>] 0) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂ν) :=
  setLIntegral_minkowskiContent_superlevel_coarea_of_finite_neighborhood ν hK hu hδ hfin

theorem boundedPositive (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) (hu : ∀ x, 0 ≤ u x)
    (hb : Bornology.IsBounded {x | 0 < u x}) :
    ∫⁻ t in Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν) (𝓝[>] 0) :=
  (fullChain ν hK hu zero_lt_one (hν _ hb.thickening Metric.isOpen_thickening.measurableSet)).1

/-- The finite-measure filter theorem permits arbitrary signed Lipschitz functions. -/
theorem finiteRegression (ν : Measure X) [IsFiniteMeasure ν] {u : X → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) :
    (∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν) (𝓝[>] 0)) ∧
    (liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν) (𝓝[>] 0) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂ν) :=
  ⟨lintegral_minkowskiContent_superlevel_le_liminf_openBallSup ν hK,
    liminf_lintegral_openBallSup_le_localSlope ν hK⟩

theorem realVolumeTest (f : Test ℝ) (hf : ∀ x, 0 ≤ f x) :
    (volume : Measure ℝ) univ = ⊤ ∧
      (∫⁻ t in Ioi (0 : ℝ), minkowskiContent volume {x | t ≤ f x} ∂(volume : Measure ℝ) ≤
          liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup f r x - f x) / r) ∂volume)
            (𝓝[>] 0)) ∧
        (liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup f r x - f x) / r) ∂volume)
              (𝓝[>] 0) ≤
            cost volume f) ∧
          cost volume f < ⊤ := by
  obtain ⟨K, hK⟩ := f.lipschitz
  have hb : Bornology.IsBounded {x : ℝ | 0 < f x} :=
    f.boundedSupport.subset fun _ hx => ne_of_gt hx
  have h := fullChain volume hK hf zero_lt_one hb.thickening.measure_lt_top
  exact
    ⟨by simp, h.1, h.2,
      (cost_ne_top_of_support_measure volume f
          f.boundedSupport.closure.measure_lt_top.ne).lt_top⟩

theorem zeroFunction (ν : Measure X) :
    liminf
        (fun r : ℝ =>
          ∫⁻ x, ENNReal.ofReal ((openBallSup (fun _ : X => (0 : ℝ)) r x - 0) / r) ∂ν)
        (𝓝[>] 0) =
      0 := by
  have h :=
    fullChain ν (LipschitzWith.const 0) (fun _ => le_rfl) zero_lt_one
      (show ν (thickening 1 {_x : X | 0 < (0 : ℝ)}) < ⊤ by simp)
  exact
    le_antisymm (by simpa only [Energy.LocalSlope.apply_const, lintegral_zero] using h.2)
      zero_le

theorem constantFinite (ν : Measure X) [IsFiniteMeasure ν] (c : ℝ) :
    liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup (fun _ : X => c) r x - c) / r) ∂ν)
      (𝓝[>] 0) = 0 :=
  le_antisymm (by simpa only [Energy.LocalSlope.apply_const, lintegral_zero] using
    liminf_lintegral_openBallSup_le_localSlope ν (LipschitzWith.const c)) zero_le

omit [BorelSpace X] in
theorem zeroMeasure (u : X → ℝ) :
    liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂(0 : Measure X))
      (𝓝[>] 0) = 0 := by simp

theorem emptyCarrier (ν : Measure Empty) (u : Empty → ℝ) :
    liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν)
      (𝓝[>] 0) = 0 := by simp [Measure.eq_zero_of_isEmpty ν]

theorem lemmaTwoOne (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    (⨅ A : MinkowskiApproximatingSequence ν B,
      liminf (fun n => upperMinkowskiContent ν (A.1 n)) atTop) ≤ minkowskiContent ν B :=
  relaxedUpperMinkowskiContent_le_minkowskiContent_of_measure_lt_top ν hB hνB

#print axioms lintegral_minkowskiContent_superlevel_le_liminf_of_majorant
#print axioms lintegral_minkowskiContent_superlevel_le_liminf_openBallSup
#print axioms liminf_lintegral_openBallSup_le_localSlope
#print axioms setLIntegral_minkowskiContent_superlevel_coarea_of_finite_neighborhood
#print axioms relaxedUpperMinkowskiContent_le_minkowskiContent_of_measure_lt_top
#print axioms lemmaTwoOne
#print axioms fullChain
#print axioms boundedPositive
#print axioms finiteRegression
#print axioms realVolumeTest
#print axioms zeroFunction
#print axioms constantFinite
#print axioms zeroMeasure
#print axioms emptyCarrier
end MetricBVCoareaRadiusAudit

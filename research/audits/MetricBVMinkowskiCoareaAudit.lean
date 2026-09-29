import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski
import FunctionalInequalities.Energy.LocalSlope.Gradient
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent full-signature clients for the Minkowski coarea inequality with the actual local
slope (globally Lipschitz, no differentiability) and its metric BV specializations. Boundary
checks: constants, the zero-dimensional space, the unbounded identity on `ℝ` for an arbitrary
law, consistency with the `C¹` gradient theorem, and a set (the rationals under the standard
Gaussian law) with zero BV perimeter and infinite Minkowski content, so the pointwise reverse of
the phase-7 inequality is false and the integrated bounds here do not assert it. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVMinkowskiCoareaAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [NormedAddCommGroup V]

theorem growthBound (u : V → ℝ) (x : V) {r : ℕ → ℝ} (hrpos : ∀ n, 0 < r n)
    (hr0 : Tendsto r atTop (𝓝 0)) :
    limsup (fun n => ENNReal.ofReal ((Isoperimetry.ballSup u (r n) x - u x) / r n)) atTop
      ≤ FunctionalInequalities.Energy.LocalSlope.apply u x := by
  exact Isoperimetry.limsup_ofReal_ballSup_le_localSlope u x hrpos hr0

variable [MeasurableSpace V] [BorelSpace V]

theorem layerCake (ν : ProbabilityMeasure V) {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, Isoperimetry.minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, limsup (fun n : ℕ => ENNReal.ofReal
        ((Isoperimetry.ballSup u (1 / ((n : ℝ) + 1)) x - u x) / (1 / ((n : ℝ) + 1)))) atTop
        ∂(ν : Measure V) := by
  exact Isoperimetry.lintegral_minkowskiContent_superlevel_le_limsup ν hK

theorem slopeCoarea (ν : ProbabilityMeasure V) {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, Isoperimetry.minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply u x ∂(ν : Measure V) := by
  exact Isoperimetry.lintegral_minkowskiContent_superlevel_le_localSlope ν hK

theorem lipschitzPerimeter (ν : ProbabilityMeasure V) {u : V → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) :
    ∫⁻ t, perimeter (ν : Measure V) {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply u x ∂(ν : Measure V) := by
  exact lintegral_perimeter_superlevel_le_localSlope ν hK

theorem testContent (ν : ProbabilityMeasure V) (f : Test V) :
    ∫⁻ t, Isoperimetry.minkowskiContent ν {x | t ≤ f x} ∂(volume : Measure ℝ) ≤
      cost (ν : Measure V) f := by
  exact lintegral_minkowskiContent_superlevel_le_cost ν f

theorem testPerimeter (ν : ProbabilityMeasure V) (f : Test V) :
    ∫⁻ t, perimeter (ν : Measure V) {x | t ≤ f x} ∂(volume : Measure ℝ) ≤
      cost (ν : Measure V) f := by
  exact lintegral_perimeter_superlevel_le_cost ν f

/-- Constants: the superlevel sets are `∅` or the whole space, and the integral vanishes. -/
theorem constantFunction (ν : ProbabilityMeasure V) (c : ℝ) :
    ∫⁻ t, Isoperimetry.minkowskiContent ν {_x : V | t ≤ c} ∂(volume : Measure ℝ) = 0 := by
  have h := Isoperimetry.lintegral_minkowskiContent_superlevel_le_localSlope ν
    (LipschitzWith.const (α := V) c)
  simp only [FunctionalInequalities.Energy.LocalSlope.apply_const, lintegral_zero] at h
  exact le_antisymm h bot_le

/-- The zero-dimensional coordinate space: every Lipschitz function has zero slope. -/
theorem zeroDimensional (ν : ProbabilityMeasure (Fin 0 → ℝ)) {u : (Fin 0 → ℝ) → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) :
    ∫⁻ t, Isoperimetry.minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) = 0 := by
  have h := Isoperimetry.lintegral_minkowskiContent_superlevel_le_localSlope ν hK
  simp only [FunctionalInequalities.Energy.LocalSlope.apply_eq_zero_of_subsingleton,
    lintegral_zero] at h
  exact le_antisymm h bot_le

/-- The unbounded identity on `ℝ` (unbounded values and support) for an arbitrary law. -/
theorem identityLine (ν : ProbabilityMeasure ℝ) :
    ∫⁻ t, Isoperimetry.minkowskiContent ν {x : ℝ | t ≤ x} ∂(volume : Measure ℝ) ≤ 1 := by
  have hK : LipschitzWith 1 (fun x : ℝ => x) := LipschitzWith.id
  refine (Isoperimetry.lintegral_minkowskiContent_superlevel_le_localSlope ν hK).trans ?_
  calc ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply (fun x : ℝ => x) x ∂(ν : Measure ℝ)
      ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(ν : Measure ℝ) := lintegral_mono fun x => by
        simpa using FunctionalInequalities.Energy.LocalSlope.apply_le_of_lipschitzWith hK x
    _ = 1 := by simp

/-- Consistency with the `C¹` theorem: for a differentiable function the slope integral is the
gradient integral, so the new bound recovers `lintegral_minkowskiContent_superlevel_le`. -/
theorem c1Consistency {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] (ν : ProbabilityMeasure E) {u : E → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, Isoperimetry.minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure E) := by
  refine (Isoperimetry.lintegral_minkowskiContent_superlevel_le_localSlope ν hK).trans_eq ?_
  refine lintegral_congr fun x => ?_
  rw [FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient u x
    (hu.differentiable one_ne_zero x), ofReal_norm]

/-- The pointwise reverse of `perimeter ≤ minkowskiContent` fails: the rationals are a Gaussian
null set, hence of zero BV perimeter, while their closure is the whole line, so their Minkowski
content is infinite. -/
theorem pointwiseReverseFails :
    ∃ (ν : ProbabilityMeasure ℝ) (B : Set ℝ), MeasurableSet B ∧
      perimeter (ν : Measure ℝ) B = 0 ∧ Isoperimetry.minkowskiContent ν B = ⊤ := by
  let ν : ProbabilityMeasure ℝ := ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
  set B : Set ℝ := Set.range ((↑) : ℚ → ℝ) with hBdef
  have hBc : B.Countable := Set.countable_range _
  have hBm : MeasurableSet B := hBc.measurableSet
  have h0 : (ν : Measure ℝ) B = 0 :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero (hBc.measure_zero _)
  refine ⟨ν, B, hBm, ?_, ?_⟩
  · have hdist : ∫⁻ x, ‖(∅ : Set ℝ).indicator (1 : ℝ → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure ℝ) = 0 := by
      have hfun : (fun x => ‖(∅ : Set ℝ).indicator (1 : ℝ → ℝ) x - B.indicator 1 x‖ₑ) =
          B.indicator 1 := by
        funext x
        by_cases hx : x ∈ B <;> simp [hx]
      rw [hfun, lintegral_indicator_one hBm, h0]
    have h := perimeter_le_liminf_of_tendsto (ν : Measure ℝ) (Bn := fun _ => (∅ : Set ℝ))
      (B := B) (fun _ => MeasurableSet.empty) (by simp only [hdist]; exact tendsto_const_nhds)
    simp only [perimeter_empty, liminf_const] at h
    exact le_antisymm h bot_le
  · by_contra hne
    have hcl := Isoperimetry.measure_closure_eq_of_minkowskiContent_ne_top ν hne
    rw [hBdef, Rat.denseRange_cast.closure_range, ← hBdef, h0, measure_univ] at hcl
    exact one_ne_zero hcl

#print axioms growthBound
#print axioms layerCake
#print axioms slopeCoarea
#print axioms lipschitzPerimeter
#print axioms testContent
#print axioms testPerimeter
#print axioms constantFunction
#print axioms zeroDimensional
#print axioms identityLine
#print axioms c1Consistency
#print axioms pointwiseReverseFails

end MetricBVMinkowskiCoareaAudit

module

public import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
public import FunctionalInequalities.Energy.Euclidean.WeakDerivative
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Stability of the Cheeger test inequality

An abstract smooth-test bound controls the Minkowski infimum. This test formulation
allows passage through weak or setwise limits without asserting convergence of the
relative perimeter of individual domains.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff symmDiff BoundedContinuousFunction
namespace FunctionalInequalities.KLS.Isoperimetry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
private theorem weak_of_setwise (νn : ℕ → ProbabilityMeasure V) (ν : ProbabilityMeasure V)
    (hset :
      ∀ D : Set V,
        MeasurableSet D →
          Tendsto (fun n => (νn n : Measure V) D) atTop (𝓝 ((ν : Measure V) D))) :
    Tendsto νn atTop (𝓝 ν) := by
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  rw [(hset G hG.measurableSet).liminf_eq]

omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem gradient_lintegral_tendsto (νn : ℕ → ProbabilityMeasure V)
    (ν : ProbabilityMeasure V) (hweak : Tendsto νn atTop (𝓝 ν)) {u : V → ℝ}
    (hu : ContDiff ℝ ∞ u) {K : ℝ≥0} (hK : LipschitzWith K u) :
    Tendsto (fun n => ∫⁻ x, ‖gradient u x‖ₑ ∂(νn n : Measure V)) atTop
      (𝓝 (∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V))) := by
  let g : V →ᵇ ℝ≥0 :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => Real.toNNReal ‖gradient u x‖,
        continuous_real_toNNReal.comp
          ((Analysis.BakryEmery.continuous_gradient_of_contDiff hu (by decide)).norm)⟩
      (K : ℝ)
      (by
        intro x y
        change
          |(Real.toNNReal ‖gradient u x‖ : ℝ) - (Real.toNNReal ‖gradient u y‖ : ℝ)| ≤ (K : ℝ)
        rw [Real.coe_toNNReal _ (norm_nonneg _), Real.coe_toNNReal _ (norm_nonneg _)]
        have hx := Energy.Euclidean.LipschitzApproximation.norm_gradient_le_of_lipschitz hK x
        have hy := Energy.Euclidean.LipschitzApproximation.norm_gradient_le_of_lipschitz hK y
        have hx0 := norm_nonneg (gradient u x)
        have hy0 := norm_nonneg (gradient u y)
        exact abs_sub_le_iff.mpr ⟨by nlinarith, by nlinarith⟩)
  have h := (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hweak) g
  have hg (x : V) : (g x : ENNReal) = ‖gradient u x‖ₑ := by
    change (Real.toNNReal ‖gradient u x‖ : ENNReal) = ‖gradient u x‖ₑ
    simp [enorm_eq_nnnorm, nnnorm]
  simp_rw [hg] at h
  exact h

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
private theorem balance_lintegral_tendsto (νn : ℕ → ProbabilityMeasure V)
    (ν : ProbabilityMeasure V)
    (hset :
      ∀ D : Set V,
        MeasurableSet D → Tendsto (fun n => (νn n : Measure V) D) atTop (𝓝 ((ν : Measure V) D)))
    {u : V → ℝ} (hu : Continuous u) :
    Tendsto
      (fun n =>
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((νn n : Measure V) {x | t < u x}) (1 - (νn n : Measure V) {x | t < u x}))
      atTop
      (𝓝
        (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}))) := by
  apply
    tendsto_lintegral_filter_of_dominated_convergence (μ :=
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) (bound := fun _ => 1)
  · exact Filter.Eventually.of_forall fun n => (measurable_min_measure_superlevel (νn n) u)
  · exact
      Filter.Eventually.of_forall fun n =>
        Filter.Eventually.of_forall fun t => (min_le_left _ _).trans prob_le_one
  · simp [lintegral_const, Real.volume_Ioo]
  · exact
      Filter.Eventually.of_forall fun t => by
        have hm : MeasurableSet {x : V | t < u x} :=
          (measurableSet_lt measurable_const hu.measurable)
        have ht := hset _ hm
        have hsub :
          Tendsto (fun n => 1 - (νn n : Measure V) {x | t < u x}) atTop
            (𝓝 (1 - (ν : Measure V) {x | t < u x})) :=
          ENNReal.Tendsto.sub tendsto_const_nhds ht (Or.inl ENNReal.one_ne_top)
        exact ht.min hsub

/-- A finite uniform lower Cheeger bound survives setwise convergence of
probability laws with an absolutely continuous limit. -/
theorem le_minkowskiConstant_of_setwise_tendsto
    (νn : ℕ → ProbabilityMeasure V) (ν : ProbabilityMeasure V)
    (hac : (ν : Measure V) ≪ volume) (H : ℝ≥0∞) (hH : H ≠ ⊤)
    (hset : ∀ D : Set V, MeasurableSet D →
      Tendsto (fun n => (νn n : Measure V) D) atTop (𝓝 ((ν : Measure V) D)))
    (hbound : ∀ᶠ n in atTop, H ≤ minkowskiConstant (νn n)) :
    H ≤ minkowskiConstant ν := by
  have hweak := weak_of_setwise νn ν hset
  apply le_minkowskiConstant_of_smooth_test H hac
  intro u hu K hK hu01
  have hbal := balance_lintegral_tendsto νn ν hset hu.continuous
  have hgrad := gradient_lintegral_tendsto νn ν hweak hu hK
  have hmul := ENNReal.Tendsto.const_mul hbal (Or.inr hH)
  apply le_of_tendsto_of_tendsto hmul hgrad
  filter_upwards [hbound] with n hn
  calc
    H * (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      min ((νn n : Measure V) {x | t < u x})
        (1 - (νn n : Measure V) {x | t < u x}))
      ≤ minkowskiConstant (νn n) * (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((νn n : Measure V) {x | t < u x})
            (1 - (νn n : Measure V) {x | t < u x})) := mul_le_mul' hn le_rfl
    _ ≤ ∫⁻ x, ‖gradient u x‖ₑ ∂(νn n : Measure V) :=
      minkowskiConstant_mul_lintegral_min_superlevel_le (νn n)
        (hu.of_le (by decide)) hK hu01

end FunctionalInequalities.KLS.Isoperimetry

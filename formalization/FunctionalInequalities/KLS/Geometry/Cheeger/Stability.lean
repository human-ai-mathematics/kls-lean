import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.Energy.Euclidean.WeakDerivative
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Stability of the Cheeger test inequality

An abstract smooth-test bound controls the Minkowski infimum. This test formulation
allows passage through weak or setwise limits without asserting convergence of the
relative perimeter of individual domains.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff symmDiff BoundedContinuousFunction
namespace FunctionalInequalities.KLS.Isoperimetry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- A uniform coarea inequality on smooth Lipschitz tests bounds the actual
Minkowski Cheeger infimum, with no attainment or finite-content assumption. -/
theorem le_minkowskiConstant_of_smooth_test {ν : ProbabilityMeasure V} (H : ℝ≥0∞)
    (hac : (ν : Measure V) ≪ volume)
    (hTest : ∀ {u : V → ℝ}, ContDiff ℝ ∞ u →
      ∀ {K : ℝ≥0}, LipschitzWith K u →
      (∀ x, u x ∈ Set.Icc (0 : ℝ) 1) →
      H * (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        min ((ν : Measure V) {x | t < u x})
          (1 - (ν : Measure V) {x | t < u x})) ≤
        ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V)) :
    H ≤ minkowskiConstant ν := by
  classical
  simp only [minkowskiConstant]
  refine le_iInf fun B ↦ le_iInf fun hBm ↦ le_iInf fun hpos ↦ le_iInf fun hlt ↦ ?_
  have hm0 : min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≠ 0 :=
    ne_of_gt (lt_min hpos (tsub_pos_of_lt hlt))
  have hmtop : min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((min_le_left _ _).trans prob_le_one)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)]
  -- An infinite Minkowski content needs no argument.
  rcases eq_or_ne (minkowskiContent ν B) ⊤ with hc | hc
  · rw [hc]
    exact le_top
  have hcl : (ν : Measure V) (closure B) = (ν : Measure V) B :=
    measure_closure_eq_of_minkowskiContent_ne_top ν hc
  have hBne : B.Nonempty := nonempty_of_measure_ne_zero (ne_of_gt hpos)
  set e : ℝ → ℝ≥0∞ :=
    fun r ↦ (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B with hedef
  -- The single-radius estimate, with the error subtracted from the balance.
  have hmain : ∀ r : ℝ, 0 < r →
      H *
          (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r) ≤
        e r / ENNReal.ofReal r := by
    intro r hr
    rcases le_or_gt (min ((ν : Measure V) B) (1 - (ν : Measure V) B)) (e r) with hle | hgt
    · rw [tsub_eq_zero_of_le hle, mul_zero]
      exact zero_le
    have hne : min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r ≠ 0 :=
      ne_of_gt (tsub_pos_of_lt hgt)
    set w : V → ℝ := distanceCutoff B r with hwdef
    have hwL : LipschitzWith (Real.toNNReal r⁻¹) w := lipschitzWith_distanceCutoff B hr
    have hw01 : ∀ x, w x ∈ Set.Icc (0 : ℝ) 1 := distanceCutoff_mem_Icc B hr
    obtain ⟨g, hgreg, hgL1, hggrad⟩ :=
      exists_smooth_approximation_lipschitz ν volume hac hwL hw01
    set δ : ℕ → ℝ≥0∞ := fun j ↦ ∫⁻ x, ‖g j x - w x‖ₑ ∂(ν : Measure V) with hδdef
    have hwmeas : Measurable w := hwL.continuous.measurable
    -- for each mollification index, the error-corrected balance is controlled
    have hstep : ∀ j, H *
        (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - (δ j + e r)) ≤
          ∫⁻ x, ‖gradient (g j) x‖ₑ ∂(ν : Measure V) := by
      intro j
      obtain ⟨K', hK'⟩ := (hgreg j).2.1
      have hgmeas : Measurable (g j) := (hgreg j).1.continuous.measurable
      have hmeas1 : Measurable fun x : V ↦ ‖g j x - w x‖ₑ := (hgmeas.sub hwmeas).enorm
      have htri : ∫⁻ x, ‖g j x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤ δ j + e r := by
        calc ∫⁻ x, ‖g j x - B.indicator 1 x‖ₑ ∂(ν : Measure V)
            ≤ ∫⁻ x, (‖g j x - w x‖ₑ + ‖w x - B.indicator 1 x‖ₑ) ∂(ν : Measure V) := by
              refine lintegral_mono fun x ↦ ?_
              calc ‖g j x - B.indicator 1 x‖ₑ
                  = ‖(g j x - w x) + (w x - B.indicator 1 x)‖ₑ := by ring_nf
                _ ≤ ‖g j x - w x‖ₑ + ‖w x - B.indicator 1 x‖ₑ := enorm_add_le _ _
          _ = δ j + ∫⁻ x, ‖w x - B.indicator 1 x‖ₑ ∂(ν : Measure V) :=
              lintegral_add_left hmeas1 _
          _ ≤ δ j + e r :=
              add_le_add le_rfl (lintegral_enorm_distanceCutoff_sub_indicator_le ν hBne hBm hr)
      have hbal := min_measure_le_lintegral_min_superlevel_add ν hgmeas (hgreg j).2.2 hBm
      have hbal' : min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≤
          (∫⁻ t in Set.Ioo (0 : ℝ) 1,
            min ((ν : Measure V) {x | t < g j x}) (1 - (ν : Measure V) {x | t < g j x})) +
              (δ j + e r) := hbal.trans (add_le_add le_rfl htri)
      calc H *
            (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - (δ j + e r))
          ≤ H *
              ∫⁻ t in Set.Ioo (0 : ℝ) 1,
                min ((ν : Measure V) {x | t < g j x})
                  (1 - (ν : Measure V) {x | t < g j x}) :=
            mul_le_mul' le_rfl (tsub_le_iff_right.mpr hbal')
        _ ≤ ∫⁻ x, ‖gradient (g j) x‖ₑ ∂(ν : Measure V) :=
            hTest (hgreg j).1 hK' (hgreg j).2.2
    -- pass to the limit in the mollification index
    have hδe : Tendsto (fun j ↦ δ j + e r) atTop (𝓝 (e r)) := by
      simpa using hgL1.add (tendsto_const_nhds (x := e r))
    have hleft : Tendsto (fun j ↦ H *
        (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - (δ j + e r))) atTop
        (𝓝 (H *
          (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r))) :=
      ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.sub tendsto_const_nhds hδe (Or.inl hmtop)) (Or.inl hne)
    have hlim := le_of_tendsto_of_tendsto' hleft hggrad hstep
    refine hlim.trans ?_
    have hgradw := lintegral_enorm_gradient_distanceCutoff_le ν volume hac B hr
    rwa [hcl] at hgradw
  -- let the radius tend to zero
  have he0 : Tendsto e (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ ↦ (ν : Measure V) (Metric.thickening r B)) (𝓝[>] 0)
        (𝓝 ((ν : Measure V) (closure B))) :=
      tendsto_measure_thickening ⟨1, one_pos, measure_ne_top _ _⟩
    rw [hcl] at h1
    have h2 := ENNReal.Tendsto.sub h1 (tendsto_const_nhds (x := (ν : Measure V) B))
      (Or.inl (measure_ne_top _ _))
    rwa [tsub_self] at h2
  have hLtend : Tendsto (fun r : ℝ ↦ H *
      (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r)) (𝓝[>] 0)
      (𝓝 (H *
        min ((ν : Measure V) B) (1 - (ν : Measure V) B))) := by
    have h2 : Tendsto (fun r : ℝ ↦ min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r)
        (𝓝[>] 0) (𝓝 (min ((ν : Measure V) B) (1 - (ν : Measure V) B))) := by
      have h3 := ENNReal.Tendsto.sub
        (tendsto_const_nhds (x := min ((ν : Measure V) B) (1 - (ν : Measure V) B))) he0
        (Or.inl hmtop)
      rwa [tsub_zero] at h3
    exact ENNReal.Tendsto.const_mul h2 (Or.inl hm0)
  calc H *
        min ((ν : Measure V) B) (1 - (ν : Measure V) B)
      = liminf (fun r : ℝ ↦ H *
          (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r)) (𝓝[>] 0) :=
        hLtend.liminf_eq.symm
    _ ≤ liminf (fun r : ℝ ↦ e r / ENNReal.ofReal r) (𝓝[>] 0) := by
        refine liminf_le_liminf ?_
        filter_upwards [self_mem_nhdsWithin] with r hr using hmain r hr
    _ = minkowskiContent ν B := rfl


omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem weak_of_setwise (νn : ℕ → ProbabilityMeasure V) (ν : ProbabilityMeasure V)
    (hset : ∀ D : Set V, MeasurableSet D →
      Tendsto (fun n => (νn n : Measure V) D) atTop (𝓝 ((ν : Measure V) D))) :
    Tendsto νn atTop (𝓝 ν) := by
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  rw [(hset G hG.measurableSet).liminf_eq]

omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem gradient_lintegral_tendsto (νn : ℕ → ProbabilityMeasure V)
    (ν : ProbabilityMeasure V) (hweak : Tendsto νn atTop (𝓝 ν))
    {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    {K : ℝ≥0} (hK : LipschitzWith K u) :
    Tendsto (fun n => ∫⁻ x, ‖gradient u x‖ₑ ∂(νn n : Measure V)) atTop
      (𝓝 (∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V))) := by
  let g : V →ᵇ ℝ≥0 := BoundedContinuousFunction.mkOfBound
    ⟨fun x => Real.toNNReal ‖gradient u x‖,
      continuous_real_toNNReal.comp ((Energy.Euclidean.continuous_gradient_of_contDiff hu (by decide)).norm)⟩
    (K : ℝ) (by
      intro x y
      change |(Real.toNNReal ‖gradient u x‖ : ℝ) -
        (Real.toNNReal ‖gradient u y‖ : ℝ)| ≤ (K : ℝ)
      rw [Real.coe_toNNReal _ (norm_nonneg _), Real.coe_toNNReal _ (norm_nonneg _)]
      have hx := Energy.Euclidean.LipschitzApproximation.norm_gradient_le_of_lipschitz hK x
      have hy := Energy.Euclidean.LipschitzApproximation.norm_gradient_le_of_lipschitz hK y
      have hx0 := norm_nonneg (gradient u x)
      have hy0 := norm_nonneg (gradient u y)
      exact abs_sub_le_iff.mpr ⟨by nlinarith, by nlinarith⟩)
  have h := (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hweak) g
  have hg (x : V) : (g x : ENNReal) = ‖gradient u x‖ₑ := by
    simp only [g, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
    simp [enorm_eq_nnnorm, nnnorm]
  simp_rw [hg] at h
  exact h

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private theorem balance_lintegral_tendsto (νn : ℕ → ProbabilityMeasure V)
    (ν : ProbabilityMeasure V)
    (hset : ∀ D : Set V, MeasurableSet D →
      Tendsto (fun n => (νn n : Measure V) D) atTop (𝓝 ((ν : Measure V) D)))
    {u : V → ℝ} (hu : Continuous u) :
    Tendsto (fun n => ∫⁻ t in Set.Ioo (0 : ℝ) 1,
      min ((νn n : Measure V) {x | t < u x})
        (1 - (νn n : Measure V) {x | t < u x})) atTop
      (𝓝 (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        min ((ν : Measure V) {x | t < u x})
          (1 - (ν : Measure V) {x | t < u x}))) := by
  apply tendsto_lintegral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) (bound := fun _ => 1)
  · exact Filter.Eventually.of_forall fun n =>
      (measurable_min_measure_superlevel (νn n) u)
  · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun t =>
      (min_le_left _ _).trans prob_le_one
  · simp [lintegral_const, Real.volume_Ioo]
  · exact Filter.Eventually.of_forall fun t => by
      have hm : MeasurableSet {x : V | t < u x} :=
        (measurableSet_lt measurable_const hu.measurable)
      have ht := hset _ hm
      have hsub : Tendsto (fun n => 1 - (νn n : Measure V) {x | t < u x}) atTop
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

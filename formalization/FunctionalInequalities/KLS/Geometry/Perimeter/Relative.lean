import FunctionalInequalities.KLS.LogConcave.Density.Bounds
import FunctionalInequalities.Analysis.SmoothDomain.Homothety
import FunctionalInequalities.KLS.Geometry.Perimeter.MollifiedBoundary

/-! # Relative perimeter and quantitative mollification

Normalized boundary integrals and the outward-dilation bound. No recovery or coarea imports. -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace FunctionalInequalities.KLS

universe u

/-! ### Relative perimeter -/

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The relative perimeter `P_ρ(U) = ∫_{∂U ∩ Ω} ρ dℋ^{n-1}` of a smooth domain with respect to a
weight `ρ` inside the open set `Ω`, against the `(n-1)`-dimensional Hausdorff measure of `V`
(`n = finrank ℝ V`).  Boundary pieces outside `Ω` carry no charge. -/
def relativePerimeter (ρ : V → ℝ) (Ω : Set V) (U : SmoothDomain V) : ℝ≥0∞ :=
  ∫⁻ x in frontier U.carrier ∩ Ω, ENNReal.ofReal (ρ x) ∂(surfaceMeasure V)

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Domains with empty frontier have zero relative perimeter; dimension zero is included. -/
theorem relativePerimeter_eq_zero_of_frontier_eq_empty (ρ : V → ℝ) (Ω : Set V)
    (U : SmoothDomain V) (h : frontier U.carrier = ∅) :
    relativePerimeter ρ Ω U = 0 := by
  unfold relativePerimeter
  rw [h, Set.empty_inter, Measure.restrict_empty, lintegral_zero_measure]

/-! ### Expansion and quantitative smoothing -/

namespace RelativePerimeter

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Dilated indicators converge to the indicator in `L¹(ν)` as the ratio tends to one, for an
open set whose frontier is `ν`-null. -/
theorem tendsto_indicator_homothety (ν : ProbabilityMeasure V) {U : Set V} (hU : IsOpen U)
    (hfr : (ν : Measure V) (frontier U) = 0) (a : V) :
    Tendsto (fun c : ℝ ↦ ∫⁻ x, ‖U.indicator (1 : V → ℝ) (AffineMap.homothety a c x) -
        U.indicator 1 x‖ₑ ∂(ν : Measure V)) (𝓝 1) (𝓝 0) := by
  have hind : Measurable (U.indicator (1 : V → ℝ)) := measurable_one.indicator hU.measurableSet
  have hIcc : ∀ y : V, U.indicator (1 : V → ℝ) y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    by_cases hy : y ∈ U
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have hzero : ∫⁻ _ : V, (0 : ℝ≥0∞) ∂(ν : Measure V) = 0 := lintegral_zero
  rw [← hzero]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ 1) ?_ ?_ ?_ ?_
  · filter_upwards with c
    exact ((hind.comp (AffineMap.homothety_continuous a c).measurable).sub hind).enorm
  · filter_upwards with c
    filter_upwards with x
    have h1 := hIcc (AffineMap.homothety a c x)
    have h2 := hIcc x
    rw [Real.enorm_eq_ofReal_abs, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_le]
    exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  · rw [lintegral_one]
    exact measure_ne_top _ _
  · have hae : ∀ᵐ x ∂(ν : Measure V), x ∉ frontier U := by
      rw [ae_iff]; simpa using hfr
    filter_upwards [hae] with x hx
    have hpath : Tendsto (fun c : ℝ ↦ AffineMap.homothety a c x) (𝓝 1) (𝓝 x) := by
      have heq : (fun c : ℝ ↦ AffineMap.homothety a c x) = fun c : ℝ ↦ c • (x - a) + a := by
        funext c; simp [AffineMap.homothety_apply]
      rw [heq]
      have hc : Continuous fun c : ℝ ↦ c • (x - a) + a :=
        (continuous_id.smul continuous_const).add continuous_const
      simpa using hc.tendsto 1
    by_cases hxU : x ∈ U
    · refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
      filter_upwards [hpath (hU.mem_nhds hxU)] with c hc
      have hc' : AffineMap.homothety a c x ∈ U := hc
      simp [Set.indicator_of_mem hc', Set.indicator_of_mem hxU]
    · have hxc : x ∉ closure U := fun hcl ↦ hx ⟨hcl, by rwa [hU.interior_eq]⟩
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
      filter_upwards [hpath (isClosed_closure.isOpen_compl.mem_nhds hxc)] with c hc
      have hc' : AffineMap.homothety a c x ∈ (closure U)ᶜ := hc
      have hcU : AffineMap.homothety a c x ∉ U := fun hmem ↦ hc' (subset_closure hmem)
      simp [Set.indicator_of_notMem hcU, Set.indicator_of_notMem hxU]

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The averaged density after outward dilation is supported inside the support interior,
and is bounded by the original density with the log-concave comparison factor. -/
theorem lintegral_normed_mul_density_le {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) {a : V} {r b₀ M s : ℝ}
    (haΩ : Metric.closedBall a r ⊆ interior (ν : Measure V).support)
    (hb₀ : 0 < b₀) (hball : ∀ z ∈ Metric.closedBall a r, b₀ ≤ ρ z) (hM : ∀ z, ρ z ≤ M)
    (hs₀ : 0 < s) (hs₁ : s < 1) (φ : ContDiffBump (0 : V))
    (hε : s * φ.rOut / (1 - s) < r) (y : V) :
    ∫⁻ x, ENNReal.ofReal (φ.normed volume (x - AffineMap.homothety a s⁻¹ y)) *
        ENNReal.ofReal (ρ x) ≤
      ENNReal.ofReal ((M / b₀) ^ ((1 - s) / s)) *
        (interior (ν : Measure V).support).indicator (fun y => ENNReal.ofReal (ρ y)) y := by
  let C := ENNReal.ofReal ((M / b₀) ^ ((1 - s) / s)) *
    (interior (ν : Measure V).support).indicator (fun y => ENNReal.ofReal (ρ y)) y
  have hs : 0 < 1 - s := sub_pos.mpr hs₁
  have hpoint : ∀ x : V,
      ENNReal.ofReal (φ.normed volume (x - AffineMap.homothety a s⁻¹ y)) * ENNReal.ofReal (ρ x)
        ≤ ENNReal.ofReal (φ.normed volume (x - AffineMap.homothety a s⁻¹ y)) * C := by
    intro x
    by_cases hk : φ.normed volume (x - AffineMap.homothety a s⁻¹ y) = 0
    · simp [hk]
    by_cases hx : ρ x = 0
    · simp [hx]
    have hxpos : 0 < ρ x := lt_of_le_of_ne (hρ.nonneg x) (Ne.symm hx)
    let z := x - AffineMap.homothety a s⁻¹ y
    have hz : ‖z‖ < φ.rOut := by
      have hmem : z ∈ Function.support (φ.normed (volume : Measure V)) := hk
      rw [φ.support_normed_eq] at hmem
      simpa only [Metric.mem_ball, dist_zero_right] using hmem
    let b := a - (s / (1 - s)) • z
    have hb : b ∈ Metric.closedBall a r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have heq : b - a = -((s / (1 - s)) • z) := by dsimp [b]; module
      rw [heq, norm_neg, norm_smul, Real.norm_of_nonneg (div_nonneg hs₀.le hs.le)]
      calc s / (1 - s) * ‖z‖ ≤ s / (1 - s) * φ.rOut :=
            mul_le_mul_of_nonneg_left hz.le (div_nonneg hs₀.le hs.le)
        _ = s * φ.rOut / (1 - s) := by ring
        _ ≤ r := hε.le
    have hcomb : y = s • x + (1 - s) • b := by
      have hscale : (1 - s) • ((s / (1 - s)) • z) = s • z := by
        rw [smul_smul, mul_div_cancel₀ s hs.ne']
      symm
      calc s • x + (1 - s) • b = s • x + (1 - s) • a - s • z := by
            dsimp [b]
            rw [smul_sub, hscale]
            module
        _ = y := by
            dsimp [z]
            simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
              smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hs₀.ne']
            module
    have hyΩ : y ∈ interior (ν : Measure V).support := by
      apply hρ.interior_pos_subset
      rw [hcomb]
      exact hρ.convex_pos.combo_self_interior_mem_interior hxpos
        (hρ.interior_support_subset (haΩ hb)) hs₀.le hs (by ring)
    have hcomp := hρ.le_rpow_mul_of_combination hs₀ hs₁ hb₀ hM (hball b hb) hcomb
    have hweight : ENNReal.ofReal (ρ x) ≤ C := by
      dsimp [C]
      rw [Set.indicator_of_mem hyΩ, ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg ((hρ.nonneg a).trans (hM a)) hb₀.le) _)]
      exact ENNReal.ofReal_le_ofReal hcomp
    exact mul_le_mul_right hweight _
  have hη : (∫⁻ x, ENNReal.ofReal (φ.normed volume
      (x - AffineMap.homothety a s⁻¹ y))) = 1 := by
    rw [lintegral_sub_right_eq_self (fun z : V => ENNReal.ofReal (φ.normed volume z))]
    rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
      (Filter.Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (φ.normed volume (x - AffineMap.homothety a s⁻¹ y)) * C :=
      lintegral_mono hpoint
    _ = (∫⁻ x, ENNReal.ofReal (φ.normed volume (x - AffineMap.homothety a s⁻¹ y))) * C :=
      lintegral_mul_const _ (φ.continuous_normed.comp
        (continuous_id.sub continuous_const)).measurable.ennreal_ofReal
    _ = C := by rw [hη, one_mul]

/-- Quantitative expansion–smoothing bound, including unbounded domains and carriers.
The outward dilation removes carrier-boundary charges before convolution. -/
theorem lintegral_enorm_gradient_mollified_homothety_le {ν : ProbabilityMeasure V}
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    (U : SmoothDomain V) {a : V} {r b₀ M s : ℝ} (hr : 0 < r)
    (haΩ : Metric.closedBall a r ⊆ interior (ν : Measure V).support)
    (hb₀ : 0 < b₀) (hball : ∀ z ∈ Metric.closedBall a r, b₀ ≤ ρ z) (hM : ∀ z, ρ z ≤ M)
    (hs₀ : 0 < s) (hs₁ : s < 1) (φ : ContDiffBump (0 : V)) (hε : s * φ.rOut / (1 - s) < r) :
    ∫⁻ x, ‖gradient ((U.homothety a (inv_ne_zero hs₀.ne')).mollifiedIndicator φ volume) x‖ₑ
        ∂(ν : Measure V) ≤
      ENNReal.ofReal (s ^ (1 - (Module.finrank ℝ V : ℝ)) * (M / b₀) ^ ((1 - s) / s)) *
        relativePerimeter ρ (interior (ν : Measure V).support) U := by
  let W := U.homothety a (inv_ne_zero hs₀.ne')
  let σ := (surfaceMeasure V).restrict (frontier W.carrier)
  let : IsLocallyFiniteMeasure σ := W.isLocallyFiniteMeasure_surfaceMeasure_frontier
  let F : V → V → ℝ≥0∞ := fun x q => ENNReal.ofReal (φ.normed volume (x - q))
  have hF : Measurable (Function.uncurry F) :=
    (φ.continuous_normed.comp (continuous_fst.sub continuous_snd)).measurable.ennreal_ofReal
  let A : V → ℝ≥0∞ := fun q => ∫⁻ x, F x q * ENNReal.ofReal (ρ x)
  have hA : Measurable A :=
    (hF.mul (hρ.measurable.comp measurable_fst).ennreal_ofReal).lintegral_prod_left
  have hν : ∀ q, (∫⁻ x, F x q ∂(ν : Measure V)) = A q := by
    intro q
    have hq : Measurable (fun x => F x q) := hF.comp (measurable_id.prodMk measurable_const)
    rw [← hρ.withDensity_eq, lintegral_withDensity_eq_lintegral_mul _
      hρ.measurable.ennreal_ofReal hq]
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm (ENNReal.ofReal (ρ x)) (F x q))
  have hbound : (∫⁻ x, ‖gradient (W.mollifiedIndicator φ volume) x‖ₑ ∂(ν : Measure V)) ≤
      ∫⁻ q in frontier W.carrier, A q ∂(surfaceMeasure V) := by
    calc
      _ ≤ ∫⁻ x, ∫⁻ q, F x q ∂σ ∂(ν : Measure V) :=
        lintegral_mono fun x => W.enorm_gradient_mollified_le φ x
      _ = ∫⁻ q, ∫⁻ x, F x q ∂(ν : Measure V) ∂σ :=
        lintegral_lintegral_swap hF.aemeasurable
      _ = _ := lintegral_congr_ae (Filter.Eventually.of_forall hν)
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with hn | hn
  · have : Subsingleton V := Module.finrank_zero_iff.mp hn
    have hempty : frontier W.carrier = ∅ := by
      rcases W.carrier.eq_empty_or_nonempty with he | he
      · rw [he, frontier_empty]
      · rw [Subsingleton.eq_univ_of_nonempty he, frontier_univ]
    rw [hempty, Measure.restrict_empty, lintegral_zero_measure] at hbound
    exact hbound.trans bot_le
  have hscale : ((‖s⁻¹‖₊ ^ ((Module.finrank ℝ V - 1 : ℕ) : ℝ) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (s ^ (1 - (Module.finrank ℝ V : ℝ))) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_rpow, coe_nnnorm,
      Real.norm_of_nonneg (inv_nonneg.mpr hs₀.le), Real.inv_rpow hs₀.le,
      ← Real.rpow_neg hs₀.le]
    congr 2
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  have hMpos : 0 < M := hb₀.trans_le
    ((hball a (Metric.mem_closedBall_self hr.le)).trans (hM a))
  have hC : 0 ≤ (M / b₀) ^ ((1 - s) / s) :=
    Real.rpow_nonneg (div_nonneg hMpos.le hb₀.le) _
  have hstep := U.setLIntegral_frontier_homothety a (inv_ne_zero hs₀.ne') hA
  rw [ENNReal.smul_def, smul_eq_mul, hscale] at hstep
  calc
    _ ≤ ∫⁻ q in frontier W.carrier, A q ∂(surfaceMeasure V) := hbound
    _ = ENNReal.ofReal (s ^ (1 - (Module.finrank ℝ V : ℝ))) *
        ∫⁻ y in frontier U.carrier, A (AffineMap.homothety a s⁻¹ y) ∂(surfaceMeasure V) := hstep
    _ ≤ ENNReal.ofReal (s ^ (1 - (Module.finrank ℝ V : ℝ))) *
        ∫⁻ y in frontier U.carrier, ENNReal.ofReal ((M / b₀) ^ ((1 - s) / s)) *
          (interior (ν : Measure V).support).indicator (fun y => ENNReal.ofReal (ρ y)) y
            ∂(surfaceMeasure V) := by
      exact mul_le_mul_right (lintegral_mono fun y =>
        lintegral_normed_mul_density_le hρ haΩ hb₀ hball hM hs₀ hs₁ φ hε y) _
    _ = _ := by
      rw [lintegral_const_mul _ (hρ.measurable.ennreal_ofReal.indicator isOpen_interior.measurableSet),
        setLIntegral_indicator isOpen_interior.measurableSet, Set.inter_comm,
        ← mul_assoc]
      rw [mul_comm (ENNReal.ofReal (s ^ (1 - (Module.finrank ℝ V : ℝ)))),
        ← ENNReal.ofReal_mul hC, mul_comm ((M / b₀) ^ ((1 - s) / s))]
      rfl

end RelativePerimeter
end FunctionalInequalities.KLS

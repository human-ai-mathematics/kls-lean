import FunctionalInequalities.KLS.Geometry.RelativePerimeter

/-! # Smooth recovery sequences for the relative perimeter

The outward dilation of `Geometry/RelativePerimeter` is combined with a vanishing mollification
radius.  No coarea, Sard or Cheeger dependency; the module imports no work-in-progress layer. -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace FunctionalInequalities.KLS

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

namespace SmoothDomain

/-! ### Mollification with a vanishing radius -/

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- Where the indicator is constant on the bump's outer ball, the mollified indicator reproduces
it exactly.  Only the normalization of the bump is used, so no boundary regularity enters. -/
theorem mollifiedIndicator_eq_indicator_of_const (U : SmoothDomain V)
    (φ : ContDiffBump (0 : V)) {x : V}
    (h : ∀ y : V, ‖x - y‖ < φ.rOut →
      U.carrier.indicator (1 : V → ℝ) y = U.carrier.indicator 1 x) :
    U.mollifiedIndicator φ volume x = U.carrier.indicator (1 : V → ℝ) x := by
  have hconst : ∀ y : V, φ.normed volume (x - y) * U.carrier.indicator (1 : V → ℝ) y
      = φ.normed volume (x - y) * U.carrier.indicator (1 : V → ℝ) x := by
    intro y
    by_cases hy : ‖x - y‖ < φ.rOut
    · rw [h y hy]
    · have hz : φ.normed (volume : Measure V) (x - y) = 0 := by
        have hns : x - y ∉ Function.support (φ.normed (volume : Measure V)) := by
          rw [φ.support_normed_eq]
          simpa only [Metric.mem_ball, dist_zero_right] using hy
        simpa using hns
      rw [hz, zero_mul, zero_mul]
  have hone : ∫ y : V, φ.normed (volume : Measure V) (x - y) = 1 := by
    have hrefl : ∀ y : V, φ.normed (volume : Measure V) (x - y)
        = φ.normed (volume : Measure V) (y - x) := by
      intro y
      rw [show x - y = -(y - x) by abel, φ.normed_neg]
    rw [integral_congr_ae (Filter.Eventually.of_forall hrefl),
      integral_sub_right_eq_self (φ.normed (volume : Measure V)) x, φ.integral_normed]
  rw [mollifiedIndicator, integral_congr_ae (Filter.Eventually.of_forall hconst),
    integral_mul_const, hone, one_mul]

omit [CompleteSpace V] in
/-- With a `ν`-null boundary the mollified indicator converges to the indicator in `L¹(ν)` as the
bump radius vanishes: below every prescribed radius there is a bump with prescribed `L¹` error.
Neither the domain nor its carrier need be bounded, and the indicator is never assumed
`volume`-integrable. -/
theorem exists_bump_lintegral_enorm_mollifiedIndicator_sub_lt (U : SmoothDomain V)
    (ν : ProbabilityMeasure V) (hfr : (ν : Measure V) (frontier U.carrier) = 0)
    {R : ℝ} (hR : 0 < R) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ φ : ContDiffBump (0 : V), φ.rOut < R ∧
      ∫⁻ x, ‖U.mollifiedIndicator φ volume x - U.carrier.indicator 1 x‖ₑ
        ∂(ν : Measure V) < δ := by
  have hind : Measurable (U.carrier.indicator (1 : V → ℝ)) :=
    measurable_one.indicator U.isOpen.measurableSet
  have hIcc : ∀ y : V, U.carrier.indicator (1 : V → ℝ) y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    by_cases hy : y ∈ U.carrier
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  set ψ : ℕ → ContDiffBump (0 : V) := fun k =>
    { rIn := R / ((k : ℝ) + 2) / 2
      rOut := R / ((k : ℝ) + 2)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) } with hψ
  have hψout : ∀ k : ℕ, (ψ k).rOut = R / ((k : ℝ) + 2) := fun _ ↦ rfl
  have hlim : Tendsto (fun k ↦ ∫⁻ x, ‖U.mollifiedIndicator (ψ k) volume x -
      U.carrier.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) := by
    have hzero : ∫⁻ _ : V, (0 : ℝ≥0∞) ∂(ν : Measure V) = 0 := lintegral_zero
    rw [← hzero]
    refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ 1) ?_ ?_ ?_ ?_
    · intro k
      exact (((U.mollifiedIndicator_contDiff_lipschitz_mem_Icc (ψ k)
        volume).1.continuous.measurable).sub hind).enorm
    · intro k
      filter_upwards with x
      have h1 := (U.mollifiedIndicator_contDiff_lipschitz_mem_Icc (ψ k) volume).2.2 x
      have h2 := hIcc x
      rw [Real.enorm_eq_ofReal_abs, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_le]
      exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
    · rw [lintegral_one]
      exact measure_ne_top _ _
    · have hae : ∀ᵐ x ∂(ν : Measure V), x ∉ frontier U.carrier := by
        rw [ae_iff]; simpa using hfr
      filter_upwards [hae] with x hx
      obtain ⟨d, hd, hsub⟩ : ∃ d : ℝ, 0 < d ∧ ∀ y : V, ‖x - y‖ < d →
          U.carrier.indicator (1 : V → ℝ) y = U.carrier.indicator 1 x := by
        by_cases hxU : x ∈ U.carrier
        · obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hxU
          refine ⟨d, hd, fun y hy ↦ ?_⟩
          have hyU : y ∈ U.carrier := by
            refine hball ?_
            rw [Metric.mem_ball, dist_eq_norm, ← norm_neg]
            simpa using hy
          simp [Set.indicator_of_mem hyU, Set.indicator_of_mem hxU]
        · have hxc : x ∉ closure U.carrier := fun hcl ↦ hx ⟨hcl, by rwa [U.isOpen.interior_eq]⟩
          obtain ⟨d, hd, hball⟩ :=
            Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hxc
          refine ⟨d, hd, fun y hy ↦ ?_⟩
          have hyc : y ∈ (closure U.carrier)ᶜ := by
            refine hball ?_
            rw [Metric.mem_ball, dist_eq_norm, ← norm_neg]
            simpa using hy
          have hyU : y ∉ U.carrier := fun hm ↦ hyc (subset_closure hm)
          simp [Set.indicator_of_notMem hyU, Set.indicator_of_notMem hxU]
      obtain ⟨k₀, hk₀⟩ := exists_nat_gt (R / d)
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
      filter_upwards [eventually_ge_atTop k₀] with k hk
      have hcast : (k₀ : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hrle : (ψ k).rOut ≤ d := by
        rw [hψout k, div_le_iff₀ hk2, mul_comm d]
        have hRd : R < (k₀ : ℝ) * d := (div_lt_iff₀ hd).mp hk₀
        have h1 : (k₀ : ℝ) * d ≤ (k : ℝ) * d := mul_le_mul_of_nonneg_right hcast hd.le
        have h2 : ((k : ℝ) + 2) * d - (k : ℝ) * d = 2 * d := by ring
        linarith [hd.le]
      rw [U.mollifiedIndicator_eq_indicator_of_const (ψ k)
        (fun y hy ↦ hsub y (lt_of_lt_of_le hy hrle))]
      simp
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  refine ⟨ψ k, ?_, hk⟩
  rw [hψout k]
  refine div_lt_self hR ?_
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

end SmoothDomain

namespace RelativePerimeter

/-! ### The recovery sequence -/

/-- Blueprint `lem:relative-perimeter-smoothing`.  Let `ν` be a probability law on a
finite-dimensional real inner-product space with a Borell density `ρ` relative to Lebesgue
measure `volume`, and put `Ω = interior ν.support`.  For every smooth domain `U` with finite relative
perimeter there are globally `C^∞`, globally Lipschitz functions `0 ≤ u_j ≤ 1` such that
`u_j → 𝟙_U` in `L¹(ν)` and `limsup_j ∫ ‖∇u_j‖ dν ≤ P_ρ(U)`.  The domain and the carrier may be
unbounded; a piece of `∂U` on `∂(supp ν)` costs nothing. -/
theorem exists_smooth_recovery_sequence {ν : ProbabilityMeasure V}
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    (U : SmoothDomain V)
    (_hU : relativePerimeter ρ (interior (ν : Measure V).support) U ≠ ⊤) :
    ∃ u : ℕ → V → ℝ,
      (∀ j, ContDiff ℝ ∞ (u j) ∧ (∃ K : ℝ≥0, LipschitzWith K (u j)) ∧
        ∀ x, u j x ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫⁻ x, ‖u j x - U.carrier.indicator 1 x‖ₑ ∂(ν : Measure V))
        atTop (𝓝 0) ∧
      limsup (fun j ↦ ∫⁻ x, ‖gradient (u j) x‖ₑ ∂(ν : Measure V)) atTop ≤
        relativePerimeter ρ (interior (ν : Measure V).support) U := by
  classical
  -- an interior ball on which the density is bounded below, and the global upper bound
  obtain ⟨a, r₀, b₀, hr₀, hb₀, hball₀⟩ := hρ.exists_ball_le
  obtain ⟨M, hM⟩ := hρ.exists_le
  set r : ℝ := r₀ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hsubball : Metric.closedBall a r ⊆ Metric.ball a r₀ := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    rw [hrdef] at hz
    linarith
  have hball : ∀ z ∈ Metric.closedBall a r, b₀ ≤ ρ z := fun z hz ↦ hball₀ z (hsubball hz)
  have haΩ : Metric.closedBall a r ⊆ interior (ν : Measure V).support := by
    refine subset_trans (subset_trans hsubball ?_) hρ.interior_pos_subset
    exact interior_maximal (fun z hz ↦ lt_of_lt_of_le hb₀ (hball₀ z hz)) Metric.isOpen_ball
  have hMpos : 0 < M :=
    lt_of_lt_of_le hb₀ ((hball a (Metric.mem_closedBall_self hr.le)).trans (hM a))
  have hbase : 0 < M / b₀ := div_pos hMpos hb₀
  -- the frontiers are null for `ν`
  have hUfr : (ν : Measure V) (frontier U.carrier) = 0 :=
    hρ.absolutelyContinuous (U.addHaar_frontier volume)
  -- the dilation ratios
  set s : ℕ → ℝ := fun j ↦ 1 - 1 / ((j : ℝ) + 2) with hsdef
  have hs₀ : ∀ j, 0 < s j := by
    intro j
    have hj : (1 : ℝ) < (j : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) j; linarith
    have hlt : 1 / ((j : ℝ) + 2) < 1 := by
      rw [div_lt_one (by linarith)]; exact hj
    simp only [hsdef]
    linarith
  have hs₁ : ∀ j, s j < 1 := by
    intro j
    have hpos : 0 < 1 / ((j : ℝ) + 2) := by positivity
    simp only [hsdef]
    linarith
  have hstend : Tendsto s atTop (𝓝 1) := by
    have h : Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa [hsdef] using tendsto_const_nhds.sub h
  -- the dilated domains and the choice of bump radii
  have hWfr : ∀ j, (ν : Measure V)
      (frontier (U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier) = 0 := fun j ↦
    hρ.absolutelyContinuous ((U.homothety a (inv_ne_zero (hs₀ j).ne')).addHaar_frontier volume)
  have hchoice : ∀ j : ℕ, ∃ φ : ContDiffBump (0 : V),
      φ.rOut < r * (1 - s j) / s j ∧
      ∫⁻ x, ‖(U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator φ volume x -
          (U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier.indicator 1 x‖ₑ
        ∂(ν : Measure V) < ((j : ℝ≥0∞) + 1)⁻¹ := by
    intro j
    have hpos : 0 < r * (1 - s j) / s j :=
      div_pos (mul_pos hr (sub_pos.mpr (hs₁ j))) (hs₀ j)
    exact SmoothDomain.exists_bump_lintegral_enorm_mollifiedIndicator_sub_lt
      (U.homothety a (inv_ne_zero (hs₀ j).ne')) ν (hWfr j) hpos
      (ENNReal.inv_pos.mpr (by simp))
  choose φ hφR hφerr using hchoice
  have hεj : ∀ j, s j * (φ j).rOut / (1 - s j) < r := by
    intro j
    have h1 : 0 < 1 - s j := sub_pos.mpr (hs₁ j)
    have h2 : 0 < s j := hs₀ j
    have h3 := hφR j
    rw [lt_div_iff₀ h2] at h3
    rw [div_lt_iff₀ h1, mul_comm (s j) ((φ j).rOut)]
    exact h3
  refine ⟨fun j ↦ (U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator (φ j) volume,
    fun j ↦ (U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator_contDiff_lipschitz_mem_Icc
      (φ j) volume, ?_, ?_⟩
  · -- `L¹(ν)` convergence: dilation error plus mollification error
    set g : ℝ → ℝ≥0∞ := fun c ↦
      ∫⁻ x, ‖U.carrier.indicator (1 : V → ℝ) (AffineMap.homothety a c x) -
        U.carrier.indicator 1 x‖ₑ ∂(ν : Measure V) with hgdef
    have hg : Tendsto g (𝓝 1) (𝓝 0) := tendsto_indicator_homothety ν U.isOpen hUfr a
    have hgs : Tendsto (fun j ↦ g (s j)) atTop (𝓝 0) := hg.comp hstend
    have hWind : ∀ (j : ℕ) (x : V),
        (U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier.indicator (1 : V → ℝ) x
          = U.carrier.indicator 1 (AffineMap.homothety a (s j) x) := by
      intro j x
      rw [U.indicator_homothety a (inv_ne_zero (hs₀ j).ne') x, inv_inv]
    have hle : ∀ j : ℕ,
        ∫⁻ x, ‖(U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator (φ j) volume x -
            U.carrier.indicator 1 x‖ₑ ∂(ν : Measure V)
          ≤ ((j : ℝ≥0∞) + 1)⁻¹ + g (s j) := by
      intro j
      have hmeas : Measurable fun x ↦
          ‖(U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator (φ j) volume x -
            (U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier.indicator (1 : V → ℝ) x‖ₑ :=
        ((((U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator_contDiff_lipschitz_mem_Icc
          (φ j) volume).1.continuous.measurable).sub
            (measurable_one.indicator
              (U.homothety a (inv_ne_zero (hs₀ j).ne')).isOpen.measurableSet)).enorm
      calc ∫⁻ x, ‖(U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator (φ j) volume x -
              U.carrier.indicator 1 x‖ₑ ∂(ν : Measure V)
          ≤ ∫⁻ x, (‖(U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator (φ j) volume x -
                (U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier.indicator (1 : V → ℝ) x‖ₑ +
              ‖(U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier.indicator (1 : V → ℝ) x -
                U.carrier.indicator 1 x‖ₑ) ∂(ν : Measure V) := by
            refine lintegral_mono fun x ↦ ?_
            rw [show (U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator (φ j) volume x -
                U.carrier.indicator (1 : V → ℝ) x
              = ((U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator (φ j) volume x -
                  (U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier.indicator (1 : V → ℝ) x) +
                ((U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier.indicator (1 : V → ℝ) x -
                  U.carrier.indicator 1 x) by ring]
            exact enorm_add_le _ _
        _ = (∫⁻ x, ‖(U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator (φ j) volume x -
                (U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier.indicator (1 : V → ℝ) x‖ₑ
              ∂(ν : Measure V)) +
            ∫⁻ x, ‖(U.homothety a (inv_ne_zero (hs₀ j).ne')).carrier.indicator (1 : V → ℝ) x -
                U.carrier.indicator 1 x‖ₑ ∂(ν : Measure V) := lintegral_add_left hmeas _
        _ ≤ ((j : ℝ≥0∞) + 1)⁻¹ + g (s j) := by
            refine add_le_add (hφerr j).le (le_of_eq ?_)
            rw [hgdef]
            exact lintegral_congr fun x ↦ by rw [hWind j x]
    have hinv : Tendsto (fun j : ℕ ↦ ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using h
    have hsum : Tendsto (fun j : ℕ ↦ ((j : ℝ≥0∞) + 1)⁻¹ + g (s j)) atTop (𝓝 0) := by
      simpa using hinv.add hgs
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ by simp) hle
  · -- the gradient budget: the dilation coefficient tends to one
    set P : ℝ≥0∞ := relativePerimeter ρ (interior (ν : Measure V).support) U with hP
    set c : ℕ → ℝ := fun j ↦
      s j ^ (1 - (Module.finrank ℝ V : ℝ)) * (M / b₀) ^ ((1 - s j) / s j) with hcdef
    have hle : ∀ j : ℕ,
        ∫⁻ x, ‖gradient ((U.homothety a (inv_ne_zero (hs₀ j).ne')).mollifiedIndicator
          (φ j) volume) x‖ₑ ∂(ν : Measure V) ≤ ENNReal.ofReal (c j) * P := fun j ↦
      lintegral_enorm_gradient_mollified_homothety_le hρ U hr haΩ hb₀ hball hM
        (hs₀ j) (hs₁ j) (φ j) (hεj j)
    have hctend : Tendsto c atTop (𝓝 1) := by
      have h1 : Tendsto (fun j : ℕ ↦ s j ^ (1 - (Module.finrank ℝ V : ℝ))) atTop (𝓝 1) := by
        have hcont : ContinuousAt (fun x : ℝ ↦ x ^ (1 - (Module.finrank ℝ V : ℝ))) 1 :=
          Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
        simpa [Function.comp_def] using hcont.tendsto.comp hstend
      have h2 : Tendsto (fun j : ℕ ↦ (M / b₀) ^ ((1 - s j) / s j)) atTop (𝓝 1) := by
        have he : Tendsto (fun j : ℕ ↦ (1 - s j) / s j) atTop (𝓝 0) := by
          have hnum : Tendsto (fun j : ℕ ↦ 1 - s j) atTop (𝓝 0) := by
            simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hstend
          simpa [Pi.div_def] using hnum.div hstend one_ne_zero
        have hcont : Continuous fun y : ℝ ↦ (M / b₀) ^ y := Real.continuous_const_rpow hbase.ne'
        simpa [Function.comp_def] using (hcont.tendsto 0).comp he
      simpa [hcdef] using h1.mul h2
    have hlim : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (c j) * P) atTop (𝓝 P) := by
      have h1 : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (c j)) atTop (𝓝 1) := by
        simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 1).comp hctend
      simpa using ENNReal.Tendsto.mul h1 (Or.inl one_ne_zero) tendsto_const_nhds
        (Or.inr ENNReal.one_ne_top)
    exact le_trans (limsup_le_limsup (Filter.Eventually.of_forall hle))
      (le_of_eq hlim.limsup_eq)

end RelativePerimeter
end FunctionalInequalities.KLS

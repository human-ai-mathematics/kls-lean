module

public import FunctionalInequalities.Probability.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Distribution functions of probability laws on the real line

Source: Blueprint `thm:one-dimensional-logconcave-poincare`, supporting calculus. Read `cdf`,
`cdf_mono`, `tendsto_cdf_atTop`, `tendsto_cdf_atBot`, then the density section
(`cdf_sub_cdf_eq_integral`, `continuous_cdf`, `hasDerivAt_cdf`, `exists_cdf_eq_half`) and the
uniform pushforward `map_cdf_eq_uniform` with its two moment identities.

For a probability law `μ` on `ℝ`, `cdf μ x = μ (Iic x)` (as a real number). When `μ` has a
nonnegative Borel Lebesgue density `ρ`, the distribution function is the primitive of `ρ`, hence
continuous, differentiable at continuity points of `ρ` with derivative `ρ`, attains the value `1/2`
(a median exists), and pushes `μ` forward to the uniform law on `[0, 1]`.

Nothing here uses log-concavity. The lemmas are stated for an arbitrary Lebesgue density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace FunctionalInequalities.Probability.Line

variable (μ : ProbabilityMeasure ℝ)

/-- The distribution function `x ↦ μ (-∞, x]`, as a real number. -/
def cdf (x : ℝ) : ℝ := (μ : Measure ℝ).real (Iic x)

theorem cdf_nonneg (x : ℝ) : 0 ≤ cdf μ x := measureReal_nonneg

theorem cdf_le_one (x : ℝ) : cdf μ x ≤ 1 := by
  unfold cdf
  rw [← probReal_univ (μ := (μ : Measure ℝ))]
  exact measureReal_mono (subset_univ _)

theorem cdf_mono : Monotone (cdf μ) := fun _ _ hxy ↦ measureReal_mono (Iic_subset_Iic.mpr hxy)

/-- The mass of the right half-line is `1 - cdf`. -/
theorem measureReal_Ioi (x : ℝ) : (μ : Measure ℝ).real (Ioi x) = 1 - cdf μ x := by
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
  rfl

/-- The increment of the distribution function is the mass of the half-open interval. -/
theorem cdf_sub_cdf {x y : ℝ} (hxy : x ≤ y) :
    cdf μ y - cdf μ x = (μ : Measure ℝ).real (Ioc x y) := by
  have hdiff : Iic y \ Iic x = Ioc x y := by
    ext z
    simp only [Set.mem_sdiff, mem_Iic, mem_Ioc, not_le]
    exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
  rw [← hdiff, measureReal_sdiff (Iic_subset_Iic.mpr hxy) measurableSet_Iic]
  rfl

/-- The distribution function tends to one at `+∞`. -/
theorem tendsto_cdf_atTop : Tendsto (cdf μ) atTop (𝓝 1) := by
  have h := tendsto_measure_Iic_atTop (μ := (μ : Measure ℝ))
  rw [measure_univ] at h
  have h' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  have hcdf : cdf μ = fun x ↦ ((μ : Measure ℝ) (Iic x)).toReal := rfl
  rw [hcdf]
  simpa [Function.comp_def] using h'

/-- The distribution function tends to zero at `-∞`. -/
theorem tendsto_cdf_atBot : Tendsto (cdf μ) atBot (𝓝 0) := by
  have h := tendsto_measure_Ici_atBot (μ := (μ : Measure ℝ))
  rw [measure_univ] at h
  have h' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  simp only [Function.comp_def, ENNReal.toReal_one] at h'
  -- `cdf x ≤ 1 - μ.real (Ici (x + 1))`, and the right side tends to `0`
  have hle : ∀ x, cdf μ x ≤ 1 - (μ : Measure ℝ).real (Ici (x + 1)) := by
    intro x
    have hdisj : Disjoint (Iic x) (Ici (x + 1)) := by
      rw [Set.disjoint_iff]
      intro y ⟨hy1, hy2⟩
      simp only [mem_Iic, mem_Ici] at hy1 hy2
      linarith
    have hunion := measureReal_union (μ := (μ : Measure ℝ)) hdisj measurableSet_Ici
    have hle1 : (μ : Measure ℝ).real (Iic x ∪ Ici (x + 1)) ≤ 1 := by
      rw [← probReal_univ (μ := (μ : Measure ℝ))]
      exact measureReal_mono (subset_univ _)
    unfold cdf
    linarith
  have hlim : Tendsto (fun x ↦ 1 - (μ : Measure ℝ).real (Ici (x + 1))) atBot (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ ↦ (μ : Measure ℝ).real (Ici (x + 1))) atBot (𝓝 1) := by
      refine h'.comp ?_
      exact tendsto_atBot_add_const_right _ _ tendsto_id
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun x ↦ cdf_nonneg μ x) hle

/-- Points of the interior of the support have distribution value strictly between zero and
one. -/
theorem cdf_pos_of_mem_interior_support {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) :
    0 < cdf μ x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hy : x - ε / 2 ∈ (μ : Measure ℝ).support :=
    interior_subset
      (hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith))
  have hpos : 0 < (μ : Measure ℝ) (Iio x) :=
    (Measure.mem_support_iff_forall _).mp hy (Iio x) (Iio_mem_nhds (by linarith))
  unfold cdf
  rw [measureReal_def]
  exact
    ENNReal.toReal_pos (ne_of_gt (hpos.trans_le (measure_mono Iio_subset_Iic_self)))
      (measure_ne_top _ _)

theorem cdf_lt_one_of_mem_interior_support {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) :
    cdf μ x < 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hy : x + ε / 2 ∈ (μ : Measure ℝ).support :=
    interior_subset
      (hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith))
  have hpos : 0 < (μ : Measure ℝ) (Ioi x) :=
    (Measure.mem_support_iff_forall _).mp hy (Ioi x) (Ioi_mem_nhds (by linarith))
  have h := measureReal_Ioi μ x
  have hpos' : 0 < (μ : Measure ℝ).real (Ioi x) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  linarith

section Density

variable {ρ : ℝ → ℝ}
  (hμ : (μ : Measure ℝ) = volume.withDensity fun x ↦ ENNReal.ofReal (ρ x))
  (hmeas : Measurable ρ) (hnn : ∀ x, 0 ≤ ρ x)

include hμ hmeas hnn

/-- The density has total integral one, hence is integrable. -/
theorem integrable_density : Integrable ρ volume := by
  have htot : ∫⁻ x, ENNReal.ofReal (ρ x) = 1 := by
    have h := congrArg (fun m : Measure ℝ ↦ m univ) hμ
    simp only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h.symm
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn), htot]
  exact ENNReal.one_lt_top

/-- The mass of a measurable set is the integral of the density over it. -/
theorem measureReal_eq_setIntegral {s : Set ℝ} (hs : MeasurableSet s) :
    (μ : Measure ℝ).real s = ∫ x in s, ρ x := by
  rw [measureReal_def, hμ, withDensity_apply _ hs,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ hnn x)
      hmeas.aestronglyMeasurable.restrict]

/-- The increment of the distribution function is the interval integral of the density. -/
theorem cdf_sub_cdf_eq_integral {x y : ℝ} (hxy : x ≤ y) :
    cdf μ y - cdf μ x = ∫ t in x..y, ρ t := by
  rw [cdf_sub_cdf μ hxy, measureReal_eq_setIntegral μ hμ hmeas hnn measurableSet_Ioc,
    intervalIntegral.integral_of_le hxy]

/-- The distribution function is a primitive of the density. -/
theorem cdf_eq_add_integral (x₀ x : ℝ) : cdf μ x = cdf μ x₀ + ∫ t in x₀..x, ρ t := by
  rcases le_total x₀ x with h | h
  · rw [← cdf_sub_cdf_eq_integral μ hμ hmeas hnn h]
    ring
  · rw [intervalIntegral.integral_symm, ← cdf_sub_cdf_eq_integral μ hμ hmeas hnn h]
    ring

/-- The distribution function of a law with a density is continuous. -/
theorem continuous_cdf : Continuous (cdf μ) := by
  have hint : ∀ a b, IntervalIntegrable ρ volume a b :=
    fun a b ↦ (integrable_density μ hμ hmeas hnn).intervalIntegrable
  have h : cdf μ = fun x ↦ cdf μ 0 + ∫ t in (0 : ℝ)..x, ρ t := by
    funext x
    exact cdf_eq_add_integral μ hμ hmeas hnn 0 x
  rw [h]
  exact continuous_const.add (intervalIntegral.continuous_primitive hint 0)

/-- At a continuity point of the density, the distribution function has that derivative. -/
theorem hasDerivAt_cdf {x : ℝ} (hc : ContinuousAt ρ x) : HasDerivAt (cdf μ) (ρ x) x := by
  have h : cdf μ = fun y ↦ cdf μ 0 + ∫ t in (0 : ℝ)..y, ρ t := by
    funext y
    exact cdf_eq_add_integral μ hμ hmeas hnn 0 y
  rw [h]
  refine (intervalIntegral.integral_hasDerivAt_right
    (integrable_density μ hμ hmeas hnn).intervalIntegrable
    hmeas.stronglyMeasurable.stronglyMeasurableAtFilter hc).const_add _

/-- Every level strictly between zero and one is attained by the distribution function. -/
theorem exists_cdf_eq {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : ∃ m, cdf μ m = t := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds h0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds h1)).exists
  exact intermediate_value_univ₂ (continuous_cdf μ hμ hmeas hnn) continuous_const ha.le hb.le

/-- A law with a density has a median. -/
theorem exists_cdf_eq_half : ∃ m, cdf μ m = 1 / 2 :=
  exists_cdf_eq μ hμ hmeas hnn (by norm_num) (by norm_num)

omit hmeas hnn in
/-- Singletons are null for a law with a density. -/
theorem measure_singleton_eq_zero (x : ℝ) : (μ : Measure ℝ) {x} = 0 := by
  rw [hμ]
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- The distribution function pushes the law forward to the uniform law on `[0, 1]`. -/
theorem map_cdf_eq_uniform :
    (μ : Measure ℝ).map (cdf μ) = volume.restrict (Icc (0 : ℝ) 1) := by
  have hcont := continuous_cdf μ hμ hmeas hnn
  have hmeasF : Measurable (cdf μ) := (cdf_mono μ).measurable
  refine Measure.ext_of_Iic _ _ fun t ↦ ?_
  rw [Measure.map_apply hmeasF measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge t 0 with ht | ht
  · have h1 : cdf μ ⁻¹' Iic t = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      exact ht.trans_le (cdf_nonneg μ x)
    have h2 : Iic t ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      intro h
      linarith [h.1, h.2.1]
    rw [h1, h2, measure_empty, measure_empty]
  rcases le_or_gt 1 t with ht1 | ht1
  · have h1 : cdf μ ⁻¹' Iic t = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (cdf_le_one μ x).trans ht1
    have h2 : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨h.2.trans ht1, h⟩
    rw [h1, h2, measure_univ, Real.volume_Icc]
    simp
  · -- `0 ≤ t < 1`
    have h2 : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · exact fun h ↦ ⟨h.2.1, h.1⟩
      · exact fun h ↦ ⟨h.2, h.1, h.2.trans ht1.le⟩
    rw [h2, Real.volume_Icc, sub_zero]
    set S := cdf μ ⁻¹' Iic t with hS
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · rw [hSe, measure_empty]
      -- then `t = 0`: otherwise the distribution function eventually lies below `t`
      have ht0 : t = 0 := by
        by_contra hne
        have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hne)
        obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds htpos)).exists
        have : a ∈ S := ha.le
        rw [hSe] at this
        exact this
      rw [ht0]
      simp
    · have hclosed : IsClosed S := isClosed_Iic.preimage hcont
      have hbdd : BddAbove S := by
        obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds ht1)).exists
        refine ⟨b, fun x hx ↦ ?_⟩
        by_contra hlt
        push Not at hlt
        have : cdf μ x ≤ t := hx
        exact absurd (hb.trans_le ((cdf_mono μ) hlt.le)) (not_lt.mpr this)
      set m := sSup S with hm
      have hmS : m ∈ S := hclosed.csSup_mem hSne hbdd
      have hSeq : S = Iic m := by
        ext x
        constructor
        · intro hx
          exact le_csSup hbdd hx
        · intro hx
          have : cdf μ x ≤ cdf μ m := (cdf_mono μ) hx
          exact this.trans hmS
      have hFm : cdf μ m = t := by
        refine le_antisymm hmS ?_
        by_contra hlt
        push Not at hlt
        obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := m))
          (t - cdf μ m) (sub_pos.mpr hlt)
        have hmem : m + ε / 2 ∈ S := by
          have hd : dist (m + ε / 2) m < ε := by
            rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
            linarith
          have h := hball hd
          rw [Real.dist_eq, abs_lt] at h
          show cdf μ (m + ε / 2) ≤ t
          linarith [h.2]
        have := le_csSup hbdd hmem
        linarith [half_pos hε]
      rw [hSeq, ← hFm]
      unfold cdf
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The distribution function of the law has mean `1/2`. -/
theorem integral_cdf : ∫ x, cdf μ x ∂(μ : Measure ℝ) = 1 / 2 := by
  have hmeasF : Measurable (cdf μ) := (cdf_mono μ).measurable
  have h := integral_map (φ := cdf μ) (μ := (μ : Measure ℝ)) hmeasF.aemeasurable
    (f := fun u : ℝ ↦ u) (aestronglyMeasurable_id)
  rw [map_cdf_eq_uniform μ hμ hmeas hnn] at h
  rw [← h, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_id]
  norm_num

/-- The centered distribution function has second moment `1/12`. -/
theorem integral_cdf_sub_half_sq :
    ∫ x, (cdf μ x - 1 / 2) ^ 2 ∂(μ : Measure ℝ) = 1 / 12 := by
  have hmeasF : Measurable (cdf μ) := (cdf_mono μ).measurable
  have h := integral_map (φ := cdf μ) (μ := (μ : Measure ℝ)) hmeasF.aemeasurable
    (f := fun u : ℝ ↦ (u - 1 / 2) ^ 2)
    ((measurable_id.sub_const _).pow_const 2).aestronglyMeasurable
  rw [map_cdf_eq_uniform μ hμ hmeas hnn] at h
  rw [← h, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_right (fun u : ℝ ↦ u ^ 2), integral_pow]
  norm_num

/-- The centered distribution function has vanishing third moment. -/
theorem integral_cdf_sub_half_cube :
    ∫ x, (cdf μ x - 1 / 2) ^ 3 ∂(μ : Measure ℝ) = 0 := by
  have hmeasF : Measurable (cdf μ) := (cdf_mono μ).measurable
  have h := integral_map (φ := cdf μ) (μ := (μ : Measure ℝ)) hmeasF.aemeasurable
    (f := fun u : ℝ ↦ (u - 1 / 2) ^ 3)
    ((measurable_id.sub_const _).pow_const 3).aestronglyMeasurable
  rw [map_cdf_eq_uniform μ hμ hmeas hnn] at h
  rw [← h, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_right (fun u : ℝ ↦ u ^ 3), integral_pow]
  norm_num

/-- Continuous functions of the distribution function are integrable. -/
theorem integrable_comp_cdf {p : ℝ → ℝ} (hp : Continuous p) :
    Integrable (fun x ↦ p (cdf μ x)) (μ : Measure ℝ) := by
  have hmeasF : Measurable (cdf μ) := (cdf_mono μ).measurable
  have h := (integrable_map_measure (μ := (μ : Measure ℝ)) (f := cdf μ) (g := p)
    hp.aestronglyMeasurable hmeasF.aemeasurable).mp
  rw [map_cdf_eq_uniform μ hμ hmeas hnn] at h
  exact h hp.integrableOn_Icc

end Density

end FunctionalInequalities.Probability.Line

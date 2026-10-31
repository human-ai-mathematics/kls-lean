module

public import FunctionalInequalities.KLS.LogConcave.Line.Density
public import FunctionalInequalities.Probability.Line.ExpIntegral

/-!
# Hazard-rate monotonicity and median bounds for log-concave laws on the line

Source: Blueprint `thm:one-dimensional-logconcave-poincare`, supporting estimates (compare
Bobkov 1999, Section 4, and the classical hazard-rate monotonicity of log-concave densities). Read
`LineDensity.mul_le_mul_of_add_eq`, the hazard inequalities `LineDensity.mul_measureReal_Ioi_le`
and `LineDensity.mul_cdf_le`, the median bounds `LineDensity.two_mul_measureReal_Ioi_le` and
`LineDensity.two_mul_cdf_le`, and the supporting-line bound `LineDensity.le_add_mul_cdf_sub`.

For a Borell density `ρ` of a log-concave law with distribution function `F` and median `m` with
`c = ρ m`, the four-point inequality `ρ a · ρ e ≤ ρ b · ρ c` for `a ≤ b ≤ c ≤ e`, `a + e = b + c`
gives monotone hazard rates: `ρ x · (1 - F y) ≤ ρ y · (1 - F x)` and `ρ y · F x ≤ ρ x · F y` for
`x ≤ y` (with the outer point in the interior of the support). At the median these read
`2 c (1 - F x) ≤ ρ x` for every `x ≥ m` and `2 c F x ≤ ρ x` for every `x ≤ m`. A supporting
exponential `ρ s ≤ c · exp (k (s - m))` at the median, integrated against
the chord bounds, gives the supporting-line bound `ρ x ≤ c + k (F x - 1/2)` on the interior of
the support.

Nothing here is a Poincaré inequality; these bounds feed the Hardy and variance modules.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open FunctionalInequalities.Probability.Line (cdf)

namespace FunctionalInequalities.KLS.LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ)

/-- The density is Lebesgue integrable. -/
theorem integrable : Integrable d.ρ volume :=
  Probability.Line.integrable_density μ d.withDensity_eq d.measurable d.nonneg

/-- The real measure of a set is the Lebesgue integral of the density. -/
theorem measureReal_eq_setIntegral {s : Set ℝ} (hs : MeasurableSet s) :
    (μ : Measure ℝ).real s = ∫ x in s, d.ρ x :=
  Probability.Line.measureReal_eq_setIntegral μ d.withDensity_eq d.measurable d.nonneg hs

/-- Distribution increments are interval integrals of the density. -/
theorem cdf_sub_cdf_eq_integral {x y : ℝ} (hxy : x ≤ y) :
    cdf μ y - cdf μ x = ∫ t in x..y, d.ρ t :=
  Probability.Line.cdf_sub_cdf_eq_integral μ d.withDensity_eq d.measurable d.nonneg hxy

include d in
/-- The distribution function is continuous. -/
theorem continuous_cdf : Continuous (cdf μ) :=
  Probability.Line.continuous_cdf μ d.withDensity_eq d.measurable d.nonneg

/-- The distribution function has derivative `ρ` on the interior of the support. -/
theorem hasDerivAt_cdf {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) :
    HasDerivAt (cdf μ) (d.ρ x) x :=
  Probability.Line.hasDerivAt_cdf μ d.withDensity_eq d.measurable d.nonneg
    (d.continuousOn.continuousAt (isOpen_interior.mem_nhds hx))

include d in
/-- A median exists. -/
theorem exists_median : ∃ m, cdf μ m = 1 / 2 :=
  Probability.Line.exists_cdf_eq_half μ d.withDensity_eq d.measurable d.nonneg

section FourPoint

variable (hμ : LogConcave μ)
include hμ

/-- The four-point inequality of log-concavity: `ρ a · ρ e ≤ ρ b · ρ c` whenever
`a ≤ b ≤ c ≤ e`, `a + e = b + c`, and the outer points lie in the interior of the support. -/
theorem mul_le_mul_of_add_eq {a b c e : ℝ} (ha : a ∈ interior (μ : Measure ℝ).support)
    (he : e ∈ interior (μ : Measure ℝ).support) (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e)
    (hsum : a + e = b + c) : d.ρ a * d.ρ e ≤ d.ρ b * d.ρ c := by
  have hconv := hμ.convex_interior_support
  have hb : b ∈ interior (μ : Measure ℝ).support :=
    hconv.ordConnected.out ha he ⟨hab, hbc.trans hce⟩
  have hc : c ∈ interior (μ : Measure ℝ).support :=
    hconv.ordConnected.out ha he ⟨hab.trans hbc, hce⟩
  rcases eq_or_lt_of_le (hab.trans (hbc.trans hce)) with hae | hae
  · have hb' : b = a := le_antisymm (by linarith) hab
    have hc' : c = a := le_antisymm (by linarith) (hab.trans hbc)
    rw [hb', hc', ← hae]
  · have hconc := d.concaveOn_log hμ
    set θ : ℝ := (e - b) / (e - a) with hθ
    have hea : 0 < e - a := sub_pos.mpr hae
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hea.le
    have hθ1 : 0 ≤ 1 - θ := by
      rw [sub_nonneg, hθ, div_le_one hea]
      linarith
    have hθmul : θ * (e - a) = e - b := by
      rw [hθ]
      field_simp
    have hb_eq : θ • a + (1 - θ) • e = b := by
      simp only [smul_eq_mul]
      linear_combination (-1 : ℝ) * hθmul
    have hc_eq : (1 - θ) • a + θ • e = c := by
      simp only [smul_eq_mul]
      linear_combination hθmul + hsum
    have h1 := hconc.2 ha he hθ0 hθ1 (by ring)
    have h2 := hconc.2 ha he hθ1 hθ0 (by ring)
    rw [hb_eq] at h1
    rw [hc_eq] at h2
    simp only [smul_eq_mul] at h1 h2
    have hlog : Real.log (d.ρ a) + Real.log (d.ρ e) ≤ Real.log (d.ρ b) + Real.log (d.ρ c) := by
      linarith
    calc d.ρ a * d.ρ e = Real.exp (Real.log (d.ρ a) + Real.log (d.ρ e)) := by
          rw [Real.exp_add, Real.exp_log (d.pos ha), Real.exp_log (d.pos he)]
      _ ≤ Real.exp (Real.log (d.ρ b) + Real.log (d.ρ c)) := Real.exp_le_exp.mpr hlog
      _ = d.ρ b * d.ρ c := by
          rw [Real.exp_add, Real.exp_log (d.pos hb), Real.exp_log (d.pos hc)]

end FourPoint

section Hazard

variable (hμ : LogConcave μ) (hi : (interior (μ : Measure ℝ).support).Nonempty)
include hμ hi

/-- Monotone hazard rate: for `x ≤ y` with `x` in the interior of the support,
`ρ x · μ(Ioi y) ≤ ρ y · μ(Ioi x)`. -/
theorem mul_measureReal_Ioi_le {x y : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support)
    (hxy : x ≤ y) :
    d.ρ x * (μ : Measure ℝ).real (Ioi y) ≤ d.ρ y * (μ : Measure ℝ).real (Ioi x) := by
  set δ := y - x with hδ
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hxy
  rw [d.measureReal_eq_setIntegral measurableSet_Ioi,
    d.measureReal_eq_setIntegral measurableSet_Ioi]
  have htrans : ∫ s in Ioi y, d.ρ s = ∫ s in Ioi x, d.ρ (s + δ) := by
    have hpre : (fun s : ℝ ↦ s + δ) ⁻¹' Ioi y = Ioi x := by
      ext s
      simp only [mem_preimage, mem_Ioi, hδ]
      constructor <;> intro h <;> linarith
    rw [←
      (measurePreserving_add_right volume δ).setIntegral_preimage_emb
        (measurableEmbedding_addRight δ) d.ρ (Ioi y),
      hpre]
  rw [htrans, ← integral_const_mul, ← integral_const_mul]
  have hae :=
    (measurePreserving_add_right volume δ).quasiMeasurePreserving.ae
      (d.ae_eq_zero_of_not_mem_interior_support hμ hi)
  refine
    integral_mono_ae ((d.integrable.comp_add_right δ).const_mul _).integrableOn
      (d.integrable.const_mul _).integrableOn ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hae] with s hs hsx
  have hsx' : x < s := hsx
  by_cases hsΩ : s + δ ∈ interior (μ : Measure ℝ).support
  · rcases le_total y s with hys | hsy
    · exact d.mul_le_mul_of_add_eq hμ hx hsΩ hxy hys (by linarith) (by rw [hδ]; ring)
    · have :=
        d.mul_le_mul_of_add_eq hμ hx hsΩ (le_of_lt hsx) hsy (by linarith) (by rw [hδ]; ring)
      linarith
  · rw [hs hsΩ, mul_zero]
    exact mul_nonneg (d.nonneg _) (d.nonneg _)

/-- Monotone reversed hazard rate: for `x ≤ y` with `y` in the interior of the support,
`ρ y · F x ≤ ρ x · F y`. -/
theorem mul_cdf_le {x y : ℝ} (hy : y ∈ interior (μ : Measure ℝ).support) (hxy : x ≤ y) :
    d.ρ y * cdf μ x ≤ d.ρ x * cdf μ y := by
  set δ := y - x with hδ
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hxy
  unfold cdf
  rw [d.measureReal_eq_setIntegral measurableSet_Iic,
    d.measureReal_eq_setIntegral measurableSet_Iic]
  have htrans : ∫ s in Iic x, d.ρ s = ∫ s in Iic y, d.ρ (s + -δ) := by
    have hpre : (fun s : ℝ ↦ s + -δ) ⁻¹' Iic x = Iic y := by
      ext s
      simp only [mem_preimage, mem_Iic, hδ]
      constructor <;> intro h <;> linarith
    rw [←
      (measurePreserving_add_right volume (-δ)).setIntegral_preimage_emb
        (measurableEmbedding_addRight (-δ)) d.ρ (Iic x),
      hpre]
  rw [htrans, ← integral_const_mul, ← integral_const_mul]
  have hae :=
    (measurePreserving_add_right volume (-δ)).quasiMeasurePreserving.ae
      (d.ae_eq_zero_of_not_mem_interior_support hμ hi)
  refine
    integral_mono_ae ((d.integrable.comp_add_right (-δ)).const_mul _).integrableOn
      (d.integrable.const_mul _).integrableOn ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Iic]
  filter_upwards [hae] with s hs hsy
  have hsy' : s ≤ y := hsy
  by_cases hsΩ : s + -δ ∈ interior (μ : Measure ℝ).support
  · rcases le_total x s with hxs | hsx
    · have := d.mul_le_mul_of_add_eq hμ hsΩ hy (by linarith) hxs hsy (by rw [hδ]; ring)
      linarith
    · have := d.mul_le_mul_of_add_eq hμ hsΩ hy (by linarith) hsx hxy (by rw [hδ]; ring)
      linarith
  · rw [hs hsΩ, mul_zero]
    exact mul_nonneg (d.nonneg _) (d.nonneg _)

end Hazard

section Median

variable (hμ : LogConcave μ) (hi : (interior (μ : Measure ℝ).support).Nonempty)
  {m : ℝ} (hm : cdf μ m = 1 / 2)
include hμ hi hm

section MedianCdf

omit hμ hi
/-- The distribution function of a point in the interior of the support to the right of the
median is at least one half. -/
theorem half_le_cdf_of_le {x : ℝ} (hmx : m ≤ x) : 1 / 2 ≤ cdf μ x := by
  have := Probability.Line.cdf_mono μ hmx
  rwa [hm] at this

/-- The distribution function to the left of the median is at most one half. -/
theorem cdf_le_half_of_le {x : ℝ} (hxm : x ≤ m) : cdf μ x ≤ 1 / 2 := by
  have := Probability.Line.cdf_mono μ hxm
  rwa [hm] at this

end MedianCdf

/-- A median lies in the interior of the support. -/
theorem median_mem : m ∈ interior (μ : Measure ℝ).support :=
  hμ.mem_interior_support_of_cdf hi (by rw [hm]; norm_num) (by rw [hm]; norm_num)

/-- To the right of the median, `2 ρ(m) · μ(Ioi x) ≤ ρ x`. -/
theorem two_mul_measureReal_Ioi_le {x : ℝ} (hmx : m ≤ x) :
    2 * d.ρ m * (μ : Measure ℝ).real (Ioi x) ≤ d.ρ x := by
  have h := d.mul_measureReal_Ioi_le hμ hi (median_mem hμ hi hm) hmx
  rw [Probability.Line.measureReal_Ioi μ m, hm] at h
  linarith

/-- To the left of the median, `2 ρ(m) · F x ≤ ρ x`. -/
theorem two_mul_cdf_le {x : ℝ} (hxm : x ≤ m) : 2 * d.ρ m * cdf μ x ≤ d.ρ x := by
  have h := d.mul_cdf_le hμ hi (median_mem hμ hi hm) hxm
  rw [hm] at h
  linarith

end Median

section SupportingLine

variable (hμ : LogConcave μ)
include hμ

/-- The chord lower bound integrated over `[x, y]`. -/
theorem integral_exp_le_cdf_sub {x y : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support)
    (hy : y ∈ interior (μ : Measure ℝ).support) (hxy : x < y) :
    ∫ s in x..y, d.ρ x * Real.exp (d.logSlope x y * (s - x)) ≤ cdf μ y - cdf μ x := by
  rw [d.cdf_sub_cdf_eq_integral hxy.le]
  exact intervalIntegral.integral_mono_on hxy.le
    (Continuous.intervalIntegrable (by fun_prop) _ _) d.integrable.intervalIntegrable
    (fun s hs ↦ d.mul_exp_le_of_mem_Icc hμ hx hy hxy hs)

/-- A supporting exponential integrated over `[x, y]` dominates the distribution increment. -/
theorem cdf_sub_le_integral_exp {x₀ k : ℝ}
    (hk : ∀ s ∈ interior (μ : Measure ℝ).support, d.ρ s ≤ d.ρ x₀ * Real.exp (k * (s - x₀)))
    {x y : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support)
    (hy : y ∈ interior (μ : Measure ℝ).support) (hxy : x ≤ y) :
    cdf μ y - cdf μ x ≤ ∫ s in x..y, d.ρ x₀ * Real.exp (k * (s - x₀)) := by
  rw [d.cdf_sub_cdf_eq_integral hxy]
  exact intervalIntegral.integral_mono_on hxy d.integrable.intervalIntegrable
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (fun s hs ↦ hk s (hμ.convex_interior_support.ordConnected.out hx hy hs))

omit hμ in
/-- Logarithmic form of an exponential upper bound. -/
theorem log_le_of_le_mul_exp {x₀ x k : ℝ} (h0 : 0 < d.ρ x₀) (hx : 0 < d.ρ x)
    (h : d.ρ x ≤ d.ρ x₀ * Real.exp (k * (x - x₀))) :
    Real.log (d.ρ x) ≤ Real.log (d.ρ x₀) + k * (x - x₀) := by
  calc Real.log (d.ρ x) ≤ Real.log (d.ρ x₀ * Real.exp (k * (x - x₀))) := Real.log_le_log hx h
    _ = Real.log (d.ρ x₀) + k * (x - x₀) := by
        rw [Real.log_mul h0.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- Supporting-line bound at an arbitrary anchor: a supporting exponential of the density at
`x₀ ∈ Ω` with slope `k` gives `ρ x ≤ ρ x₀ + k (F x - F x₀)` on the interior of the support. -/
theorem le_add_mul_cdf_sub_of_mem {m : ℝ} (hmΩ : m ∈ interior (μ : Measure ℝ).support) {k : ℝ}
    (hk : ∀ s ∈ interior (μ : Measure ℝ).support, d.ρ s ≤ d.ρ m * Real.exp (k * (s - m)))
    {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) :
    d.ρ x ≤ d.ρ m + k * (cdf μ x - cdf μ m) := by
  have hc : 0 < d.ρ m := d.pos hmΩ
  have hρx : 0 < d.ρ x := d.pos hx
  rcases lt_trichotomy x m with hxm | hxm | hmx
  · have hF : cdf μ x ≤ cdf μ m := Probability.Line.cdf_mono μ hxm.le
    rcases le_or_gt k 0 with hk0 | hk0
    · by_cases hρ : d.ρ x ≤ d.ρ m
      · nlinarith [mul_nonneg_of_nonpos_of_nonpos hk0 (by linarith : cdf μ x - cdf μ m ≤ 0)]
      · push Not at hρ
        set κ := d.logSlope x m with hκ
        have hκeq : Real.log (d.ρ m) = Real.log (d.ρ x) + κ * (m - x) :=
          d.log_eq_add_logSlope_mul hxm.ne
        have hmx' : 0 < m - x := by linarith
        have hκneg : κ < 0 := by
          have : Real.log (d.ρ m) < Real.log (d.ρ x) := Real.log_lt_log hc hρ
          by_contra hcon
          push Not at hcon
          nlinarith
        have hkκ : k ≤ κ := by
          have h2 := d.log_le_of_le_mul_exp hc hρx (hk x hx)
          by_contra hcon
          push Not at hcon
          nlinarith
        have hchord := d.integral_exp_le_cdf_sub hμ hx hmΩ hxm
        rw [Probability.Line.integral_exp_affine (d.ρ x) κ x x m hκneg.ne] at hchord
        simp only [sub_self, mul_zero, Real.exp_zero] at hchord
        have hexp : d.ρ x * Real.exp (κ * (m - x)) = d.ρ m := by
          rw [← Real.exp_log hc, hκeq, Real.exp_add, Real.exp_log hρx]
        have hval : d.ρ x / κ * (Real.exp (κ * (m - x)) - 1) = (d.ρ m - d.ρ x) / κ := by
          rw [div_mul_eq_mul_div, mul_sub, hexp, mul_one]
        rw [hval] at hchord
        have h3 := (div_le_iff_of_neg hκneg).mp hchord
        nlinarith [mul_le_mul_of_nonneg_right hkκ (by linarith : 0 ≤ cdf μ m - cdf μ x)]
    · have htan := d.cdf_sub_le_integral_exp hμ hk hx hmΩ hxm.le
      rw [Probability.Line.integral_exp_affine (d.ρ m) k m x m hk0.ne'] at htan
      simp only [sub_self, mul_zero, Real.exp_zero] at htan
      have h1 := hk x hx
      have h2 : k * (cdf μ m - cdf μ x) ≤ d.ρ m * (1 - Real.exp (k * (x - m))) := by
        have := mul_le_mul_of_nonneg_left htan hk0.le
        have heq : k * (d.ρ m / k * (1 - Real.exp (k * (x - m)))) =
            d.ρ m * (1 - Real.exp (k * (x - m))) := by
          field_simp
        linarith
      linarith
  · subst hxm
    simp
  · have hF : cdf μ m ≤ cdf μ x := Probability.Line.cdf_mono μ hmx.le
    rcases le_or_gt 0 k with hk0 | hk0
    · by_cases hρ : d.ρ x ≤ d.ρ m
      · nlinarith [mul_nonneg hk0 (by linarith : 0 ≤ cdf μ x - cdf μ m)]
      · push Not at hρ
        set κ := d.logSlope m x with hκ
        have hκeq : Real.log (d.ρ x) = Real.log (d.ρ m) + κ * (x - m) :=
          d.log_eq_add_logSlope_mul hmx.ne
        have hxm' : 0 < x - m := by linarith
        have hκpos : 0 < κ := by
          have : Real.log (d.ρ m) < Real.log (d.ρ x) := Real.log_lt_log hc hρ
          by_contra hcon
          push Not at hcon
          nlinarith
        have hκk : κ ≤ k := by
          have h2 := d.log_le_of_le_mul_exp hc hρx (hk x hx)
          by_contra hcon
          push Not at hcon
          nlinarith
        have hchord := d.integral_exp_le_cdf_sub hμ hmΩ hx hmx
        rw [Probability.Line.integral_exp_affine (d.ρ m) κ m m x hκpos.ne'] at hchord
        simp only [sub_self, mul_zero, Real.exp_zero] at hchord
        have hexp : d.ρ m * Real.exp (κ * (x - m)) = d.ρ x := by
          rw [← Real.exp_log hρx, hκeq, Real.exp_add, Real.exp_log hc]
        have hval : d.ρ m / κ * (Real.exp (κ * (x - m)) - 1) = (d.ρ x - d.ρ m) / κ := by
          rw [div_mul_eq_mul_div, mul_sub, hexp, mul_one]
        rw [hval] at hchord
        have h3 := (div_le_iff₀ hκpos).mp hchord
        nlinarith [mul_le_mul_of_nonneg_left hκk (by linarith : 0 ≤ cdf μ x - cdf μ m)]
    · have htan := d.cdf_sub_le_integral_exp hμ hk hmΩ hx hmx.le
      rw [Probability.Line.integral_exp_affine (d.ρ m) k m m x hk0.ne] at htan
      simp only [sub_self, mul_zero, Real.exp_zero] at htan
      have h1 := hk x hx
      have h2 : d.ρ m * (Real.exp (k * (x - m)) - 1) ≤ k * (cdf μ x - cdf μ m) := by
        have := mul_le_mul_of_nonpos_left htan hk0.le
        have hk0' : k ≠ 0 := hk0.ne
        have heq : k * (d.ρ m / k * (Real.exp (k * (x - m)) - 1)) =
            d.ρ m * (Real.exp (k * (x - m)) - 1) := by
          field_simp
        linarith
      linarith

/-- Supporting-line bound: a supporting exponential of the density at the median `m` with
slope `k` gives `ρ x ≤ ρ m + k (F x - 1/2)` on the interior of the support. -/
theorem le_add_mul_cdf_sub (hi : (interior (μ : Measure ℝ).support).Nonempty) {m : ℝ}
    (hm : cdf μ m = 1 / 2) {k : ℝ}
    (hk : ∀ s ∈ interior (μ : Measure ℝ).support, d.ρ s ≤ d.ρ m * Real.exp (k * (s - m)))
    {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) :
    d.ρ x ≤ d.ρ m + k * (cdf μ x - 1 / 2) := by
  have h := d.le_add_mul_cdf_sub_of_mem hμ (median_mem hμ hi hm) hk hx
  rwa [hm] at h

end SupportingLine

end FunctionalInequalities.KLS.LineDensity

import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation
import FunctionalInequalities.Probability.Line.Cdf
import Mathlib.Analysis.Convex.Slope

/-!
# Log-concave laws on the real line: density, support interval and chord bounds

Source: Blueprint `thm:one-dimensional-logconcave-poincare`, supporting structure. Read
`LineDensity`, `LogConcave.exists_lineDensity`, the interior-support lemmas
(`LogConcave.measure_compl_interior_support`, `LogConcave.mem_interior_support_of_cdf`), then the
chord and tangent bounds (`LineDensity.mul_exp_le_of_mem_Icc`, `LineDensity.le_mul_exp_of_not_mem_Ioo`,
`LineDensity.exists_supergradient`).

For a compact-set log-concave probability law `μ` on `ℝ` whose support has nonempty interior `Ω`
(an open interval), the Borell representation gives a Lebesgue density `ρ` that is continuous and
positive on `Ω` with concave logarithm, while `μ (Ωᶜ) = 0` and `ρ` vanishes almost everywhere off
`Ω`. Every point with distribution value strictly between `0` and `1` lies in `Ω`; in particular
every median does. Concavity of `log ρ` gives, for `x < y` in `Ω` with `κ` the logarithmic slope
between them, the lower chord bound `ρ x · exp (κ (s - x)) ≤ ρ s` on `[x, y]` and the upper
extrapolation bound `ρ s ≤ ρ x · exp (κ (s - x))` at points of `Ω` outside `(x, y)`, and at every
point `m` of `Ω` a supporting exponential `ρ s ≤ ρ m · exp (k (s - m))`.

Nothing here is a Poincaré inequality; these are the pointwise inputs of the hazard-rate and
variance estimates of the following modules.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace FunctionalInequalities.KLS

/-- The Borell density data of a log-concave law on the real line. -/
structure LineDensity (μ : ProbabilityMeasure ℝ) where
  /-- The Lebesgue density representative. -/
  ρ : ℝ → ℝ
  /-- The representative is a Borell density of `μ` with respect to Lebesgue measure. -/
  isBorell : IsBorellDensity (μ : Measure ℝ) volume ρ

namespace LogConcave

variable {μ : ProbabilityMeasure ℝ}

/-- A log-concave law on the line with support of nonempty interior has a Borell density. -/
theorem exists_lineDensity (hμ : LogConcave μ)
    (hi : (interior (μ : Measure ℝ).support).Nonempty) : Nonempty (LineDensity μ) := by
  obtain ⟨ρ, hρ⟩ := hμ.exists_isBorellDensity_of_interior_support_nonempty volume hi
    (hμ.absolutelyContinuous_of_interior_support_nonempty volume hi)
  exact ⟨⟨ρ, hρ⟩⟩

/-- The interior of the support is convex, hence an interval. -/
theorem convex_interior_support (hμ : LogConcave μ) :
    Convex ℝ (interior (μ : Measure ℝ).support) :=
  hμ.convex_support.interior

/-- The interior of the support carries the whole law: the support is convex, so its frontier is
Lebesgue-null, and the law is absolutely continuous. -/
theorem measure_compl_interior_support (hμ : LogConcave μ)
    (hi : (interior (μ : Measure ℝ).support).Nonempty) :
    (μ : Measure ℝ) (interior (μ : Measure ℝ).support)ᶜ = 0 := by
  have hac := hμ.absolutelyContinuous_of_interior_support_nonempty volume hi
  have hsub : (interior (μ : Measure ℝ).support)ᶜ ⊆
      ((μ : Measure ℝ).support)ᶜ ∪ frontier (μ : Measure ℝ).support := by
    intro x hx
    by_cases hs : x ∈ (μ : Measure ℝ).support
    · right
      rw [Measure.isClosed_support.frontier_eq]
      exact ⟨hs, hx⟩
    · exact Or.inl hs
  refine measure_mono_null hsub (measure_union_null Measure.measure_compl_support ?_)
  exact hac (hμ.convex_support.addHaar_frontier volume)

/-- Points with distribution value strictly between zero and one lie in the interior of the
support. -/
theorem mem_interior_support_of_cdf (hμ : LogConcave μ)
    (hi : (interior (μ : Measure ℝ).support).Nonempty) {x : ℝ}
    (h0 : 0 < Probability.Line.cdf μ x) (h1 : Probability.Line.cdf μ x < 1) :
    x ∈ interior (μ : Measure ℝ).support := by
  set Ω := interior (μ : Measure ℝ).support with hΩ
  have hnull : (μ : Measure ℝ).real Ωᶜ = 0 := by
    rw [measureReal_def, hμ.measure_compl_interior_support hi, ENNReal.toReal_zero]
  have hconv : Convex ℝ Ω := hμ.convex_interior_support
  by_contra hx
  -- either every point of `Ω` lies to the right of `x`, or every point lies to the left
  have hsides : (∀ ω ∈ Ω, x < ω) ∨ (∀ ω ∈ Ω, ω < x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨ω₁, hω₁, hle₁⟩, ⟨ω₂, hω₂, hle₂⟩⟩ := hcon
    exact hx (hconv.ordConnected.out hω₁ hω₂ ⟨hle₁, hle₂⟩)
  rcases hsides with hright | hleft
  · have hsub : Iic x ⊆ Ωᶜ := fun y hy hyΩ ↦ (hright y hyΩ).not_ge hy
    have : Probability.Line.cdf μ x ≤ 0 := by
      unfold Probability.Line.cdf
      rw [← hnull]
      exact measureReal_mono hsub
    exact absurd h0 (not_lt.mpr this)
  · have hsub : Ioi x ⊆ Ωᶜ := fun y hy hyΩ ↦ (hleft y hyΩ).not_ge (le_of_lt hy)
    have : (μ : Measure ℝ).real (Ioi x) ≤ 0 := by
      rw [← hnull]
      exact measureReal_mono hsub
    rw [Probability.Line.measureReal_Ioi] at this
    linarith

end LogConcave

namespace LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ)

theorem measurable : Measurable d.ρ := d.isBorell.measurable

theorem nonneg (x : ℝ) : 0 ≤ d.ρ x := d.isBorell.nonneg x

/-- The law is the Lebesgue density measure of `ρ`. -/
theorem withDensity_eq : (μ : Measure ℝ) = volume.withDensity fun x ↦ ENNReal.ofReal (d.ρ x) :=
  d.isBorell.withDensity_eq.symm

/-- The density is continuous on the interior of the support. -/
theorem continuousOn : ContinuousOn d.ρ (interior (μ : Measure ℝ).support) :=
  d.isBorell.continuousOn_interior_support

/-- The density is positive on the interior of the support. -/
theorem pos {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) : 0 < d.ρ x :=
  d.isBorell.pos_of_mem_interior_support hx

/-- The logarithm of the density is concave on the interior of the support. -/
theorem concaveOn_log (hμ : LogConcave μ) :
    ConcaveOn ℝ (interior (μ : Measure ℝ).support) fun x ↦ Real.log (d.ρ x) :=
  d.isBorell.concaveOn_log.subset (fun _ hx ↦ d.pos hx) hμ.convex_interior_support

/-- The density vanishes Lebesgue-almost everywhere off the interior of the support. -/
theorem ae_eq_zero_of_not_mem_interior_support (hμ : LogConcave μ)
    (hi : (interior (μ : Measure ℝ).support).Nonempty) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∉ interior (μ : Measure ℝ).support → d.ρ x = 0 := by
  set Ω := interior (μ : Measure ℝ).support with hΩ
  have h0 : (volume.withDensity fun x ↦ ENNReal.ofReal (d.ρ x)) Ωᶜ = 0 := by
    rw [← d.withDensity_eq]
    exact hμ.measure_compl_interior_support hi
  rw [withDensity_apply _ measurableSet_interior.compl,
    setLIntegral_eq_zero_iff' measurableSet_interior.compl
      d.measurable.ennreal_ofReal.aemeasurable] at h0
  filter_upwards [h0] with x hx hxΩ
  have := hx hxΩ
  rw [ENNReal.ofReal_eq_zero] at this
  exact le_antisymm this (d.nonneg x)

/-- The logarithmic slope of the density between two points. -/
def logSlope (x y : ℝ) : ℝ := (Real.log (d.ρ y) - Real.log (d.ρ x)) / (y - x)

theorem log_eq_add_logSlope_mul {x y : ℝ} (hxy : x ≠ y) :
    Real.log (d.ρ y) = Real.log (d.ρ x) + d.logSlope x y * (y - x) := by
  unfold logSlope
  have : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  field_simp
  ring

section Chord

variable (hμ : LogConcave μ)
include hμ

/-- Lower chord bound: on `[x, y]` the density dominates the exponential interpolation of its
endpoint values. -/
theorem mul_exp_le_of_mem_Icc {x y s : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support)
    (hy : y ∈ interior (μ : Measure ℝ).support) (hxy : x < y) (hs : s ∈ Icc x y) :
    d.ρ x * Real.exp (d.logSlope x y * (s - x)) ≤ d.ρ s := by
  have hconc := d.concaveOn_log hμ
  have hsΩ : s ∈ interior (μ : Measure ℝ).support :=
    hμ.convex_interior_support.ordConnected.out hx hy hs
  have hyx : 0 < y - x := sub_pos.mpr hxy
  set θ : ℝ := (s - x) / (y - x) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hs.1) hyx.le
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hyx]
    linarith [hs.2]
  have hcomb : (1 - θ) • x + θ • y = s := by
    simp only [smul_eq_mul, hθ]
    field_simp
    ring
  have h := hconc.2 hx hy (sub_nonneg.mpr hθ1) hθ0 (by ring)
  rw [hcomb] at h
  simp only [smul_eq_mul] at h
  have hslope : d.logSlope x y * (s - x) = θ * (Real.log (d.ρ y) - Real.log (d.ρ x)) := by
    unfold logSlope
    rw [hθ]
    field_simp
  have hlog : Real.log (d.ρ x) + d.logSlope x y * (s - x) ≤ Real.log (d.ρ s) := by
    rw [hslope]
    linarith
  calc d.ρ x * Real.exp (d.logSlope x y * (s - x))
      = Real.exp (Real.log (d.ρ x) + d.logSlope x y * (s - x)) := by
        rw [Real.exp_add, Real.exp_log (d.pos hx)]
    _ ≤ Real.exp (Real.log (d.ρ s)) := Real.exp_le_exp.mpr hlog
    _ = d.ρ s := Real.exp_log (d.pos hsΩ)

/-- Upper extrapolation bound: outside `(x, y)` the density lies below the exponential through
its values at `x` and `y`. -/
theorem le_mul_exp_of_not_mem_Ioo {x y s : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support)
    (hy : y ∈ interior (μ : Measure ℝ).support) (hxy : x < y)
    (hs : s ∈ interior (μ : Measure ℝ).support) (hs' : s ∉ Ioo x y) :
    d.ρ s ≤ d.ρ x * Real.exp (d.logSlope x y * (s - x)) := by
  have hconc := d.concaveOn_log hμ
  suffices hlog : Real.log (d.ρ s) ≤ Real.log (d.ρ x) + d.logSlope x y * (s - x) by
    calc d.ρ s = Real.exp (Real.log (d.ρ s)) := (Real.exp_log (d.pos hs)).symm
      _ ≤ Real.exp (Real.log (d.ρ x) + d.logSlope x y * (s - x)) := Real.exp_le_exp.mpr hlog
      _ = d.ρ x * Real.exp (d.logSlope x y * (s - x)) := by
        rw [Real.exp_add, Real.exp_log (d.pos hx)]
  have hyx : 0 < y - x := sub_pos.mpr hxy
  have hκ : d.logSlope x y * (y - x) = Real.log (d.ρ y) - Real.log (d.ρ x) := by
    unfold logSlope
    field_simp
  rcases lt_or_ge s x with hsx | hsx
  · -- `s < x < y`: the slope over `[s, x]` is at least the slope over `[x, y]`
    have h := hconc.slope_anti_adjacent hs hy hsx hxy
    -- h : (log ρ y - log ρ x) / (y - x) ≤ (log ρ x - log ρ s) / (x - s)
    have hxs : 0 < x - s := sub_pos.mpr hsx
    rw [div_le_div_iff₀ hyx hxs] at h
    have hκ' : d.logSlope x y * (s - x) = -((Real.log (d.ρ y) - Real.log (d.ρ x)) * (x - s) / (y - x)) := by
      unfold logSlope
      field_simp
      ring
    rw [hκ']
    have : (Real.log (d.ρ y) - Real.log (d.ρ x)) * (x - s) / (y - x) ≤
        Real.log (d.ρ x) - Real.log (d.ρ s) := by
      rw [div_le_iff₀ hyx]
      linarith
    linarith
  · rcases eq_or_lt_of_le hsx with hsx' | hsx'
    · rw [← hsx']
      simp
    · have hsy : y ≤ s := by
        by_contra hlt
        push Not at hlt
        exact hs' ⟨hsx', hlt⟩
      rcases eq_or_lt_of_le hsy with hsy' | hsy'
      · subst hsy'
        linarith [hκ]
      · -- `x < y < s`: the slope over `[y, s]` is at most the slope over `[x, y]`
        have h := hconc.slope_anti_adjacent hx hs hxy hsy'
        have hsy0 : 0 < s - y := sub_pos.mpr hsy'
        rw [div_le_div_iff₀ hsy0 hyx] at h
        -- h : (log ρ s - log ρ y) * (y - x) ≤ (log ρ y - log ρ x) * (s - y)
        have hκ' : d.logSlope x y * (s - x) =
            (Real.log (d.ρ y) - Real.log (d.ρ x)) * (s - y) / (y - x) +
              (Real.log (d.ρ y) - Real.log (d.ρ x)) := by
          unfold logSlope
          field_simp
          ring
        rw [hκ']
        have : Real.log (d.ρ s) - Real.log (d.ρ y) ≤
            (Real.log (d.ρ y) - Real.log (d.ρ x)) * (s - y) / (y - x) := by
          rw [le_div_iff₀ hyx]
          linarith
        linarith

/-- A supporting exponential at an interior point: the density lies below `ρ m · exp (k (· - m))`
on the whole interior of the support, for a suitable slope `k`. -/
theorem exists_supergradient {m : ℝ} (hm : m ∈ interior (μ : Measure ℝ).support) :
    ∃ k : ℝ, ∀ s ∈ interior (μ : Measure ℝ).support,
      d.ρ s ≤ d.ρ m * Real.exp (k * (s - m)) := by
  have hconc := d.concaveOn_log hμ
  set Ω := interior (μ : Measure ℝ).support with hΩ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior m hm
  have hmem_right : m + ε / 2 ∈ Ω := hball (by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  have hmem_left : m - ε / 2 ∈ Ω := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  -- the set of right slopes
  set R : Set ℝ := (fun t ↦ d.logSlope m t) '' {t | t ∈ Ω ∧ m < t} with hR
  have hRne : R.Nonempty :=
    ⟨d.logSlope m (m + ε / 2), m + ε / 2, ⟨hmem_right, by linarith⟩, rfl⟩
  -- every left slope bounds every right slope
  have hbound : ∀ s ∈ Ω, s < m → ∀ t ∈ Ω, m < t → d.logSlope m t ≤ d.logSlope s m := by
    intro s hs hsm t ht hmt
    have h := hconc.slope_anti_adjacent hs ht hsm hmt
    exact h
  have hRbdd : BddAbove R := by
    refine ⟨d.logSlope (m - ε / 2) m, ?_⟩
    rintro _ ⟨t, ⟨ht, hmt⟩, rfl⟩
    exact hbound _ hmem_left (by linarith) t ht hmt
  refine ⟨sSup R, fun s hs ↦ ?_⟩
  suffices hlog : Real.log (d.ρ s) ≤ Real.log (d.ρ m) + sSup R * (s - m) by
    calc d.ρ s = Real.exp (Real.log (d.ρ s)) := (Real.exp_log (d.pos hs)).symm
      _ ≤ Real.exp (Real.log (d.ρ m) + sSup R * (s - m)) := Real.exp_le_exp.mpr hlog
      _ = d.ρ m * Real.exp (sSup R * (s - m)) := by
        rw [Real.exp_add, Real.exp_log (d.pos hm)]
  rcases lt_trichotomy s m with hsm | hsm | hsm
  · -- left of `m`: the slope over `[s, m]` bounds `sSup R` from above
    have hk : sSup R ≤ d.logSlope s m := by
      refine csSup_le hRne ?_
      rintro _ ⟨t, ⟨ht, hmt⟩, rfl⟩
      exact hbound s hs hsm t ht hmt
    have hms : 0 < m - s := sub_pos.mpr hsm
    have hslope : d.logSlope s m * (m - s) = Real.log (d.ρ m) - Real.log (d.ρ s) := by
      unfold logSlope
      field_simp
    have : sSup R * (m - s) ≤ Real.log (d.ρ m) - Real.log (d.ρ s) := by
      rw [← hslope]
      exact mul_le_mul_of_nonneg_right hk hms.le
    nlinarith
  · rw [hsm]
    simp
  · -- right of `m`: the slope over `[m, s]` is in `R`
    have hk : d.logSlope m s ≤ sSup R := le_csSup hRbdd ⟨s, ⟨hs, hsm⟩, rfl⟩
    have hsm0 : 0 < s - m := sub_pos.mpr hsm
    have hslope : d.logSlope m s * (s - m) = Real.log (d.ρ s) - Real.log (d.ρ m) := by
      unfold logSlope
      field_simp
    have : Real.log (d.ρ s) - Real.log (d.ρ m) ≤ sSup R * (s - m) := by
      rw [← hslope]
      exact mul_le_mul_of_nonneg_right hk hsm0.le
    linarith

end Chord

end LineDensity

end FunctionalInequalities.KLS

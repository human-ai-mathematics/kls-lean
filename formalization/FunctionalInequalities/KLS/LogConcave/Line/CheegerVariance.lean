module

public import FunctionalInequalities.KLS.LogConcave.Line.Buser

/-!
# The Cheeger constant of a log-concave law on the line

Bobkov, *Isoperimetric and analytic inequalities for log-concave probability measures* (1999),
Proposition 4.1: for a log-concave law `μ` on `ℝ` with density `f` and median `m`,
`Is(μ) = 2 f(m)` and `1 / (3 Var μ) ≤ Is(μ)² ≤ 2 / Var μ`. Here `Is(μ)` is the Minkowski Cheeger
infimum `Isoperimetry.minkowskiConstant μ` (outer Minkowski content over intermediate mass).

This file proves the identity `Is(μ) = 2 f(m)` and the lower bound in the form
`Is(μ)⁻² ≤ 3 Var μ`, which is exact in `[0, ∞]`; the `LogConcave` version states it for every
log-concave law on the line, Dirac laws included. The lower bound composes `Is(μ) ≥ 2 f(m)`
with `Var μ ≥ 1 / (12 f(m)²)`; the identity adds the half-line test set `(-∞, m]`, whose outer
Minkowski content is the derivative `f(m)` of the distribution function.
The upper bound `Is(μ)² ≤ 2 / Var μ` and equality cases are outside this module's proved
statements.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FunctionalInequalities.Probability.Line (cdf)
open scoped ENNReal

namespace FunctionalInequalities.KLS.LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ)

/-- The open `r`-thickening of a closed half-line `(-∞, a]` is `(-∞, a + r)`. -/
theorem thickening_Iic {r : ℝ} (hr : 0 < r) (a : ℝ) :
    Metric.thickening r (Iic a) = Iio (a + r) := by
  ext x
  rw [Metric.mem_thickening_iff]
  simp only [mem_Iic, mem_Iio, Real.dist_eq]
  constructor
  · rintro ⟨z, hz, hdist⟩
    rcases abs_lt.mp hdist with ⟨_, hupper⟩
    linarith
  · intro hx
    by_cases hxa : x ≤ a
    · refine ⟨x, hxa, ?_⟩
      simpa using hr
    · have hax : a < x := lt_of_not_ge hxa
      refine ⟨a, le_rfl, ?_⟩
      rw [abs_of_pos (sub_pos.mpr hax)]
      linarith

include d

/-- Open half-lines carry the distribution function: `μ (-∞, a) = F a`. -/
theorem measure_Iio_eq_ofReal_cdf (a : ℝ) :
    (μ : Measure ℝ) (Iio a) = ENNReal.ofReal (cdf μ a) := by
  have hset : Iic a = Iio a ∪ ({a} : Set ℝ) := by
    ext x
    simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with hxa | hxa
      · exact Or.inl hxa
      · exact Or.inr hxa
    · intro hx
      rcases hx with hxa | hxa
      · exact le_of_lt hxa
      · exact le_of_eq hxa
  have hdis : Disjoint (Iio a) ({a} : Set ℝ) := by
    exact Set.disjoint_singleton_right.mpr (lt_irrefl a)
  have hunion :
      (μ : Measure ℝ) (Iic a) =
        (μ : Measure ℝ) (Iio a) + (μ : Measure ℝ) ({a} : Set ℝ) := by
    rw [hset]
    exact measure_union hdis (measurableSet_singleton a)
  calc
    (μ : Measure ℝ) (Iio a) =
        (μ : Measure ℝ) (Iio a) + 0 := by simp
    _ = (μ : Measure ℝ) (Iio a) + (μ : Measure ℝ) ({a} : Set ℝ) := by
      rw [d.measure_singleton a]
    _ = (μ : Measure ℝ) (Iic a) := hunion.symm
    _ = ENNReal.ofReal (cdf μ a) := by
      exact measure_Iic_eq_ofReal_cdf μ a

/-- For `r > 0` the Minkowski difference quotient of `(-∞, a]` is the difference quotient of the
distribution function. -/
theorem thickening_Iic_quotient_eq {r : ℝ} (hr : 0 < r) (a : ℝ) :
    ((μ : Measure ℝ) (Metric.thickening r (Iic a)) - (μ : Measure ℝ) (Iic a)) /
        ENNReal.ofReal r =
      ENNReal.ofReal ((cdf μ (a + r) - cdf μ a) / r) := by
  rw [thickening_Iic hr a, measure_Iio_eq_ofReal_cdf d,
    measure_Iic_eq_ofReal_cdf μ a,
    ← ENNReal.ofReal_sub _ (Probability.Line.cdf_nonneg μ a),
    ← ENNReal.ofReal_div_of_pos hr]

/-- The outer Minkowski content of `(-∞, a]` at a point of the interior of the support is at most
the density there. -/
theorem minkowskiContent_Iic_le {a : ℝ} (ha : a ∈ interior (μ : Measure ℝ).support) :
    Isoperimetry.minkowskiContent (μ : Measure ℝ) (Iic a) ≤ ENNReal.ofReal (d.ρ a) := by
  have hreal :
      Tendsto
        (fun r : ℝ => (cdf μ (a + r) - cdf μ a) / r)
        (𝓝[>] (0 : ℝ)) (𝓝 (d.ρ a)) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (d.hasDerivAt_cdf ha).tendsto_slope_zero_right

  have hen :
      Tendsto
        (fun r : ℝ => ENNReal.ofReal ((cdf μ (a + r) - cdf μ a) / r))
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (d.ρ a))) :=
    ENNReal.tendsto_ofReal hreal

  have heq :
      (fun r : ℝ =>
          ((μ : Measure ℝ) (Metric.thickening r (Iic a)) -
            (μ : Measure ℝ) (Iic a)) / ENNReal.ofReal r) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun r : ℝ =>
          ENNReal.ofReal ((cdf μ (a + r) - cdf μ a) / r)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact thickening_Iic_quotient_eq d hr a

  have hquot :
      Tendsto
        (fun r : ℝ =>
          ((μ : Measure ℝ) (Metric.thickening r (Iic a)) -
            (μ : Measure ℝ) (Iic a)) / ENNReal.ofReal r)
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (d.ρ a))) :=
    hen.congr' heq.symm

  unfold Isoperimetry.minkowskiContent
  exact hquot.liminf_eq.le

/-- The half-line at a median gives `Is(μ) ≤ 2 f(m)`. -/
theorem minkowskiConstant_le_two_mul {m : ℝ} (hm : cdf μ m = 1 / 2) :
    Isoperimetry.minkowskiConstant μ ≤ ENNReal.ofReal (2 * d.ρ m) := by
  have hm_int :
      m ∈ interior (μ : Measure ℝ).support :=
    median_mem d.logConcave d.interior_support_nonempty hm

  have hmass :
      (μ : Measure ℝ) (Iic m) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [measure_Iic_eq_ofReal_cdf μ m, hm]

  have hpos : 0 < (μ : Measure ℝ) (Iic m) := by
    rw [hmass]
    norm_num

  have hlt : (μ : Measure ℝ) (Iic m) < 1 := by
    rw [hmass]
    norm_num

  have hhalf :
      (1 : ENNReal) - ENNReal.ofReal (1 / 2 : ℝ) =
        ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [← ENNReal.ofReal_one]
    rw [← ENNReal.ofReal_sub (1 : ℝ) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num

  have hden :
      min ((μ : Measure ℝ) (Iic m))
          (1 - (μ : Measure ℝ) (Iic m)) =
        ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [hmass, hhalf]
    exact min_self _

  have hle :
      Isoperimetry.minkowskiConstant μ ≤
        Isoperimetry.minkowskiContent (μ : Measure ℝ) (Iic m) /
          min ((μ : Measure ℝ) (Iic m))
            (1 - (μ : Measure ℝ) (Iic m)) := by
    unfold Isoperimetry.minkowskiConstant
    refine iInf_le_of_le (Iic m) ?_
    refine iInf_le_of_le measurableSet_Iic ?_
    refine iInf_le_of_le hpos ?_
    exact iInf_le_of_le hlt le_rfl

  calc
    Isoperimetry.minkowskiConstant μ ≤
        Isoperimetry.minkowskiContent (μ : Measure ℝ) (Iic m) /
          min ((μ : Measure ℝ) (Iic m))
            (1 - (μ : Measure ℝ) (Iic m)) := hle
    _ ≤ ENNReal.ofReal (d.ρ m) / ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [hden]
      gcongr
      exact d.minkowskiContent_Iic_le hm_int
    _ = ENNReal.ofReal (d.ρ m / (1 / 2 : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ = ENNReal.ofReal (2 * d.ρ m) := by
      congr 1
      ring

/-- Bobkov (1999), Proposition 4.1, first identity: `Is(μ) = 2 f(m)` at a median `m`. -/
theorem minkowskiConstant_eq_two_mul {m : ℝ} (hm : cdf μ m = 1 / 2) :
    Isoperimetry.minkowskiConstant μ = ENNReal.ofReal (2 * d.ρ m) := by
  apply le_antisymm
  · exact minkowskiConstant_le_two_mul d hm
  · exact d.two_mul_le_minkowskiConstant
      d.logConcave d.interior_support_nonempty hm

include d

/-- Bobkov (1999), Proposition 4.1, lower bound `1 / (3 Var μ) ≤ Is(μ)²`, in the form
`Is(μ)⁻² ≤ 3 Var μ`, for a law with a density. -/
theorem inv_minkowskiConstant_sq_le_three_mul_evariance :
    (Isoperimetry.minkowskiConstant μ)⁻¹ ^ 2 ≤ 3 * evariance id (μ : Measure ℝ) := by
  obtain ⟨m, hm⟩ := d.exists_median
  have hμ := d.logConcave
  have hi := d.interior_support_nonempty
  have hmΩ : m ∈ interior (μ : Measure ℝ).support :=
    median_mem hμ hi hm
  have hc : 0 < d.ρ m :=
    d.pos hmΩ
  obtain ⟨k, hk⟩ := d.exists_supergradient hμ hmΩ
  have hvar :
      1 / (12 * d.ρ m ^ 2) ≤ variance id (μ : Measure ℝ) :=
    d.one_div_le_variance hμ hi hm hk
  have hreal :
      1 / (4 * d.ρ m ^ 2) ≤
        3 * variance id (μ : Measure ℝ) := by
    have hscale :
        (1 : ℝ) / (4 * d.ρ m ^ 2) =
          3 * (1 / (12 * d.ρ m ^ 2)) := by
      ring
    rw [hscale]
    exact mul_le_mul_of_nonneg_left hvar (by norm_num)
  have hvarE :
      ENNReal.ofReal (variance id (μ : Measure ℝ)) =
        evariance id (μ : Measure ℝ) :=
    ProbabilityTheory.ofReal_variance hμ.memLp_id_two
  have hQ :
      ENNReal.ofReal (2 * d.ρ m) ≤
        Isoperimetry.minkowskiConstant μ :=
    d.two_mul_le_minkowskiConstant hμ hi hm
  have hinv :
      (Isoperimetry.minkowskiConstant μ)⁻¹ ≤
        (ENNReal.ofReal (2 * d.ρ m))⁻¹ :=
    ENNReal.inv_le_inv.mpr hQ
  have hinvsq :
      (Isoperimetry.minkowskiConstant μ)⁻¹ ^ 2 ≤
        (ENNReal.ofReal (2 * d.ρ m))⁻¹ ^ 2 := by
    gcongr
  calc
    (Isoperimetry.minkowskiConstant μ)⁻¹ ^ 2 ≤
        (ENNReal.ofReal (2 * d.ρ m))⁻¹ ^ 2 := hinvsq
    _ = (ENNReal.ofReal ((2 * d.ρ m)⁻¹)) ^ 2 := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * d.ρ m)]
    _ = ENNReal.ofReal ((2 * d.ρ m)⁻¹ ^ 2) := by
      rw [ENNReal.ofReal_pow (by positivity)]
    _ = ENNReal.ofReal ((1 : ℝ) / (4 * d.ρ m ^ 2)) := by
      congr 1
      field_simp [ne_of_gt hc]
      norm_num
    _ ≤ ENNReal.ofReal (3 * variance id (μ : Measure ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 3 * evariance id (μ : Measure ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.ofReal_ofNat, hvarE]

end FunctionalInequalities.KLS.LineDensity

namespace FunctionalInequalities.KLS.LogConcave

variable {ν : ProbabilityMeasure ℝ}

/-- Bobkov (1999), Proposition 4.1, lower bound: every log-concave law on the line satisfies
`Is(ν)⁻² ≤ 3 Var ν`, i.e. `1 / (3 Var ν) ≤ Is(ν)²`; for a Dirac law both sides of the original
form are infinite and the left side here is `0`. -/
theorem inv_minkowskiConstant_sq_le_three_mul_evariance (hν : LogConcave ν) :
    (Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2 ≤ 3 * evariance id (ν : Measure ℝ) := by
  rcases eq_empty_or_nonempty (interior (ν : Measure ℝ).support) with hempty | hi
  · rw [hν.minkowskiConstant_eq_top_of_interior_empty hempty]
    simp
  obtain ⟨d⟩ := hν.exists_lineDensity hi
  exact d.inv_minkowskiConstant_sq_le_three_mul_evariance

end FunctionalInequalities.KLS.LogConcave

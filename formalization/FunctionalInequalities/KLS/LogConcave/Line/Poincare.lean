module

public import FunctionalInequalities.KLS.LogConcave.Line.Hardy
public import FunctionalInequalities.KLS.LogConcave.Line.Variance
public import FunctionalInequalities.KLS.LogConcave.Poincare
public import FunctionalInequalities.KLS.LogConcave.Isotropic

/-!
# The one-dimensional log-concave Poincaré bound `C_P^lit(ν) ≤ 12 Var_ν`

Source: Blueprint `thm:one-dimensional-logconcave-poincare` (Bobkov 1999, Corollary 4.3 and
equation (1.3)). Read `LogConcave.smoothTest_holds_twelve_variance`,
`LogConcave.localSlope_constant_le_twelve_variance` and
`LogConcave.localSlope_constant_le_twelve_evariance`; `logConcave_dirac` supplies the zero-variance
example.

For a log-concave probability law `ν` on the real line the literature Poincaré constant
`Poincare.LocalSlope.Intrinsic.constant ν` is at most `12 · Var_ν(id)`. When the affine support is
a point the direction space is zero-dimensional and the constant is `0`. Otherwise the support has
nonempty interior, a Borell density `ρ` exists, and with a median `m` and `c = ρ m > 0` the Hardy
module gives the smooth-test inequality with constant `(1 / c)²` while the variance module gives
`1 / (12 c²) ≤ Var_ν`; the smooth-test and literature optima agree for log-concave laws.

The proof route differs from Bobkov's Cheeger-constant argument: it uses an integration-by-parts
Hardy inequality with the hazard-rate median bounds and the supporting-line variance estimate. The
displayed numerical value `12` is exactly the Blueprint normalization; no smaller constant is
claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open FunctionalInequalities.Probability.Line (cdf)

namespace FunctionalInequalities.KLS

section Dirac

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Dirac laws are compact-set log-concave. -/
theorem logConcave_dirac (a : E) : LogConcave (Probability.ofMeasure (Measure.dirac a)) := by
  intro K₀ K₁ hK₀ hK₁ t ht0 ht1
  change (Measure.dirac a) K₀ ^ t * (Measure.dirac a) K₁ ^ (1 - t) ≤ (Measure.dirac a) _
  by_cases h0 : a ∈ K₀
  · by_cases h1 : a ∈ K₁
    · have hmem : a ∈ {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y} :=
        ⟨a, h0, a, h1, by rw [← add_smul, add_sub_cancel, one_smul]⟩
      rw [Measure.dirac_apply_of_mem h0, Measure.dirac_apply_of_mem h1, ENNReal.one_rpow,
        ENNReal.one_rpow, one_mul, Measure.dirac_apply_of_mem hmem]
    · rw [Measure.dirac_apply' _ hK₁.isClosed.measurableSet, Set.indicator_of_notMem h1,
        ENNReal.zero_rpow_of_pos (by linarith), mul_zero]
      exact zero_le
  · rw [Measure.dirac_apply' _ hK₀.isClosed.measurableSet, Set.indicator_of_notMem h0,
      ENNReal.zero_rpow_of_pos ht0, zero_mul]
    exact zero_le

end Dirac

namespace LogConcave

variable {ν : ProbabilityMeasure ℝ}

/-- Smooth-test Poincaré inequality with constant `12 · Var` for a log-concave law on the line
whose support has nonempty interior. -/
theorem smoothTest_holds_twelve_variance (hν : LogConcave ν)
    (hi : (interior (ν : Measure ℝ).support).Nonempty) :
    Poincare.SmoothTest.Holds (ν : Measure ℝ) (12 * variance id (ν : Measure ℝ)) := by
  obtain ⟨d⟩ := hν.exists_lineDensity hi
  obtain ⟨m, hm⟩ := d.exists_median
  have hmΩ := LineDensity.median_mem hν hi hm
  obtain ⟨k, hk⟩ := d.exists_supergradient hν hmΩ
  have hc : 0 < d.ρ m := d.pos hmΩ
  have hvar := d.one_div_le_variance hν hi hm hk
  refine (d.smoothTest_holds hν hi hm).mono ?_
  calc (1 / d.ρ m) ^ 2 = 12 * (1 / (12 * d.ρ m ^ 2)) := by
        field_simp
    _ ≤ 12 * variance id (ν : Measure ℝ) := by gcongr

/-- A log-concave law on the line either has zero-dimensional affine support or a support with
nonempty interior. -/
theorem direction_eq_bot_or_interior_support_nonempty (hν : LogConcave ν) :
    (Probability.affineSupport ν).direction = ⊥ ∨ (interior (ν : Measure ℝ).support).Nonempty := by
  rcases Ideal.eq_bot_or_top ((Probability.affineSupport ν).direction : Ideal ℝ) with hbot | htop
  · exact Or.inl hbot
  · right
    have hne : ((Probability.affineSupport ν : AffineSubspace ℝ ℝ) : Set ℝ).Nonempty :=
      ⟨_, Probability.support_subset_affineSupport ν (Probability.supportPoint_mem_support ν)⟩
    exact hν.interior_support_nonempty_of_affineSupport_eq_top
      ((AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp htop)

/-- Blueprint `thm:one-dimensional-logconcave-poincare`: every log-concave law on the line has
literature Poincaré constant at most `12 · Var_ν(id)`, the zero-variance (Dirac) case included. -/
theorem localSlope_constant_le_twelve_variance (hν : LogConcave ν) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤
      ENNReal.ofReal (12 * variance id (ν : Measure ℝ)) := by
  rcases hν.direction_eq_bot_or_interior_support_nonempty with hbot | hi
  · rw [Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_direction_eq_bot ν hbot]
    exact bot_le
  · have h12 : 0 ≤ 12 * variance id (ν : Measure ℝ) :=
      mul_nonneg (by norm_num) (variance_nonneg _ _)
    rw [← hν.smoothTest_constant_eq_localSlope, ENNReal.ofReal_eq_coe_nnreal h12]
    exact Poincare.SmoothTest.constant_le (hν.smoothTest_holds_twelve_variance hi)

/-- The same bound in extended form, through the extended variance. -/
theorem localSlope_constant_le_twelve_evariance (hν : LogConcave ν) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ 12 * evariance id (ν : Measure ℝ) := by
  refine hν.localSlope_constant_le_twelve_variance.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by norm_num), ofReal_variance hν.memLp_id_two]
  norm_num

end LogConcave

end FunctionalInequalities.KLS

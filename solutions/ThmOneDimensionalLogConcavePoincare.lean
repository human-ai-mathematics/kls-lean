module

public import FunctionalInequalities.KLS.LogConcave.Line.SharpPoincare

/-!
# Lean certificate: `thm:one-dimensional-logconcave-poincare`

Every log-concave probability law `ν` on the real line satisfies
`C_P^lit(ν) ≤ 4 · Var_ν(id)`, where `C_P^lit` is the literature Poincaré constant
`Poincare.LocalSlope.Intrinsic.constant` of the Blueprint and the right-hand side is read in
`ENNReal` through `ENNReal.ofReal`; the extended-variance form `≤ 4 · eVar_ν(id)` is packaged as
well. Zero variance (a Dirac law, whose affine support is a point) is included: the constant is
`0`. The historical constant `12` (Bobkov) is a corollary and also carries its own independent
proof in `KLS/LogConcave/Line/Poincare.lean`. Nothing here asserts a smaller universal constant, a
bound in higher dimension, a Cheeger inequality, or any statement about the raw energy on tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory FunctionalInequalities

namespace Solutions.ThmOneDimensionalLogConcavePoincare

/-- The complete one-dimensional bound of the Blueprint, in real and extended-variance form. -/
theorem certificate (ν : ProbabilityMeasure ℝ) (hν : KLS.LogConcave ν) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (4 * variance id (ν : Measure ℝ)) ∧
    Poincare.LocalSlope.Intrinsic.constant ν ≤ 4 * evariance id (ν : Measure ℝ) :=
  ⟨hν.localSlope_constant_le_four_variance, hν.localSlope_constant_le_four_evariance⟩

/-- Typed application: a finite literature Poincaré constant for every log-concave law on the
line, with the explicit numerical normalization `4`. -/
example (ν : ProbabilityMeasure ℝ) (hν : KLS.LogConcave ν) :
    Poincare.LocalSlope.Intrinsic.constant ν ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (certificate ν hν).1

/-- The historical constant `12` of Bobkov is a corollary of the certificate. -/
example (ν : ProbabilityMeasure ℝ) (hν : KLS.LogConcave ν) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (12 * variance id (ν : Measure ℝ)) :=
  (certificate ν hν).1.trans
    (ENNReal.ofReal_le_ofReal (by nlinarith [variance_nonneg id (ν : Measure ℝ)]))

/-- The zero-variance case: the Dirac law at the origin is log-concave, has variance zero, and its
literature constant is zero. -/
example :
    Poincare.LocalSlope.Intrinsic.constant (Probability.ofMeasure (Measure.dirac (0 : ℝ))) ≤ 0 := by
  have h := (certificate _ (KLS.logConcave_dirac (0 : ℝ))).1
  simpa [variance_dirac] using h

/-- A law with nonempty interior support satisfies the smooth-test inequality with the same
constant `4 · Var`. -/
example (ν : ProbabilityMeasure ℝ) (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure ℝ).support).Nonempty) :
    Poincare.SmoothTest.Holds (ν : Measure ℝ) (4 * variance id (ν : Measure ℝ)) :=
  hν.smoothTest_holds_four_variance hi

end Solutions.ThmOneDimensionalLogConcavePoincare

/--
info: 'Solutions.ThmOneDimensionalLogConcavePoincare.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmOneDimensionalLogConcavePoincare.certificate

/--
info: 'FunctionalInequalities.Probability.Line.map_cdf_eq_uniform'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.Line.map_cdf_eq_uniform

/--
info: 'FunctionalInequalities.KLS.LogConcave.exists_lineDensity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.exists_lineDensity

/--
info: 'FunctionalInequalities.KLS.LineDensity.exists_supergradient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.exists_supergradient

/--
info: 'FunctionalInequalities.KLS.LineDensity.mul_le_mul_of_add_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.mul_le_mul_of_add_eq

/--
info: 'FunctionalInequalities.KLS.LineDensity.two_mul_measureReal_Ioi_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.two_mul_measureReal_Ioi_le

/--
info: 'FunctionalInequalities.KLS.LineDensity.two_mul_cdf_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.two_mul_cdf_le

/--
info: 'FunctionalInequalities.KLS.LineDensity.le_add_mul_cdf_sub'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.le_add_mul_cdf_sub

/--
info: 'FunctionalInequalities.KLS.LineDensity.smoothTest_holds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.smoothTest_holds

/--
info: 'FunctionalInequalities.KLS.LineDensity.one_div_le_variance'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.one_div_le_variance

/--
info: 'FunctionalInequalities.KLS.LogConcave.smoothTest_holds_twelve_variance'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.smoothTest_holds_twelve_variance

/--
info: 'FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_twelve_variance'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_twelve_variance

/--
info: 'FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_twelve_evariance'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_twelve_evariance

/--
info: 'FunctionalInequalities.KLS.logConcave_dirac'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.logConcave_dirac

/--
info: 'FunctionalInequalities.KLS.LineDensity.setIntegral_Iic_sq_sub_le_of_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.setIntegral_Iic_sq_sub_le_of_le

/--
info: 'FunctionalInequalities.Probability.Line.one_div_le_variance_affineQuantile'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.Line.one_div_le_variance_affineQuantile

/--
info: 'FunctionalInequalities.KLS.LineDensity.variance_ge_of_affine_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.variance_ge_of_affine_bound

/--
info: 'FunctionalInequalities.KLS.LineDensity.cdf_mul_one_sub_cdf_le_sd_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.cdf_mul_one_sub_cdf_le_sd_mul

/--
info: 'FunctionalInequalities.KLS.LineDensity.integral_sq_div_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.integral_sq_div_le

/--
info: 'FunctionalInequalities.KLS.LineDensity.variance_clip_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.variance_clip_le

/--
info: 'FunctionalInequalities.KLS.LineDensity.variance_le_four_variance_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LineDensity.variance_le_four_variance_mul

/--
info: 'FunctionalInequalities.KLS.LogConcave.smoothTest_holds_four_variance'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.smoothTest_holds_four_variance

/--
info: 'FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_four_variance'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_four_variance

/--
info: 'FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_four_evariance'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_four_evariance

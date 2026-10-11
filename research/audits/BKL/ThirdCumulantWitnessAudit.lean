import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Audit: a law satisfying every premise of the conditional BKL Lemma 4.2

The uniform law on `[-√3, √3]` is a centered isotropic probability law on `ℝ` with all exponential
moments, and it satisfies `LetwinQuadraticBound` (for `M = m`, `Var(m X²) = 4 m² / 5 ≤ 8 m²`), so the
conditional BKL Lemma 4.2 (`sum_sq_cumulant_three_le_of_letwin` in
`Analysis/BakryEmery/Cumulant/Basic.lean`) applies to it with every premise discharged. The client also
connects the cumulant and Taylor formulations (`taylorTensor_two_inner_eq_of_centered`,
`cumulant_three_eq_integral`). Since the uniform law is symmetric (`κ₃ = 0`), a second, skewed witness
is included: the two-point law `(1/5) δ₂ + (4/5) δ_{-1/2}` is centered and isotropic with
`Var(m X²) = 9 m² / 4 ≤ 8 m²` and `κ₃(1, 1, 1) = 3/2 ≠ 0`. The uniform law is log-concave, the
two-point law is not; the conditional statement does not assume log-concavity. The client does not
prove the Letwin theorem,
which remains an explicit premise of the library statement.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace BKLThirdCumulantWitness

open FunctionalInequalities.Analysis.BakryEmery

/-- The uniform law on `[-√3, √3]`. -/
def unifSym : Measure ℝ := (volume : Measure ℝ)[|Set.Icc (-Real.sqrt 3) (Real.sqrt 3)]

theorem isProbabilityMeasure_unifSym : IsProbabilityMeasure unifSym := by
    have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hdiff : 0 < Real.sqrt (3 : ℝ) - -Real.sqrt 3 := by
      linarith
    refine ⟨?_⟩
    simp only [unifSym, ProbabilityTheory.cond, Real.volume_Icc]
    simp
    exact ENNReal.inv_mul_cancel (by positivity) (by simp)

theorem integral_unifSym (f : ℝ → ℝ) :
    ∫ x, f x ∂unifSym = (2 * Real.sqrt 3)⁻¹ * ∫ x in (-Real.sqrt 3)..(Real.sqrt 3), f x := by
    have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hle : -Real.sqrt 3 ≤ Real.sqrt 3 := by
      linarith
    have hpos : 0 < 2 * Real.sqrt 3 := by
      positivity
    have hvol :
        volume (Set.Icc (-Real.sqrt 3) (Real.sqrt 3)) =
          ENNReal.ofReal (2 * Real.sqrt 3) := by
      rw [Real.volume_Icc]
      congr 1
      ring
    have hcoeff :
        ENNReal.toReal
            ((volume (Set.Icc (-Real.sqrt 3) (Real.sqrt 3)))⁻¹) =
          (2 * Real.sqrt 3)⁻¹ := by
      rw [hvol, ENNReal.toReal_inv, ENNReal.toReal_ofReal hpos.le]
    rw [unifSym, ProbabilityTheory.cond, integral_smul_measure, hcoeff]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hle]
    simp [smul_eq_mul]

theorem integrable_exp_mul_norm_unifSym (r : ℝ) :
    Integrable (fun x : ℝ => Real.exp (r * ‖x‖)) unifSym := by
    have hcont : Continuous (fun x : ℝ => Real.exp (r * ‖x‖)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_norm)
    have hI :
        IntegrableOn (fun x : ℝ => Real.exp (r * ‖x‖))
          (Set.Icc (-Real.sqrt 3) (Real.sqrt 3)) := by
      exact hcont.integrableOn_Icc
    have hs0 :
        (volume : Measure ℝ) (Set.Icc (-Real.sqrt 3) (Real.sqrt 3)) ≠ 0 := by
      rw [Real.volume_Icc]
      have hsqrt : 0 < Real.sqrt (3 : ℝ) :=
        Real.sqrt_pos.2 (by norm_num)
      have hlen : 0 < Real.sqrt (3 : ℝ) - -Real.sqrt (3 : ℝ) := by
        linarith
      exact (ENNReal.ofReal_pos.mpr hlen).ne'
    have hscale :
        ((volume : Measure ℝ) (Set.Icc (-Real.sqrt 3) (Real.sqrt 3)))⁻¹
          ≠ (⊤ : ENNReal) :=
      ENNReal.inv_ne_top.mpr hs0
    rw [unifSym]
    change Integrable (fun x : ℝ => Real.exp (r * ‖x‖))
      (((volume : Measure ℝ) (Set.Icc (-Real.sqrt 3) (Real.sqrt 3)))⁻¹ •
        (volume : Measure ℝ).restrict (Set.Icc (-Real.sqrt 3) (Real.sqrt 3)))
    exact hI.smul_measure hscale

theorem centered_unifSym (v : ℝ) : ∫ x, ⟪v, x⟫ ∂unifSym = 0 := by
  rw [integral_unifSym]
  have h : (fun x : ℝ => ⟪v, x⟫) = fun x => v * x := by
    funext x
    simp [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [h, intervalIntegral.integral_const_mul, integral_id]
  ring

theorem isotropic_unifSym (v w : ℝ) : ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂unifSym = ⟪v, w⟫ := by
  rw [integral_unifSym]
  have h : (fun x : ℝ => ⟪v, x⟫ * ⟪w, x⟫) = fun x => (v * w) * x ^ 2 := by
    funext x
    simp [RCLike.inner_apply, conj_trivial]
    ring
  rw [h, intervalIntegral.integral_const_mul, integral_pow]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hvw : ⟪v, w⟫ = v * w := by simp [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [hvw]
  field_simp
  have h33 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, h3]
  linear_combination 2 * (v * w) * h33

private lemma unifSym_quadratic_bound (c : ℝ) :
    ∫ x : ℝ, (c * (x ^ 2 - 1)) ^ 2 ∂unifSym ≤ 4 * c ^ 2 := by
  let : IsProbabilityMeasure unifSym := isProbabilityMeasure_unifSym
  have hmem :
      ∀ᵐ x ∂unifSym, x ∈ Set.Icc (-Real.sqrt 3) (Real.sqrt 3) := by
    simpa [unifSym, ProbabilityTheory.cond] using
      (ae_restrict_mem (μ := (volume : Measure ℝ))
        (s := Set.Icc (-Real.sqrt 3) (Real.sqrt 3)) measurableSet_Icc)
  have hbound :
      ∀ᵐ x ∂unifSym, (c * (x ^ 2 - 1)) ^ 2 ≤ 4 * c ^ 2 := by
    filter_upwards [hmem] with x hx
    have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have hxupper : x ^ 2 ≤ 3 := by
      nlinarith [Real.sqrt_nonneg 3, hx.1, hx.2, sq_nonneg x]
    have hpoly : (x ^ 2 - 1) ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg (x ^ 2 - 1)]
    rw [show (c * (x ^ 2 - 1)) ^ 2 =
        c ^ 2 * (x ^ 2 - 1) ^ 2 by ring]
    calc
      c ^ 2 * (x ^ 2 - 1) ^ 2 ≤ c ^ 2 * 4 :=
        mul_le_mul_of_nonneg_left hpoly (sq_nonneg c)
      _ = 4 * c ^ 2 := by ring
  have hnorm :
      ∀ᵐ x ∂unifSym,
        ‖(c * (x ^ 2 - 1)) ^ 2‖ ≤ 4 * c ^ 2 := by
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (c * (x ^ 2 - 1)))]
    exact hx
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => (c * (x ^ 2 - 1)) ^ 2) unifSym := by
    fun_prop
  have hi :
      Integrable (fun x : ℝ => (c * (x ^ 2 - 1)) ^ 2) unifSym :=
    (integrable_const (μ := unifSym) (4 * c ^ 2)).mono' hmeas hnorm
  have hmono :
      ∫ x : ℝ, (c * (x ^ 2 - 1)) ^ 2 ∂unifSym ≤
        ∫ _ : ℝ, (4 * c ^ 2) ∂unifSym :=
    integral_mono_ae hi (integrable_const (μ := unifSym) (4 * c ^ 2)) hbound
  simpa using hmono

theorem letwinQuadraticBound_unifSym : LetwinQuadraticBound unifSym := by
    classical
    rw [LetwinQuadraticBound]
    intro M hMself
    let c : ℝ := M 1
    have hM (x : ℝ) : M x = c * x := by
      change M x = (M 1) * x
      rw [show x = x • (1 : ℝ) by simp, M.map_smul]
      simp [mul_comm]
    have hquad (x : ℝ) : ⟪M x, x⟫ = c * x ^ 2 := by
      rw [hM]
      change ⟪c • x, x⟫ = c * x ^ 2
      simp [pow_two, smul_eq_mul]
      ring
    have hmean : ∫ y : ℝ, ⟪M y, y⟫ ∂unifSym = c := by
      simp_rw [hquad]
      rw [integral_const_mul]
      have h := isotropic_unifSym 1 1
      have h' : ∫ y : ℝ, y ^ 2 ∂unifSym = 1 := by
        simpa [pow_two] using h
      rw [h']
      ring
    have hvar :
        ∫ x : ℝ, (⟪M x, x⟫ -
            ∫ y : ℝ, ⟪M y, y⟫ ∂unifSym) ^ 2 ∂unifSym ≤
          4 * c ^ 2 := by
      have hpoint (x : ℝ) :
          (⟪M x, x⟫ -
              ∫ y : ℝ, ⟪M y, y⟫ ∂unifSym) ^ 2 =
            (c * (x ^ 2 - 1)) ^ 2 := by
        rw [hquad, hmean]
        ring
      simp_rw [hpoint]
      exact unifSym_quadratic_bound c
    have hdim : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
    let : Unique (Fin (Module.finrank ℝ ℝ)) :=
      { default := ⟨0, by omega⟩
        uniq := by
          intro i
          apply Fin.ext
          omega }
    have hsum :
        ∑ i, ∑ j, ⟪M (stdOrthonormalBasis ℝ ℝ i),
            (stdOrthonormalBasis ℝ ℝ j)⟫ ^ 2 = c ^ 2 := by
      simp only [Fintype.sum_unique]
      let b : ℝ := stdOrthonormalBasis ℝ ℝ default
      have hb : b ^ 2 = 1 := by
        have hn : ‖b‖ = 1 := by
          dsimp [b]
          exact (stdOrthonormalBasis ℝ ℝ).norm_eq_one default
        rw [Real.norm_eq_abs] at hn
        nlinarith [sq_abs b]
      rw [show ⟪M b, b⟫ = c * b ^ 2 by
        dsimp [b]
        exact hquad _]
      rw [hb]
      ring
    rw [hsum]
    nlinarith [sq_nonneg c]

/-- The conditional BKL Lemma 4.2 with every premise discharged. -/
theorem sum_sq_cumulant_three_le_unifSym (u : ℝ) :
    ∑ j, ∑ k, cumulant unifSym 3 ![u, stdOrthonormalBasis ℝ ℝ j, stdOrthonormalBasis ℝ ℝ k] ^ 2 ≤
      8 * ‖u‖ ^ 2 := by
    have := isProbabilityMeasure_unifSym
    exact
      sum_sq_cumulant_three_le_of_letwin unifSym
        integrable_exp_mul_norm_unifSym centered_unifSym isotropic_unifSym
        letwinQuadraticBound_unifSym u

/-- The cumulant and Taylor formulations agree for the witness: `T_2⟪u, ·⟫(v, w) = ½ κ_3(u, v, w)`. -/
theorem taylorTensor_two_eq_half_cumulant_unifSym (u v w : ℝ) :
    taylorTensor unifSym (fun x => ⟪u, x⟫) 2 ![v, w] = (1 / 2 : ℝ) * cumulant unifSym 3 ![u, v, w] := by
  have := isProbabilityMeasure_unifSym
  rw [taylorTensor_two_inner_eq_of_centered unifSym integrable_exp_mul_norm_unifSym centered_unifSym,
    cumulant_three_eq_integral unifSym integrable_exp_mul_norm_unifSym centered_unifSym]

end BKLThirdCumulantWitness

open scoped ENNReal

namespace BKLSkewWitness
open FunctionalInequalities.Analysis.BakryEmery

/-- The two-point law `(1/5) δ₂ + (4/5) δ_{-1/2}`: centered, isotropic and skewed. -/
def twoPt : Measure ℝ := (1 / 5 : ℝ≥0∞) • Measure.dirac 2 + (4 / 5 : ℝ≥0∞) • Measure.dirac (-1 / 2)

theorem integrable_twoPt (f : ℝ → ℝ) : Integrable f twoPt := by
  refine Integrable.add_measure ?_ ?_
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))

theorem integral_twoPt (f : ℝ → ℝ) : ∫ x, f x ∂twoPt = (1 / 5) * f 2 + (4 / 5) * f (-1 / 2) := by
  rw [twoPt, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · simp [smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))

theorem isProbabilityMeasure_twoPt : IsProbabilityMeasure twoPt := by
  constructor
  rw [twoPt]
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

theorem centered_twoPt (v : ℝ) : ∫ x, ⟪v, x⟫ ∂twoPt = 0 := by
  rw [integral_twoPt]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem isotropic_twoPt (v w : ℝ) : ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂twoPt = ⟪v, w⟫ := by
  rw [integral_twoPt]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem integrable_exp_mul_norm_twoPt (r : ℝ) :
    Integrable (fun x => Real.exp (r * ‖x‖)) twoPt := integrable_twoPt _

theorem letwinQuadraticBound_twoPt : LetwinQuadraticBound twoPt := by
  classical
  rw [LetwinQuadraticBound]
  intro M _
  let c : ℝ := M 1
  have hM (x : ℝ) : M x = c * x := by
    change M x = (M 1) * x
    rw [show x = x • (1 : ℝ) by simp, M.map_smul]
    simp [mul_comm]
  have hquad (x : ℝ) : ⟪M x, x⟫ = c * x ^ 2 := by
    rw [hM]
    change ⟪c • x, x⟫ = c * x ^ 2
    simp [pow_two, smul_eq_mul]
    ring
  have hvar : ∫ x : ℝ, (⟪M x, x⟫ - ∫ y : ℝ, ⟪M y, y⟫ ∂twoPt) ^ 2 ∂twoPt = 9 / 4 * c ^ 2 := by
    simp_rw [hquad]
    rw [integral_twoPt (fun y => c * y ^ 2), integral_twoPt]
    ring
  have hdim : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  let : Unique (Fin (Module.finrank ℝ ℝ)) :=
    { default := ⟨0, by omega⟩
      uniq := by
        intro i
        apply Fin.ext
        omega }
  have hsum : ∑ i, ∑ j, ⟪M (stdOrthonormalBasis ℝ ℝ i), (stdOrthonormalBasis ℝ ℝ j)⟫ ^ 2 = c ^ 2 := by
    simp only [Fintype.sum_unique]
    let b : ℝ := stdOrthonormalBasis ℝ ℝ default
    have hb : b ^ 2 = 1 := by
      have hn : ‖b‖ = 1 := by
        dsimp [b]
        exact (stdOrthonormalBasis ℝ ℝ).norm_eq_one default
      rw [Real.norm_eq_abs] at hn
      nlinarith [sq_abs b]
    rw [show ⟪M b, b⟫ = c * b ^ 2 by
      dsimp [b]
      exact hquad _]
    rw [hb]
    ring
  rw [hvar, hsum]
  nlinarith [sq_nonneg c]

/-- The witness is skewed: `κ₃(1, 1, 1) = E X³ = 3/2 ≠ 0`. -/
theorem cumulant_three_twoPt : cumulant twoPt 3 ![1, 1, 1] = 3 / 2 := by
  have := isProbabilityMeasure_twoPt
  rw [cumulant_three_eq_integral twoPt integrable_exp_mul_norm_twoPt centered_twoPt, integral_twoPt]
  simp only [RCLike.inner_apply, conj_trivial]
  norm_num

/-- The conditional BKL Lemma 4.2 for a skewed law with every premise discharged: the bound is
attained by a nonzero third cumulant (`κ₃(1,1,1)² = 9/4 ≤ 8`). -/
theorem sum_sq_cumulant_three_le_twoPt (u : ℝ) :
    ∑ j, ∑ k, cumulant twoPt 3 ![u, stdOrthonormalBasis ℝ ℝ j, stdOrthonormalBasis ℝ ℝ k] ^ 2 ≤
      8 * ‖u‖ ^ 2 := by
  have := isProbabilityMeasure_twoPt
  exact sum_sq_cumulant_three_le_of_letwin twoPt integrable_exp_mul_norm_twoPt centered_twoPt
    isotropic_twoPt letwinQuadraticBound_twoPt u

end BKLSkewWitness

#print axioms BKLThirdCumulantWitness.letwinQuadraticBound_unifSym
#print axioms BKLThirdCumulantWitness.sum_sq_cumulant_three_le_unifSym
#print axioms BKLThirdCumulantWitness.taylorTensor_two_eq_half_cumulant_unifSym
#print axioms BKLSkewWitness.letwinQuadraticBound_twoPt
#print axioms BKLSkewWitness.cumulant_three_twoPt
#print axioms BKLSkewWitness.sum_sq_cumulant_three_le_twoPt
#print axioms FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin
#print axioms FunctionalInequalities.Analysis.BakryEmery.cumulant_three_eq_integral
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_two_inner_eq_of_centered
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_logLaplace_zero_apply

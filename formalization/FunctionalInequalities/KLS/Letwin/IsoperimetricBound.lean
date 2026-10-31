module

public import FunctionalInequalities.KLS.BKL.Poincare
public import FunctionalInequalities.KLS.Geometry.Cheeger.Comparison
public import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Buser
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Letwin's logarithmic-quarter isoperimetric bound from the dimension-free KLS bound

Letwin arXiv:2607.24164v1, Theorem 1.1, n ≥ 2: ψ_n ≤ C (log n)^{1/4} with one universal C > 0.
Here ψ_n is written as the supremum of the existing literature isoperimetric inverse scale
across isotropic log-concave laws on ℝⁿ. This proof uses the stronger dimension-free
BKL theorem and the π Cheeger–Buser comparison. It is an alternative proof of the source
statement, rather than the paper's original third-moment argument.

Letwin arXiv:2607.24164v1, Section 1, comparison display `1/4 ≤ ψ_μ² / C_P(μ) ≤ π`
(`inverseScale_sq_div_literatureConstant_mem_Icc`): for every log-concave law on ℝⁿ, n ≥ 1, with a
Borell density, `0 < C_P(μ) < ∞` and the ratio lies in `[1/4, π]`. The family theorem
`inv_smoothConstant_univ_sq_div_literatureConstant_mem_Icc` takes the KLS proposition as a premise
for finiteness of `C_P`; here it is discharged by the dimension-free bound.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace FunctionalInequalities.KLS.LogConcave

/-- Letwin Theorem 1.1, with the supremum over all isotropic log-concave laws written explicitly. -/
theorem exists_logQuarter_isoperimetricBound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      (⨆ (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (_ : LogConcave μ) (_ : Isotropic μ),
        Isoperimetry.inverseScale μ) ≤ ENNReal.ofReal (C * (Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) := by
  obtain ⟨A, _hA, hAll⟩ := BKL.Localization.exists_isotropicBound.{0}
  let B : ℝ := 1 + Real.pi * (A : ℝ)
  have hB1 : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (mul_nonneg Real.pi_pos.le A.coe_nonneg)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow2 : 0 < (Real.log 2) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlog2 _
  refine ⟨B / (Real.log 2) ^ (1 / 4 : ℝ), div_pos hB hpow2, fun n hn => ?_⟩
  refine iSup_le fun μ => iSup_le fun hLC => iSup_le fun hiso => ?_
  have hP := hAll (EuclideanSpace ℝ (Fin n)) μ hLC hiso
  have hsq : Isoperimetry.inverseScale μ ^ 2 ≤ ENNReal.ofReal (Real.pi * (A : ℝ)) := by
    calc Isoperimetry.inverseScale μ ^ 2 ≤
        ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ :=
      hLC.inverseScale_sq_le_pi_literature
      _ ≤ ENNReal.ofReal Real.pi * (A : ENNReal) := by gcongr
      _ = ENNReal.ofReal (Real.pi * (A : ℝ)) := by
        rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_coe_nnreal]
  have hbound : Isoperimetry.inverseScale μ ≤ ENNReal.ofReal B := by
    by_cases hsmall : Isoperimetry.inverseScale μ ≤ 1
    · refine hsmall.trans ?_
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hB1
    · have hone : 1 ≤ Isoperimetry.inverseScale μ := (lt_of_not_ge hsmall).le
      have hself : Isoperimetry.inverseScale μ ≤ Isoperimetry.inverseScale μ ^ 2 := by
        calc Isoperimetry.inverseScale μ = Isoperimetry.inverseScale μ * 1 := (mul_one _).symm
          _ ≤ Isoperimetry.inverseScale μ * Isoperimetry.inverseScale μ := by gcongr
          _ = Isoperimetry.inverseScale μ ^ 2 := (pow_two _).symm
      exact hself.trans (hsq.trans (ENNReal.ofReal_le_ofReal (by dsimp [B]; linarith)))
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
  have hp : (Real.log 2) ^ (1 / 4 : ℝ) ≤ (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hlog2.le hlog (by norm_num)
  have hfinal : B ≤ B / (Real.log 2) ^ (1 / 4 : ℝ) * (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) := by
    calc B = B / (Real.log 2) ^ (1 / 4 : ℝ) * (Real.log 2) ^ (1 / 4 : ℝ) :=
      (div_mul_cancel₀ B hpow2.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (div_pos hB hpow2).le
  exact hbound.trans (ENNReal.ofReal_le_ofReal hfinal)

/-- **Letwin's comparison display** (arXiv:2607.24164v1, Section 1): for a log-concave probability
law `μ` on `ℝⁿ`, `n ≥ 1`, with a Borell density `ρ` relative to Lebesgue measure (equivalently, `μ`
is full-dimensional), `0 < C_P(μ) < ∞` and `1/4 ≤ ψ_μ² / C_P(μ) ≤ π`. Here
`ψ_μ = Isoperimetry.inverseScale μ`, which equals `(h_S)⁻¹` for the ambient smooth-boundary
constant `h_S = Isoperimetry.smoothConstant ρ univ μ`
(`Isoperimetry.inverseScale_eq_inv_smoothConstant_univ`), and
`C_P(μ) = Poincare.LocalSlope.Intrinsic.constant μ` is the constant of Equation (1.1). The
finiteness of `C_P(μ)` comes from the dimension-free bound `KLS.BKL.Localization.conjecture`. -/
theorem inverseScale_sq_div_literatureConstant_mem_Icc {n : ℕ} (hn : n ≠ 0)
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : LogConcave μ)
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : IsBorellDensity (μ : Measure (EuclideanSpace ℝ (Fin n))) volume ρ) :
    0 < Poincare.LocalSlope.Intrinsic.constant μ ∧ Poincare.LocalSlope.Intrinsic.constant μ < ⊤ ∧
      Isoperimetry.inverseScale μ ^ 2 / Poincare.LocalSlope.Intrinsic.constant μ ∈
        Set.Icc 4⁻¹ (ENNReal.ofReal Real.pi) := by
  rw [Isoperimetry.inverseScale_eq_inv_smoothConstant_univ hρ]
  exact hμ.inv_smoothConstant_univ_sq_div_literatureConstant_mem_Icc
    BKL.Localization.conjecture hn hρ

end FunctionalInequalities.KLS.LogConcave

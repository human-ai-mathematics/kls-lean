module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Moments.MGFAnalytic
import TauCeti.Probability.Distributions.Laplace

/-!
# The Laplace law

The Laplace law with rate `β > 0` has density `(β/2) e^{-β|s|}` on `ℝ`. It is the noise `η_β` of
Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1. The function `s ↦ e^{ws}`
is integrable for `η_β` exactly when `|w| < β`. On this interval the moment generating function
is `β²/(β² - w²)`. The law has mean `0`, second moment `2/β²` and total mass `1`.
The proofs identify `η_β` with Tau Ceti's Laplace law of location `0` and scale `β⁻¹`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Probability.Line

/-- The Laplace density `(β/2) e^{-β|s|}`. -/
def laplaceDensity (β s : ℝ) : ℝ := β / 2 * Real.exp (-(β * |s|))

/-- The Laplace law with rate `β`: Lebesgue measure with density `(β/2) e^{-β|s|}`. -/
def laplaceMeasure (β : ℝ) : Measure ℝ :=
  volume.withDensity fun s => ENNReal.ofReal (laplaceDensity β s)

private theorem laplaceDensity_eq_laplacePDFReal {β : ℝ} (hβ : 0 < β) :
    laplaceDensity β = TauCeti.Probability.laplacePDFReal 0 β⁻¹ := by
  funext x
  rw [TauCeti.Probability.laplacePDFReal_of_pos (inv_pos.mpr hβ), laplaceDensity,
    sub_zero, div_inv_eq_mul]
  simp [mul_comm, div_eq_mul_inv]

private theorem laplaceMeasure_eq_scale {β : ℝ} (hβ : 0 < β) :
    laplaceMeasure β = TauCeti.Probability.laplaceMeasure 0 β⁻¹ := by
  rw [laplaceMeasure, TauCeti.Probability.laplaceMeasure_eq_withDensity, laplaceDensity_eq_laplacePDFReal hβ]
  congr 1
  exact funext fun x => (TauCeti.Probability.laplacePDF_eq_ofReal 0 β⁻¹ x).symm

/-- The Laplace density has total integral `1`. -/
theorem integral_laplaceDensity {β : ℝ} (hβ : 0 < β) :
    ∫ x : ℝ, laplaceDensity β x = 1 := by
  rw [laplaceDensity_eq_laplacePDFReal hβ]
  exact TauCeti.Probability.integral_laplacePDFReal (inv_pos.mpr hβ) 0

/-- The Laplace density is integrable. -/
theorem integrable_laplaceDensity {β : ℝ} (hβ : 0 < β) :
    Integrable (laplaceDensity β) := by
  rw [laplaceDensity_eq_laplacePDFReal hβ]
  exact TauCeti.Probability.integrable_laplacePDFReal 0

/-- For `β > 0`, `laplaceMeasure β` has total mass `1`. -/
theorem isProbabilityMeasure_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (laplaceMeasure β) := by
  rw [laplaceMeasure_eq_scale hβ]
  exact TauCeti.Probability.isProbabilityMeasure_laplaceMeasure (inv_pos.mpr hβ) 0

/-! ### Local moment generating function and moments

The moment generating function on `|w| < β` gives moment integrability and the derivative
formula at `0`. The first two moments follow from the corresponding Laplace formulas. -/

section Moments

open ProbabilityTheory Filter Set
open scoped Topology

private theorem laplaceMeasure_mgf_scale {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    Integrable (fun s : ℝ => Real.exp (w * s)) (TauCeti.Probability.laplaceMeasure 0 β⁻¹) ∧
      mgf id (TauCeti.Probability.laplaceMeasure 0 β⁻¹) w = β ^ 2 / (β ^ 2 - w ^ 2) := by
  have hb : 0 < β⁻¹ := inv_pos.mpr hβ
  have ht : w ∈ Ioo (-(β⁻¹)⁻¹) (β⁻¹)⁻¹ := by simpa only [inv_inv, mem_Ioo] using abs_lt.mp hw
  refine ⟨(TauCeti.Probability.integrable_exp_mul_laplaceMeasure_iff hb 0 w).2 ht, ?_⟩
  rw [TauCeti.Probability.mgf_id_laplaceMeasure hb 0 ht, zero_mul, Real.exp_zero, inv_pow]
  field_simp [hβ.ne']

/-- **Local moment generating function of the Laplace law**: for `β > 0` and `|w| < β`, the
function `s ↦ e^{ws} (β/2) e^{-β|s|}` is integrable with integral `β² / (β² - w²)`. -/
theorem integral_exp_mul_laplaceDensity {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    MeasureTheory.Integrable (fun s => Real.exp (w * s) * laplaceDensity β s) ∧
      ∫ s, Real.exp (w * s) * laplaceDensity β s = β ^ 2 / (β ^ 2 - w ^ 2) := by
  obtain ⟨hi, hm⟩ := laplaceMeasure_mgf_scale hβ hw
  rw [TauCeti.Probability.integrable_laplaceMeasure_iff, ← laplaceDensity_eq_laplacePDFReal hβ] at hi
  change (∫ s : ℝ, Real.exp (w * s) ∂TauCeti.Probability.laplaceMeasure 0 β⁻¹) = _ at hm
  rw [TauCeti.Probability.integral_laplaceMeasure_eq, ← laplaceDensity_eq_laplacePDFReal hβ] at hm
  exact ⟨by simpa only [smul_eq_mul, mul_comm] using hi,
    by simpa only [smul_eq_mul, mul_comm] using hm⟩

/-- The law-level moment generating function on `|w| < β`. -/
theorem laplaceMeasure_mgf {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    Integrable (fun s : ℝ => Real.exp (w * s)) (laplaceMeasure β) ∧
      mgf id (laplaceMeasure β) w = β ^ 2 / (β ^ 2 - w ^ 2) := by
  rw [laplaceMeasure_eq_scale hβ]
  exact laplaceMeasure_mgf_scale hβ hw

/-- `0` is an interior point of the exponential-integrability set of the Laplace law. -/
theorem zero_mem_interior_integrableExpSet_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    0 ∈ interior (integrableExpSet id (laplaceMeasure β)) := by
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (Ioo_mem_nhds (by linarith : -β < 0) hβ)
  intro w hw
  exact (laplaceMeasure_mgf hβ (abs_lt.mpr hw)).1

/-- Near `0` the moment generating function is the rational function `β²/(β² - w²)`. -/
theorem laplaceMeasure_mgf_eventuallyEq {β : ℝ} (hβ : 0 < β) :
    mgf id (laplaceMeasure β) =ᶠ[𝓝 (0 : ℝ)] fun w => β ^ 2 / (β ^ 2 - w ^ 2) := by
  filter_upwards [Ioo_mem_nhds (by linarith : -β < 0) hβ] with w hw
  exact (laplaceMeasure_mgf hβ (abs_lt.mpr hw)).2

/-- The `k`-th moment is the `k`-th derivative at `0` of `β²/(β² - w²)`. -/
theorem laplaceMeasure_moment_eq_iteratedDeriv {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    (∫ s : ℝ, s ^ k ∂laplaceMeasure β) =
      iteratedDeriv k (fun w : ℝ => β ^ 2 / (β ^ 2 - w ^ 2)) 0 := by
  have h := ProbabilityTheory.iteratedDeriv_mgf_zero (X := id)
    (zero_mem_interior_integrableExpSet_laplaceMeasure hβ) k
  have hd := Filter.EventuallyEq.iteratedDeriv_eq k (laplaceMeasure_mgf_eventuallyEq hβ)
  simpa only [Pi.pow_apply, id_eq] using h.symm.trans hd

/-- Every polynomial moment of the Laplace law is finite (from the rates `±β/2`). -/
theorem integrable_pow_laplaceMeasure {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    Integrable (fun s : ℝ => s ^ k) (laplaceMeasure β) := by
  have hhalf : 0 < β / 2 := by positivity
  have hsmall : |β / 2| < β := by rw [abs_of_pos hhalf]; linarith
  have hp := (laplaceMeasure_mgf hβ hsmall).1
  have hn := (laplaceMeasure_mgf (w := -(β / 2)) hβ (by simpa only [abs_neg] using hsmall)).1
  exact ProbabilityTheory.integrable_pow_of_integrable_exp_mul
    (X := id) hhalf.ne' hp hn k

/-- The Laplace law has the exponential moment `e^{(β/2)|s|}`. -/
theorem integrable_exp_abs_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    Integrable (fun s : ℝ => Real.exp ((β / 2) * |s|)) (laplaceMeasure β) := by
  have hhalf : 0 < β / 2 := by positivity
  have hsmall : |β / 2| < β := by rw [abs_of_pos hhalf]; linarith
  have hp := (laplaceMeasure_mgf hβ hsmall).1
  have hn := (laplaceMeasure_mgf (w := -(β / 2)) hβ (by simpa only [abs_neg] using hsmall)).1
  exact ProbabilityTheory.integrable_exp_mul_abs (X := id) hp hn

/-- The Laplace law is centered. -/
theorem integral_id_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    (∫ s : ℝ, s ∂laplaceMeasure β) = 0 := by
  rw [laplaceMeasure_eq_scale hβ]
  exact TauCeti.Probability.integral_id_laplaceMeasure (inv_pos.mpr hβ) 0

/-- The second moment of the Laplace law is `2/β²`. -/
theorem integral_sq_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    (∫ s : ℝ, s ^ 2 ∂laplaceMeasure β) = 2 / β ^ 2 := by
  rw [laplaceMeasure_eq_scale hβ]
  have hm := TauCeti.Probability.integral_pow_abs_sub_laplaceMeasure (inv_pos.mpr hβ) 0 2
  norm_num at hm
  simpa only [div_eq_mul_inv, inv_pow] using hm

/-- **Mean and variance of the Laplace law.** -/
theorem laplaceMeasure_moments {β : ℝ} (hβ : 0 < β) :
    Integrable (fun s : ℝ => s) (laplaceMeasure β) ∧
      Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β) ∧
      (∫ s : ℝ, s ∂laplaceMeasure β) = 0 ∧
      (∫ s : ℝ, s ^ 2 ∂laplaceMeasure β) = 2 / β ^ 2 := by
  refine ⟨?_, integrable_pow_laplaceMeasure hβ 2, integral_id_laplaceMeasure hβ,
    integral_sq_laplaceMeasure hβ⟩
  simpa only [pow_one] using integrable_pow_laplaceMeasure hβ 1

/--
**The noise factor of BKL (111) has zero derivative at the origin**: `w ↦ log ∫ e^{(w/σ)s} dη_β(s)`
is differentiable at `0` with derivative `0`, since `η_β` is centered. -/
theorem hasDerivAt_log_integral_exp_laplaceMeasure_zero {β σ : ℝ} (hβ : 0 < β) (hσ : σ ≠ 0) :
    HasDerivAt (fun w : ℝ => Real.log (∫ s : ℝ, Real.exp (w / σ * s) ∂laplaceMeasure β)) 0 0 := by
  have hi (w : ℝ) (hw : |w / σ| < β) :
    (∫ s : ℝ, Real.exp (w / σ * s) ∂laplaceMeasure β) = β ^ 2 / (β ^ 2 - (w / σ) ^ 2) := by
    have h := (laplaceMeasure_mgf hβ hw).2
    simpa only [ProbabilityTheory.mgf, id] using h
  have hev : ∀ᶠ w in nhds (0 : ℝ), |w / σ| < β := by
    have hc : ContinuousAt (fun w : ℝ => |w / σ|) 0 := by fun_prop
    exact hc.eventually (Iio_mem_nhds (by simpa using hβ))
  have hsq : HasDerivAt (fun w : ℝ => (w / σ) ^ 2) 0 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).div_const σ).pow 2
    exact h.congr_deriv (by simp)
  have hden : HasDerivAt (fun w : ℝ => β ^ 2 - (w / σ) ^ 2) 0 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (β ^ 2)).sub hsq
    exact h.congr_deriv (by simp)
  have hG : HasDerivAt (fun w : ℝ => β ^ 2 / (β ^ 2 - (w / σ) ^ 2)) 0 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (β ^ 2)).div hden (by simp [hβ.ne'])
    exact h.congr_deriv (by simp)
  have hlog : HasDerivAt (fun w : ℝ => Real.log (β ^ 2 / (β ^ 2 - (w / σ) ^ 2))) 0 0 := by
    have h := hG.log (by simp [hβ.ne'])
    exact h.congr_deriv (by simp)
  refine hlog.congr_of_eventuallyEq ?_
  filter_upwards [hev] with w hw
  rw [hi w hw]

end Moments

end FunctionalInequalities.Probability.Line

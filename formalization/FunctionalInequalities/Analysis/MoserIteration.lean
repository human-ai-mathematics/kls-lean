import FunctionalInequalities.Analysis.DyadicSummation
import FunctionalInequalities.Analysis.LpExponent
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Radius-normalized Moser iterations of `L^p` norms

Generic iteration of actual extended `L^p` norms along exponents `p0 κ^m` (`κ > 1`) and measures `μ m`, as in the Moser
iteration of Gilbarg–Trudinger (2001), proof of Theorem 8.18. The physical one-step estimate is a premise:
`‖f‖_{p0 κ^{m+1}, μ (m+1)}^{p0 κ^m} ≤ C 4^m R^{-a} ‖f‖_{p0 κ^m, μ m}^{p0 κ^m}`, with a general physical exponent `a` and the
normalization `N/κ + a = N` (for example `a = 2`, `N = n` in dimension `n > 2`, and `a = 2 − 2/κ`, `N = 2` in dimension two,
where the finite-`q` Sobolev support factor scales like `R^{2/κ}`). The radius is normalized before the iteration, for every
`R > 0`; every norm is finite before any real representative is taken.

* `eLpNorm_top_le_of_shrinking_norm_steps`: infinite horizon, ending in the essential supremum on a fixed inner measure.
* `finite_normalized_eLpNorm_sequence_bound`: finite horizon, for positive-power chains that must stop.
* `le_rpow_one_div_mul_of_rpow_le`: the `ℝ≥0∞` root `X^p ≤ C Y^p ⇒ X ≤ C^{1/p} Y` used by the steps.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FunctionalInequalities.Analysis
/-- Taking positive roots of a homogeneous extended-norm inequality, including infinite norms. -/
theorem le_rpow_one_div_mul_of_rpow_le {X Y C : ℝ≥0∞} {p : ℝ} (hp : 0 < p)
    (h : X^p ≤ C * Y^p) : X ≤ C^(1/p) * Y := by
  apply (ENNReal.rpow_le_rpow_iff hp).1
  have he : (1/p) * p = 1 := by field_simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,← ENNReal.rpow_mul,he,ENNReal.rpow_one]
  exact h

/-- Exact radius normalization for an arbitrary physical gain `a` satisfying `N/κ+a=N`.
This includes the support-volume scaling in dimension two; extended norms may be infinite. -/
private theorem radius_normalized_step {X Y C : ℝ≥0∞} {N κ p R a : ℝ}
    (hκ : 0 < κ) (hp : 0 < p) (hR : 0 < R) (hscale : N/κ+a=N)
    (h : X^p ≤ C*(ENNReal.ofReal R)^(-a)*Y^p) :
    (ENNReal.ofReal R)^(-N/(κ*p))*X ≤
      C^(1/p)*((ENNReal.ofReal R)^(-N/p)*Y) := by
  let B := ENNReal.ofReal R
  have hB0 : B ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hBt : B ≠ ∞ := ENNReal.ofReal_ne_top
  apply le_rpow_one_div_mul_of_rpow_le hp
  have heX : (-N/(κ*p))*p = -N/κ := by field_simp
  have heY : (-N/p)*p = -N := by field_simp
  have he : -N/κ+-a = -N := by simp only [neg_div]; linarith
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ← ENNReal.rpow_mul,← ENNReal.rpow_mul,heX,heY]
  calc
    _ ≤ B^(-N/κ)*(C*B^(-a)*Y^p) := mul_le_mul_of_nonneg_left h zero_le
    _ = C*(B^(-N/κ)*B^(-a))*Y^p := by ac_rfl
    _ = C*B^(-N/κ+-a)*Y^p := by rw [← ENNReal.rpow_add _ _ hB0 hBt]
    _ = _ := by rw [he]; ac_rfl

/-- Iteration of actual finite extended norms after radius normalization. The physical one-step
estimate is retained as a premise; this is the generic recurrence, not the PDE input producer. -/
private theorem normalized_eLpNorm_sequence_bound
    {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X) (f : X → ℝ)
    {N κ p0 R C a : ℝ} (hκ : 1 < κ) (hp0 : 0 < p0) (hR : 0 < R) (hC : 1 ≤ C)
    (hscale : N / κ + a = N)
    (hmem : ∀ m, MemLp f (ENNReal.ofReal (p0 * κ ^ m)) (μ m))
    (hstep : ∀ m,
      (eLpNorm f (ENNReal.ofReal (p0 * κ ^ (m+1))) (μ (m+1))) ^ (p0 * κ ^ m) ≤
        ENNReal.ofReal (C * (4 : ℝ) ^ m) * (ENNReal.ofReal R) ^ (-a : ℝ) *
          (eLpNorm f (ENNReal.ofReal (p0 * κ ^ m)) (μ m)) ^ (p0 * κ ^ m)) :
    ∀ m, (ENNReal.ofReal R) ^ (-N / (p0 * κ ^ m)) *
        eLpNorm f (ENNReal.ofReal (p0 * κ ^ m)) (μ m) ≤
      ENNReal.ofReal (Real.exp
        ((Real.log C / (1-κ⁻¹) + Real.log 4 * κ⁻¹ / (1-κ⁻¹)^2) / p0)) *
        ((ENNReal.ofReal R) ^ (-N/p0) * eLpNorm f (ENNReal.ofReal p0) (μ 0)) := by
  let P := fun m : ℕ => p0 * κ ^ m
  let Y := fun m : ℕ => (ENNReal.ofReal R) ^ (-N / P m) * eLpNorm f (ENNReal.ofReal (P m)) (μ m)
  have hκ0 : 0 < κ := zero_lt_one.trans hκ
  have hP (m : ℕ) : 0 < P m := mul_pos hp0 (pow_pos hκ0 m)
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hY (m : ℕ) : Y m ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hR0 ENNReal.ofReal_ne_top) (hmem m).2.ne
  have hEN (m : ℕ) : Y (m+1) ≤ (ENNReal.ofReal (C*(4 : ℝ)^m)) ^ (1/P m) * Y m := by
    have H := radius_normalized_step hκ0 (hP m) hR hscale (hstep m)
    have hnext : P (m+1) = κ * P m := by dsimp only [P]; rw [pow_succ]; ring
    simpa only [Y, ← hnext] using H
  have hreal (m : ℕ) : (Y (m+1)).toReal ≤ (C*(4 : ℝ)^m) ^ (1/P m) * (Y m).toReal := by
    have hCn : 0 ≤ C*(4 : ℝ)^m := mul_nonneg (zero_le_one.trans hC) (pow_nonneg (by norm_num) m)
    have hrt : (ENNReal.ofReal (C*(4 : ℝ)^m)) ^ (1/P m) * Y m ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) (hY m)
    have H := ENNReal.toReal_mono hrt (hEN m)
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hCn] using H
  have hb := geometric_root_recurrence_bound hκ hp0 hC (fun m => (Y m).toReal)
    (fun _ => ENNReal.toReal_nonneg) hreal
  intro m
  have hE : 0 ≤ Real.exp
      ((Real.log C / (1-κ⁻¹) + Real.log 4 * κ⁻¹ / (1-κ⁻¹)^2) / p0) := (Real.exp_pos _).le
  have ht : ENNReal.ofReal (Real.exp
      ((Real.log C / (1-κ⁻¹) + Real.log 4 * κ⁻¹ / (1-κ⁻¹)^2) / p0)) * Y 0 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hY 0)
  have H := (ENNReal.toReal_le_toReal (hY m) ht).mp (by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hE] using hb m)
  simpa only [Y, P, pow_zero, mul_one] using H

/-- The limit of radius-normalized finite norms controls the essential supremum.
No pointwise supremum is asserted. -/
private theorem eLpNorm_top_le_of_radius_normalized_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    {f : X → ℝ} (hf : MemLp f ∞ μ) (p : ℕ → NNReal)
    (hp : Tendsto p atTop atTop) {R N : ℝ} (hR : 0 < R) {B : ℝ≥0∞}
    (hbound : ∀ k, (ENNReal.ofReal R) ^ (-N / (p k : ℝ)) * eLpNorm f (p k : ENNReal) μ ≤ B) :
    eLpNorm f ∞ μ ≤ B := by
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hn (k : ℕ) : eLpNorm f (p k : ENNReal) μ ≤ (ENNReal.ofReal R) ^ (N / (p k : ℝ)) * B := by
    calc
      _ = (ENNReal.ofReal R) ^ (N / (p k : ℝ)) *
          ((ENNReal.ofReal R) ^ (-N / (p k : ℝ)) * eLpNorm f (p k : ENNReal) μ) := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ hR0 ENNReal.ofReal_ne_top]
        have he : N / (p k : ℝ) + -N / (p k : ℝ) = 0 := by ring
        rw [he, ENNReal.rpow_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound k) zero_le
  have hinv : Tendsto (fun k => (p k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.mpr hp)
  have he : Tendsto (fun k => N / (p k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv
  have hr : Tendsto (fun k => R ^ (N / (p k : ℝ))) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero, Function.comp_def] using (Real.continuousAt_const_rpow hR.ne').tendsto.comp he
  have hfac : Tendsto (fun k => (ENNReal.ofReal R) ^ (N / (p k : ℝ))) atTop (𝓝 1) := by
    simpa only [ENNReal.ofReal_rpow_of_pos hR, ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  have hlim := tendsto_eLpNorm_finite_measure μ hf p hp
  have hlimB : Tendsto (fun k => (ENNReal.ofReal R) ^ (N / (p k : ℝ)) * B) atTop (𝓝 B) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul hfac (Or.inl one_ne_zero)
      tendsto_const_nhds (Or.inr ENNReal.one_ne_top)
  exact le_of_tendsto_of_tendsto' hlim hlimB hn

/-- Generic inverse-Moser endpoint on a fixed inner measure dominated by all shrinking measures.
The derivative-energy producer remains a separate obligation in the actual application. -/
theorem eLpNorm_top_le_of_shrinking_norm_steps
    {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X) (ν : Measure X)
    [IsFiniteMeasure ν] [NeZero ν] (f : X → ℝ) (hf : MemLp f ∞ ν)
    (hν : ∀ m, ν ≤ μ m)
    {N κ p0 R C a : ℝ} (hκ : 1 < κ) (hp0 : 0 < p0) (hR : 0 < R) (hC : 1 ≤ C)
    (hscale : N / κ + a = N)
    (hmem : ∀ m, MemLp f (ENNReal.ofReal (p0 * κ ^ m)) (μ m))
    (hstep : ∀ m,
      (eLpNorm f (ENNReal.ofReal (p0 * κ ^ (m+1))) (μ (m+1))) ^ (p0 * κ ^ m) ≤
        ENNReal.ofReal (C * (4 : ℝ) ^ m) * (ENNReal.ofReal R) ^ (-a : ℝ) *
          (eLpNorm f (ENNReal.ofReal (p0 * κ ^ m)) (μ m)) ^ (p0 * κ ^ m)) :
    eLpNorm f ∞ ν ≤
      ENNReal.ofReal (Real.exp
        ((Real.log C / (1-κ⁻¹) + Real.log 4 * κ⁻¹ / (1-κ⁻¹)^2) / p0)) *
        ((ENNReal.ofReal R) ^ (-N/p0) * eLpNorm f (ENNReal.ofReal p0) (μ 0)) := by
  have hκ0 : 0 < κ := zero_lt_one.trans hκ
  let p : ℕ → NNReal := fun m => ⟨p0 * κ ^ m, (mul_pos hp0 (pow_pos hκ0 m)).le⟩
  have hp : Tendsto p atTop atTop := by
    apply NNReal.tendsto_coe_atTop.mp
    exact (tendsto_pow_atTop_atTop_of_one_lt hκ).const_mul_atTop hp0
  have hb := normalized_eLpNorm_sequence_bound μ f hκ hp0 hR hC hscale hmem hstep
  apply eLpNorm_top_le_of_radius_normalized_bounds ν hf p hp hR (N := N)
  intro m
  have hn := eLpNorm_mono_measure f (hν m) (p := ENNReal.ofReal (p0 * κ ^ m))
  have H := mul_le_mul_of_nonneg_left hn (show 0 ≤ (ENNReal.ofReal R) ^ (-N/(p0*κ^m)) by exact zero_le)
  have hep : (p m : ENNReal) = ENNReal.ofReal (p0*κ^m) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  change (ENNReal.ofReal R) ^ (-N/(p0*κ^m)) * eLpNorm f (p m : ENNReal) ν ≤ _
  rw [hep]
  exact H.trans (hb m)

/-- Iteration of actual finite extended norms after radius normalization. The physical one-step
estimate is retained as a premise; this is the generic recurrence, not the PDE input producer. -/
theorem finite_normalized_eLpNorm_sequence_bound
    {X : Type*} [MeasurableSpace X] (μ : ℕ → Measure X) (f : X → ℝ)
    {N κ p0 R C a : ℝ} (hκ : 1 < κ) (hp0 : 0 < p0) (hR : 0 < R) (hC : 1 ≤ C)
    (hscale : N / κ + a = N)
    (hmem : ∀ m, MemLp f (ENNReal.ofReal (p0 * κ ^ m)) (μ m))
    (K : ℕ)
    (hstep : ∀ m < K,
      (eLpNorm f (ENNReal.ofReal (p0 * κ ^ (m+1))) (μ (m+1))) ^ (p0 * κ ^ m) ≤
        ENNReal.ofReal (C * (4 : ℝ) ^ m) * (ENNReal.ofReal R) ^ (-a : ℝ) *
          (eLpNorm f (ENNReal.ofReal (p0 * κ ^ m)) (μ m)) ^ (p0 * κ ^ m)) :
    (ENNReal.ofReal R) ^ (-N / (p0 * κ ^ K)) *
        eLpNorm f (ENNReal.ofReal (p0 * κ ^ K)) (μ K) ≤
      ENNReal.ofReal (Real.exp
        ((Real.log C / (1-κ⁻¹) + Real.log 4 * κ⁻¹ / (1-κ⁻¹)^2) / p0)) *
        ((ENNReal.ofReal R) ^ (-N/p0) * eLpNorm f (ENNReal.ofReal p0) (μ 0)) := by
  let P := fun m : ℕ => p0 * κ ^ m
  let Y := fun m : ℕ => (ENNReal.ofReal R) ^ (-N / P m) * eLpNorm f (ENNReal.ofReal (P m)) (μ m)
  have hκ0 : 0 < κ := zero_lt_one.trans hκ
  have hP (m : ℕ) : 0 < P m := mul_pos hp0 (pow_pos hκ0 m)
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hY (m : ℕ) : Y m ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hR0 ENNReal.ofReal_ne_top) (hmem m).2.ne
  have hEN (m : ℕ) (hm : m < K) : Y (m+1) ≤ (ENNReal.ofReal (C*(4 : ℝ)^m)) ^ (1/P m) * Y m := by
    have H := radius_normalized_step hκ0 (hP m) hR hscale (hstep m hm)
    have hnext : P (m+1) = κ * P m := by dsimp only [P]; rw [pow_succ]; ring
    simpa only [Y, ← hnext] using H
  have hreal (m : ℕ) (hm : m < K) : (Y (m+1)).toReal ≤ (C*(4 : ℝ)^m) ^ (1/P m) * (Y m).toReal := by
    have hCn : 0 ≤ C*(4 : ℝ)^m := mul_nonneg (zero_le_one.trans hC) (pow_nonneg (by norm_num) m)
    have hrt : (ENNReal.ofReal (C*(4 : ℝ)^m)) ^ (1/P m) * Y m ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) (hY m)
    have H := ENNReal.toReal_mono hrt (hEN m hm)
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hCn] using H
  have hb := finite_geometric_root_recurrence_bound hκ hp0 hC (fun m => (Y m).toReal)
    (fun _ => ENNReal.toReal_nonneg) K hreal
  have hE : 0 ≤ Real.exp
      ((Real.log C / (1-κ⁻¹) + Real.log 4 * κ⁻¹ / (1-κ⁻¹)^2) / p0) := (Real.exp_pos _).le
  have ht : ENNReal.ofReal (Real.exp
      ((Real.log C / (1-κ⁻¹) + Real.log 4 * κ⁻¹ / (1-κ⁻¹)^2) / p0)) * Y 0 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hY 0)
  have H := (ENNReal.toReal_le_toReal (hY K) ht).mp (by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hE] using hb)
  simpa only [Y, P, pow_zero, mul_one] using H

end FunctionalInequalities.Analysis

import FunctionalInequalities.Analysis.Mollification
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Weak directional derivatives

`HasWeakDerivAlong f g v`: `g` is the weak derivative of `f` along `v`, tested against `C¹` functions with compact
support, both functions locally integrable (definition approved 2026-10-13, see
build/reviews/2026-10-12-bkl-claude-goal/routes/letwin-weak-definitions.md); uniqueness a.e., classical derivatives of
`C¹` and Lipschitz functions, products with `C¹` multipliers, global-L² weak products and bounded
rough products with compact-local L² derivatives. These are weak-calculus supports for the moment-map
route to Letwin arXiv:2607.24164v1; they do not establish Hessian evolution, a trace estimate or constant 8.
Proof bodies: GPT (Letwin sub-controller task L-W3a); statements by the Letwin sub-controller; placement: Claude.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `g` is the **weak directional derivative** of `f` along `v`, tested against `C¹` functions with
compact support; both functions are locally integrable (so the integrals are not junk). Weak Letwin
route (routes/letwin-weak-definitions.md, item 4). -/
def HasWeakDerivAlong (f g : E → ℝ) (v : E) : Prop :=
  LocallyIntegrable f (volume : Measure E) ∧ LocallyIntegrable g (volume : Measure E) ∧
    ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) = -∫ x, g x * ψ x ∂(volume : Measure E)

/-- Weak derivatives are unique almost everywhere. -/
theorem HasWeakDerivAlong.ae_eq {f g₁ g₂ : E → ℝ} {v : E} (h₁ : HasWeakDerivAlong f g₁ v)
    (h₂ : HasWeakDerivAlong f g₂ v) : g₁ =ᵐ[(volume : Measure E)] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq h₁.2.1 h₂.2.1
  intro ψ hψ hψc
  have hψ' : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have e₁ := h₁.2.2 ψ hψ' hψc
  have e₂ := h₂.2.2 ψ hψ' hψc
  have e : (∫ x, g₁ x * ψ x ∂(volume : Measure E)) =
      ∫ x, g₂ x * ψ x ∂(volume : Measure E) := by
    linarith
  simpa only [smul_eq_mul, mul_comm] using e

/-- A `C¹` function with locally integrable derivative has its classical directional derivative as
weak derivative. -/
theorem hasWeakDerivAlong_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) :
    HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v := by
  refine ⟨hf.continuous.locallyIntegrable, ?_, ?_⟩
  · exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).locallyIntegrable
  · intro ψ hψ hψc
    have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
      change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
      exact (hψc.fderiv ℝ).comp_left (by simp)
    have hf'g : Integrable (fun x => fderiv ℝ f x v * ψ x) (volume : Measure E) := by
      exact
        ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous
          |>.integrable_of_hasCompactSupport hψc.mul_left
    have hfg' : Integrable (fun x => f x * fderiv ℝ ψ x v) (volume : Measure E) := by
      exact (hf.continuous.mul hψd).integrable_of_hasCompactSupport hψdc.mul_left
    have hfg : Integrable (fun x => f x * ψ x) (volume : Measure E) := by
      have hfg₀ : Integrable (fun x => ψ x * f x) (volume : Measure E) :=
        hf.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          hψ.continuous hψc
      convert hfg₀ using 1
      funext x
      exact mul_comm _ _
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
      (fun x _ => (hf.differentiable (by simp)).differentiableAt)
      (fun x _ => (hψ.differentiable (by simp)).differentiableAt)

/-- A Lipschitz function has its almost-everywhere (Rademacher) derivative as weak derivative. -/
theorem hasWeakDerivAlong_of_lipschitz {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v : E) :
    HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v := by
  have hline : LocallyIntegrable (fun x => lineDeriv ℝ f x v) (volume : Measure E) :=
    hf.locallyIntegrable_lineDeriv v
  have hdiff : ∀ᵐ x : E ∂(volume : Measure E), DifferentiableAt ℝ f x :=
    hf.ae_differentiableAt
  have hae : (fun x => lineDeriv ℝ f x v) =ᵐ[(volume : Measure E)]
      (fun x => fderiv ℝ f x v) := by
    filter_upwards [hdiff] with x hx
    exact hx.lineDeriv_eq_fderiv
  refine ⟨hf.continuous.locallyIntegrable, hline.congr hae, ?_⟩
  intro ψ hψ hψc
  obtain ⟨D, hψlip⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ (by simp)
  have hleft : (fun x => fderiv ℝ f x v * ψ x) =ᵐ[(volume : Measure E)]
      (fun x => lineDeriv ℝ f x v * ψ x) := by
    filter_upwards [hae] with x hx
    rw [hx]
  have hlineeq :
      (∫ x, lineDeriv ℝ f x v * ψ x ∂(volume : Measure E)) =
        -(∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) := by
    calc
      ∫ x, lineDeriv ℝ f x v * ψ x ∂(volume : Measure E) =
          ∫ x, lineDeriv ℝ ψ x (-v) * f x ∂(volume : Measure E) :=
        hf.integral_lineDeriv_mul_eq hψlip hψc v
      _ = ∫ x, -(f x * fderiv ℝ ψ x v) ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hx : DifferentiableAt ℝ ψ x :=
          (hψ.differentiable (by simp)).differentiableAt
        rw [hx.lineDeriv_eq_fderiv]
        simp [mul_comm]
      _ = -(∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) :=
        integral_neg _
  calc
    ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) =
        -(∫ x, lineDeriv ℝ f x v * ψ x ∂(volume : Measure E)) := by
      linarith [hlineeq]
    _ = -(∫ x, fderiv ℝ f x v * ψ x ∂(volume : Measure E)) := by
      rw [integral_congr_ae hleft]

/-- Product rule with a `C¹` multiplier of compact support. -/
theorem HasWeakDerivAlong.mul_contDiff {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v)
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    HasWeakDerivAlong (fun x => χ x * f x) (fun x => χ x * g x + fderiv ℝ χ x v * f x) v := by
  have hχd : Continuous (fun x => fderiv ℝ χ x v) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχdc : HasCompactSupport (fun x => fderiv ℝ χ x v) := by
    change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ χ)
    exact (hχc.fderiv ℝ).comp_left (by simp)
  have hχf : LocallyIntegrable (fun x => χ x * f x) (volume : Measure E) := by
    simpa [mul_comm] using h.1.continuous_mul hχ.continuous
  have hχg : LocallyIntegrable (fun x => χ x * g x) (volume : Measure E) := by
    simpa [mul_comm] using h.2.1.continuous_mul hχ.continuous
  have hχdf : LocallyIntegrable (fun x => fderiv ℝ χ x v * f x)
      (volume : Measure E) := by
    simpa [mul_comm] using h.1.continuous_mul hχd
  refine ⟨hχf, hχg.add hχdf, ?_⟩
  intro ψ hψ hψc
  have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
    change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
    exact (hψc.fderiv ℝ).comp_left (by simp)
  have iA : Integrable
      (fun x => (χ x * f x) * fderiv ℝ ψ x v) (volume : Measure E) := by
    have hi := hχf.integrable_smul_left_of_hasCompactSupport hψd hψdc
    convert hi using 1
    funext x
    ring
  have iB : Integrable
      (fun x => (f x * ψ x) * fderiv ℝ χ x v) (volume : Measure E) := by
    have hi := h.1.continuous_mul hψ.continuous
      |>.integrable_smul_left_of_hasCompactSupport hχd hχdc
    convert hi using 1
    funext x
    ring
  have iC : Integrable
      (fun x => (χ x * g x) * ψ x) (volume : Measure E) := by
    have hi := hχg.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    convert hi using 1
    funext x
    ring
  have iD : Integrable
      (fun x => (fderiv ℝ χ x v * f x) * ψ x) (volume : Measure E) := by
    have hi := hχdf.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    convert hi using 1
    funext x
    ring
  have hderiv : ∀ x,
      fderiv ℝ (fun y => χ y * ψ y) x v =
        χ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ χ x v := by
    intro x
    change (fderiv ℝ (χ * ψ) x) v =
      χ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ χ x v
    rw [fderiv_mul
      ((hχ.differentiable (by simp)).differentiableAt)
      ((hψ.differentiable (by simp)).differentiableAt)]
    simp [smul_eq_mul]
  have hsum :
      (∫ x, (χ x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E)) +
          (∫ x, (f x * ψ x) * fderiv ℝ χ x v ∂(volume : Measure E)) =
        -(∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) := by
    calc
      (∫ x, (χ x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E)) +
            (∫ x, (f x * ψ x) * fderiv ℝ χ x v ∂(volume : Measure E)) =
          ∫ x, ((χ x * f x) * fderiv ℝ ψ x v +
            (f x * ψ x) * fderiv ℝ χ x v) ∂(volume : Measure E) :=
        (integral_add iA iB).symm
      _ = ∫ x, f x * fderiv ℝ (fun y => χ y * ψ y) x v ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hderiv x]
        ring
      _ = -∫ x, g x * (χ x * ψ x) ∂(volume : Measure E) :=
        h.2.2 (fun x => χ x * ψ x) (hχ.mul hψ) hχc.mul_right
      _ = -(∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with x
        ring
  have hBD :
      (∫ x, (f x * ψ x) * fderiv ℝ χ x v ∂(volume : Measure E)) =
        ∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hCD :
      (∫ x, (χ x * g x + fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E)) =
        (∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) +
          (∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E)) := by
    calc
      ∫ x, (χ x * g x + fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) =
          ∫ x, ((χ x * g x) * ψ x + (fderiv ℝ χ x v * f x) * ψ x) ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) +
          (∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E)) :=
        integral_add iC iD
  calc
    ∫ x, (χ x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E) =
        -(∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) -
          ∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) := by
      linarith [hsum, hBD]
    _ = -∫ x, (χ x * g x + fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) := by
      rw [hCD]
      ring

end FunctionalInequalities.Analysis

section LW3B1WeakDerivativeMollification

open MeasureTheory Set Filter
open scoped Topology Convolution

/-! Mollification commutes with weak directional derivatives (task L-W3b1). -/

namespace FunctionalInequalities.Analysis

/-- **Mollification commutes with weak derivatives** (weak Letwin route, task W3b1, generic): if `g` is the weak derivative
of `f` along `v`, then `φ.normed ⋆ f` is smooth with `∂ᵥ(φ.normed ⋆ f) = φ.normed ⋆ g`. -/
theorem fderiv_convolution_eq_of_hasWeakDerivAlong {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v) (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (convolution (φ.normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v =
      convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  let ρ : E → ℝ := φ.normed volume
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hρ : ContDiff ℝ 1 ρ := φ.contDiff_normed (n := 1)
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  let ψ : E → ℝ := fun y => ρ (x - y)
  have hψ : ContDiff ℝ 1 ψ :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hψd (y : E) :
      fderiv ℝ ψ y v = -(fderiv ℝ ρ (x - y) v) := by
    have hd := ((hρ.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
    have he := congrArg (fun A : E →L[ℝ] ℝ => A v) hd.fderiv
    simpa only [ψ, Function.comp_def, ContinuousLinearMap.comp_apply,
      neg_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.map_neg] using he
  have hw := h.2.2 ψ hψ hψc
  simp_rw [hψd, mul_neg] at hw
  rw [integral_neg] at hw
  have hi :
      (∫ y, f y * fderiv ℝ ρ (x - y) v ∂(volume : Measure E)) =
        ∫ y, g y * ρ (x - y) ∂(volume : Measure E) :=
    neg_injective hw
  have hint :
      Integrable
        (fun y => (ContinuousLinearMap.precompL E L)
          (fderiv ℝ ρ (x - y)) (f y))
        (volume : Measure E) :=
    ((hρc.fderiv ℝ).convolutionExists_left
      (ContinuousLinearMap.precompL E L)
      (hρ.continuous_fderiv one_ne_zero) h.1 x).integrable_swap
  have hconv :
      fderiv ℝ (convolution ρ f L volume) x v =
        ∫ y, fderiv ℝ ρ (x - y) v * f y ∂(volume : Measure E) := by
    rw [(hρc.hasFDerivAt_convolution_left L hρ h.1 x).fderiv]
    rw [convolution_eq_swap (ContinuousLinearMap.precompL E L)]
    rw [ContinuousLinearMap.integral_apply hint]
    rfl
  change fderiv ℝ (convolution ρ f L volume) x v =
    convolution ρ g L volume x
  calc
    fderiv ℝ (convolution ρ f L volume) x v =
        ∫ y, fderiv ℝ ρ (x - y) v * f y ∂(volume : Measure E) := hconv
    _ = ∫ y, f y * fderiv ℝ ρ (x - y) v ∂(volume : Measure E) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => mul_comm _ _
    _ = ∫ y, g y * ρ (x - y) ∂(volume : Measure E) := hi
    _ = convolution ρ g L volume x := by
      rw [convolution_eq_swap L]
      apply integral_congr_ae
      refine Eventually.of_forall fun y => ?_
      change g y * ρ (x - y) = ρ (x - y) * g y
      exact mul_comm _ _

end FunctionalInequalities.Analysis

end LW3B1WeakDerivativeMollification

section LN11C1WeakDerivativeOfDifferenceBound

open MeasureTheory Set Filter
open scoped Topology

/-! Uniform `L²` bounds on difference quotients give a weak derivative in `L²` (task L-N11c1). -/

namespace FunctionalInequalities.Analysis

private lemma l2_pairing_toLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (A : Lp ℝ 2 μ) {b : X → ℝ} (hb : MemLp b 2 μ) :
    inner ℝ A (hb.toLp b) = ∫ x, A x * b x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toLp] with x hx
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx]
  exact mul_comm _ _

private lemma l2_toLp_norm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a : X → ℝ} (ha : MemLp a 2 μ) :
    ‖ha.toLp a‖ ^ 2 = ∫ x, a x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, l2_pairing_toLp]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp] with x hx
  rw [hx, pow_two]

private lemma translated_memLp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (w : E) :
    MemLp (fun x => f (x - w)) 2 (volume : Measure E) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    hf.comp_measurePreserving (measurePreserving_add_right volume (-w))

private lemma quotient_pairing_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (v : E)
    {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    Tendsto
      (fun t : ℝ => ∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x)
      (𝓝[≠] 0) (𝓝 (∫ x, f x * fderiv ℝ ψ x v)) := by
  let F : ℝ → ℝ := fun t =>
    convolution (fun y => f (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume (t • v)
  have hi : LocallyIntegrable (fun y => f (-y)) (volume : Measure E) :=
    (hf.comp_measurePreserving (Measure.measurePreserving_neg volume)).locallyIntegrable
      (by norm_num)
  have hF (t : ℝ) : F t = ∫ x, f (x - t • v) * ψ x := by
    have h := integral_sub_left_eq_self
      (fun y => f (-y) * ψ (t • v - y)) (volume : Measure E) (t • v)
    simpa only [F, convolution_def, ContinuousLinearMap.mul_apply',
      neg_sub, sub_sub_cancel] using h.symm
  have hd : HasDerivAt F (∫ x, f x * fderiv ℝ ψ x v) 0 := by
    have h :=
      (hψc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
        hi hψ (0 • v)).comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simp only [one_smul, zero_smul] at h
    apply h.congr_deriv
    calc
      _ = convolution (fun y => f (-y)) (fun x => fderiv ℝ ψ x v)
          (ContinuousLinearMap.mul ℝ ℝ) volume 0 :=
        convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hi
          (hψc.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) 0 v
      _ = ∫ x, f x * fderiv ℝ ψ x v := by
        simpa only [convolution_def, ContinuousLinearMap.mul_apply', zero_sub] using
          integral_neg_eq_self (fun x => f x * fderiv ℝ ψ x v) volume
  have hp : MemLp ψ 2 (volume : Measure E) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have heq (t : ℝ) :
      (∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x) =
        t⁻¹ * (F t - F 0) := by
    have i₁ : Integrable (fun x => f (x - t • v) * ψ x)
        (volume : Measure E) :=
      (translated_memLp hf (t • v)).integrable_mul hp
    have i₀ : Integrable (fun x => f x * ψ x) (volume : Measure E) :=
      hf.integrable_mul hp
    rw [hF t, hF 0]
    simp only [zero_smul, sub_zero]
    calc
      _ = ∫ x, t⁻¹ * (f (x - t • v) * ψ x - f x * ψ x) := by
        apply integral_congr_ae
        exact .of_forall (fun x => by ring)
      _ = _ := by
        rw [integral_const_mul, integral_sub i₁ i₀]
  have ht := hd.tendsto_slope_zero
  simp only [zero_add, smul_eq_mul] at ht
  exact ht.congr' (.of_forall fun t => (heq t).symm)

/-- **Difference-quotient criterion for a weak derivative in `L²`** (Nirenberg; Evans PDE §5.8.2 Thm 3(ii); weak Letwin
route, N11, task N11c1): if `f ∈ L²` and `∫ (f(x + t v) − f(x))² ≤ C t²` for all small `t ≠ 0`, then `f` has a weak
derivative along `v` that lies in `L²`. -/
theorem exists_hasWeakDerivAlong_of_sq_difference_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E)) (v : E) {C : ℝ}
    (hdiff : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      ∫ x, (f (x + t • v) - f x) ^ 2 ∂(volume : Measure E) ≤ C * t ^ 2) :
    ∃ g : E → ℝ, HasWeakDerivAlong f g v ∧ MemLp g 2 (volume : Measure E) := by
  have hC : 0 ≤ C := by
    have h := hdiff 1 one_ne_zero (by norm_num)
    have hn : 0 ≤ ∫ x, (f (x + (1 : ℝ) • v) - f x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    norm_num only [one_pow, mul_one] at h
    exact hn.trans h
  let Q : ℝ → E → ℝ := fun t x => t⁻¹ * (f (x - t • v) - f x)
  have hQ (t : ℝ) : MemLp (Q t) 2 (volume : Measure E) :=
    ((translated_memLp hf (t • v)).sub hf).const_mul t⁻¹
  let A : ℝ → Lp ℝ 2 (volume : Measure E) := fun t => (hQ t).toLp (Q t)
  have hbound (t : ℝ) (ht : t ≠ 0) (ht1 : |t| ≤ 1) :
      ‖A t‖ ≤ Real.sqrt C := by
    apply (Real.le_sqrt (norm_nonneg _) hC).2
    have hdiff' :
        (∫ x, (f (x - t • v) - f x) ^ 2) ≤ C * t ^ 2 := by
      simpa only [neg_smul, sub_eq_add_neg, neg_sq] using
        hdiff (-t) (neg_ne_zero.mpr ht) (by simpa only [abs_neg] using ht1)
    calc
      ‖A t‖ ^ 2 = ∫ x, (Q t x) ^ 2 := l2_toLp_norm_sq (hQ t)
      _ = t⁻¹ ^ 2 * ∫ x, (f (x - t • v) - f x) ^ 2 := by
        simp only [Q, mul_pow, integral_const_mul]
      _ ≤ t⁻¹ ^ 2 * (C * t ^ 2) :=
        mul_le_mul_of_nonneg_left hdiff' (sq_nonneg _)
      _ = C := by field_simp
  let W : ℝ → WeakDual ℝ (Lp ℝ 2 (volume : Measure E)) := fun t =>
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E)) (A t)).toWeakDual
  have hevent :
      ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        W t ∈ WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ (Lp ℝ 2 (volume : Measure E)))
            (Real.sqrt C) := by
    filter_upwards [eventually_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)]
      with t ht ht1
    have ht0 : t ≠ 0 := ht
    have ht2 : |t| ≤ 1 := by
      exact (show |t| < 1 from by
        simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht1).le
    change dist (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E)) (A t)) 0
      ≤ Real.sqrt C
    simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hbound t ht0 ht2
  obtain ⟨L, _, hL⟩ :=
    (WeakDual.isCompact_closedBall
      (0 : StrongDual ℝ (Lp ℝ 2 (volume : Measure E))) (Real.sqrt C)).exists_mapClusterPt
      (u := W) (f := 𝓝[≠] (0 : ℝ)) (le_principal_iff.mpr hevent)
  let G : Lp ℝ 2 (volume : Measure E) :=
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E))).symm L.toStrongDual
  have hg : MemLp (fun x => -(G x)) 2 (volume : Measure E) := (Lp.memLp G).neg
  refine ⟨fun x => -(G x), ⟨hf.locallyIntegrable (by norm_num),
    hg.locallyIntegrable (by norm_num), ?_⟩, hg⟩
  intro ψ hψ hψc
  have hp : MemLp ψ 2 (volume : Measure E) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  let P : Lp ℝ 2 (volume : Measure E) := hp.toLp ψ
  have heq (t : ℝ) : W t P = ∫ x, Q t x * ψ x := by
    change inner ℝ (A t) P = _
    rw [l2_pairing_toLp]
    apply integral_congr_ae
    filter_upwards [(hQ t).coeFn_toLp] with x hx
    rw [hx]
  have ht : Tendsto (fun t => W t P) (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ x, f x * fderiv ℝ ψ x v)) := by
    exact (quotient_pairing_tendsto hf v hψ hψc).congr'
      (.of_forall fun t => (heq t).symm)
  have hc : MapClusterPt (L P) (𝓝[≠] (0 : ℝ)) (fun t => W t P) :=
    MapClusterPt.continuousAt_comp (WeakDual.eval_continuous P).continuousAt hL
  have hvalue : L P = ∫ x, f x * fderiv ℝ ψ x v :=
    eq_of_nhds_neBot (hc.clusterPt.mono ht).neBot
  have hrepr : (∫ x, G x * ψ x) = L P := by
    rw [← l2_pairing_toLp G hp]
    exact InnerProductSpace.toDual_symm_apply
  calc
    (∫ x, f x * fderiv ℝ ψ x v) = ∫ x, G x * ψ x :=
      hvalue.symm.trans hrepr.symm
    _ = -(∫ x, (-(G x)) * ψ x) := by
      simp only [neg_mul, integral_neg, neg_neg]

end FunctionalInequalities.Analysis

end LN11C1WeakDerivativeOfDifferenceBound

section LN11C2WeakDerivativeGluing

open MeasureTheory Set Filter Metric
open scoped Topology

/-! Gluing local weak derivatives along cutoffs into a global one (task L-N11c2). -/

namespace FunctionalInequalities.Analysis

/-- **Gluing local weak derivatives** (weak Letwin route, N11, task N11c2, generic): if for every `C¹` cutoff `χ` with
compact support the product `χ f` has a weak derivative along `v` that is locally `L²`, then `f` itself has a weak
derivative along `v` that is `L²` on every compact set. -/
theorem exists_hasWeakDerivAlong_of_forall_cutoff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ∀ S : Set E, IsCompact S → MemLp f 2 ((volume : Measure E).restrict S)) (v : E)
    (hloc : ∀ χ : E → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
      ∃ g : E → ℝ, HasWeakDerivAlong (fun x => χ x * f x) g v ∧ MemLp g 2 (volume : Measure E)) :
    ∃ g : E → ℝ, HasWeakDerivAlong f g v ∧
      ∀ S : Set E, IsCompact S → MemLp g 2 ((volume : Measure E).restrict S) := by
  classical
  have compact_bound : ∀ S : Set E, IsCompact S →
      ∃ n : ℕ, ∀ x ∈ S, ‖x‖ < (n : ℝ) + 1 := by
    intro S hS
    obtain ⟨r, hr⟩ := hS.isBounded.subset_ball (0 : E)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨n, ?_⟩
    intro x hx
    have hxr : ‖x‖ < r := by
      simpa only [mem_ball, dist_zero_right] using hr hx
    exact hxr.trans (hn.trans (lt_add_one _))
  have local_integrability : ∀ u : E → ℝ,
      (∀ S : Set E, IsCompact S → MemLp u 2 ((volume : Measure E).restrict S)) →
      LocallyIntegrable u (volume : Measure E) := by
    intro u hu
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure ((volume : Measure E).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hu S hS).integrable (by norm_num)
  let χ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  have hχ_one : ∀ (n : ℕ) (x : E), ‖x‖ < (n : ℝ) + 1 → χ n x = 1 := by
    intro n x hx
    apply (χ n).one_of_mem_closedBall
    change dist x 0 ≤ (n : ℝ) + 1
    rw [dist_zero_right]
    exact hx.le
  have hχ_deriv : ∀ (n : ℕ) (x : E), ‖x‖ < (n : ℝ) + 1 →
      fderiv ℝ (χ n : E → ℝ) x = 0 := by
    intro n x hx
    have he : (χ n : E → ℝ) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      have hxball : x ∈ ball (0 : E) ((n : ℝ) + 1) := by
        simpa only [mem_ball, dist_zero_right] using hx
      filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
      apply hχ_one n y
      simpa only [mem_ball, dist_zero_right] using hy
    exact he.fderiv_eq.trans
      (congrFun (fderiv_const (𝕜 := ℝ) (E := E) (1 : ℝ)) x)
  have hex : ∀ n : ℕ, ∃ G : E → ℝ,
      HasWeakDerivAlong (fun x => χ n x * f x) G v ∧
        MemLp G 2 (volume : Measure E) := by
    intro n
    exact hloc (χ n) (χ n).contDiff (χ n).hasCompactSupport
  choose G hG hGL using hex
  have consistency : ∀ m n : ℕ, ∀ᵐ x ∂(volume : Measure E),
      ‖x‖ < (m : ℝ) + 1 → ‖x‖ < (n : ℝ) + 1 → G m x = G n x := by
    intro m n
    have H := (hG m).mul_contDiff (χ n).contDiff (χ n).hasCompactSupport
    have K := (hG n).mul_contDiff (χ m).contDiff (χ m).hasCompactSupport
    have e : (fun x => χ n x * (χ m x * f x)) =
        (fun x => χ m x * (χ n x * f x)) := by
      funext x
      ring
    rw [e] at H
    have he := H.ae_eq K
    filter_upwards [he] with x hx
    intro hm hn
    simpa only [hχ_one m x hm, hχ_one n x hn,
      hχ_deriv m x hm, hχ_deriv n x hn,
      zero_apply, one_mul, zero_mul, add_zero] using hx
  let g : E → ℝ := fun x => G ⌈‖x‖⌉₊ x
  have agreement : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure E),
      ‖x‖ < (n : ℝ) + 1 → g x = G n x := by
    have hall : ∀ᵐ x ∂(volume : Measure E), ∀ m n : ℕ,
        ‖x‖ < (m : ℝ) + 1 → ‖x‖ < (n : ℝ) + 1 → G m x = G n x :=
      ae_all_iff.mpr (fun m => ae_all_iff.mpr (consistency m))
    intro n
    filter_upwards [hall] with x hx
    intro hxn
    exact hx ⌈‖x‖⌉₊ n
      (lt_of_le_of_lt (Nat.le_ceil ‖x‖) (lt_add_one _)) hxn
  have hgL : ∀ S : Set E, IsCompact S →
      MemLp g 2 ((volume : Measure E).restrict S) := by
    intro S hS
    obtain ⟨n, hn⟩ := compact_bound S hS
    have he : g =ᵐ[(volume : Measure E).restrict S] G n := by
      apply (ae_restrict_iff' hS.measurableSet).mpr
      filter_upwards [agreement n] with x hx
      exact fun hxS => hx (hn x hxS)
    exact (memLp_congr_ae he).mpr ((hGL n).restrict S)
  refine ⟨g, ⟨local_integrability f hf, local_integrability g hgL, ?_⟩, hgL⟩
  intro ψ hψ hψc
  obtain ⟨n, hn⟩ := compact_bound (tsupport ψ) hψc.isCompact
  have hleft : (fun x => f x * fderiv ℝ ψ x v) =
      (fun x => (χ n x * f x) * fderiv ℝ ψ x v) := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · rw [hχ_one n x (hn x hx), one_mul]
    · have hz : fderiv ℝ ψ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
      simp only [hz, zero_apply, mul_zero]
  have hright : (fun x => G n x * ψ x) =ᵐ[(volume : Measure E)]
      (fun x => g x * ψ x) := by
    filter_upwards [agreement n] with x hx
    by_cases hs : x ∈ tsupport ψ
    · rw [hx (hn x hs)]
    · rw [image_eq_zero_of_notMem_tsupport hs, mul_zero, mul_zero]
  calc
    (∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, (χ n x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E) :=
      congrArg (fun u : E → ℝ => ∫ x, u x ∂(volume : Measure E)) hleft
    _ = -∫ x, G n x * ψ x ∂(volume : Measure E) :=
      (hG n).2.2 ψ hψ hψc
    _ = -∫ x, g x * ψ x ∂(volume : Measure E) :=
      congrArg Neg.neg (integral_congr_ae hright)

end FunctionalInequalities.Analysis

end LN11C2WeakDerivativeGluing


section WeakProducts

open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology

namespace FunctionalInequalities.Analysis


private lemma tendsto_integral_mul_of_l2
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → ℝ} {u : ℕ → X → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hu : ∀ m, MemLp (u m) 2 μ)
    (hconv : Tendsto (fun m => eLpNorm (u m - b) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, a x * u m x ∂μ) atTop
      (𝓝 (∫ x, a x * b x ∂μ)) := by
  have hp {z : X → ℝ} (hz : MemLp z 2 μ) :
      inner ℝ (ha.toLp a) (hz.toLp z) = ∫ x, a x * z x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hz.coeFn_toLp] with x hx hz'
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, hz']
    exact mul_comm _ _
  have ht :
      Tendsto (fun m => (hu m).toLp (u m)) atTop (𝓝 (hb.toLp b)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu b hb).2 hconv
  have hi :
      Tendsto (fun m => inner ℝ (ha.toLp a) ((hu m).toLp (u m)))
        atTop (𝓝 (inner ℝ (ha.toLp a) (hb.toLp b))) :=
    tendsto_const_nhds.inner ht
  simpa only [hp] using hi

set_option maxHeartbeats 800000 in
/-- Scalar weak product rule: global L2 factors and directional derivatives
produce a locally integrable product and its actual weak derivative. -/
theorem HasWeakDerivAlong.mul_of_memLp_two {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : MemLp df 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg2 : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdg2 : MemLp dg 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v := by
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    { rIn := (1 / ((m : ℝ) + 1)) / 2
      rOut := 1 / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hr : 0 < 1 / ((m : ℝ) + 1) := by positivity
        linarith }
  have hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    change Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let gm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  let dgm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] dg
  have hgm2 (m : ℕ) :
      MemLp (gm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Mollification.memLp_convolution (φ m) hg2
  have hdgm2 (m : ℕ) :
      MemLp (dgm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Mollification.memLp_convolution (φ m) hdg2
  have hgmconv :
      Tendsto (fun m => eLpNorm (gm m - g) 2 volume) atTop (𝓝 0) :=
    Mollification.tendsto_eLpNorm_convolution_sub hφ hg2
  have hdgmconv :
      Tendsto (fun m => eLpNorm (dgm m - dg) 2 volume) atTop (𝓝 0) :=
    Mollification.tendsto_eLpNorm_convolution_sub hφ hdg2
  have hgmC (m : ℕ) : ContDiff ℝ 1 (gm m) :=
    ((φ m).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((φ m).contDiff_normed (n := 1)) hg.1
  have hgmder (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (gm m) x v = dgm m x :=
    fderiv_convolution_eq_of_hasWeakDerivAlong hg (φ m) x
  refine ⟨(hf2.integrable_mul hg2).locallyIntegrable,
    ((hdf2.integrable_mul hg2).add (hf2.integrable_mul hdg2)).locallyIntegrable, ?_⟩
  intro ψ hψ hψc
  have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
    change HasCompactSupport ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘
      fderiv ℝ ψ)
    exact (hψc.fderiv ℝ).comp_left (by simp)
  have hψtop : MemLp ψ (⊤ : ℝ≥0∞)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hψdtop : MemLp (fun x => fderiv ℝ ψ x v) (⊤ : ℝ≥0∞)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψd.memLp_of_hasCompactSupport hψdc
  let a : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x * fderiv ℝ ψ x v
  let b : EuclideanSpace ℝ (Fin n) → ℝ := fun x => df x * ψ x
  let c : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x * ψ x
  have ha : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψdtop.mul' hf2
  have hb : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψtop.mul' hdf2
  have hc : MemLp c 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψtop.mul' hf2
  have hid (m : ℕ) :
      (∫ x, a x * gm m x) + (∫ x, c x * dgm m x) =
        -(∫ x, b x * gm m x) := by
    have hder (x : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ (fun y => ψ y * gm m y) x v =
          ψ x * dgm m x + gm m x * fderiv ℝ ψ x v := by
      change (fderiv ℝ (ψ * gm m) x) v = _
      rw [fderiv_mul
        ((hψ.differentiable one_ne_zero).differentiableAt)
        (((hgmC m).differentiable one_ne_zero).differentiableAt)]
      simp only [add_apply, smul_apply, smul_eq_mul, hgmder]
    have hw := hf.2.2 (fun x => ψ x * gm m x)
      (hψ.mul (hgmC m)) hψc.mul_right
    calc
      (∫ x, a x * gm m x) + (∫ x, c x * dgm m x) =
          ∫ x, a x * gm m x + c x * dgm m x :=
        (integral_add (ha.integrable_mul (hgm2 m))
          (hc.integrable_mul (hdgm2 m))).symm
      _ = ∫ x, f x * fderiv ℝ (fun y => ψ y * gm m y) x v := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change a x * gm m x + c x * dgm m x =
            f x * fderiv ℝ (fun y => ψ y * gm m y) x v
          rw [hder]
          dsimp only [a, c]
          ring
      _ = -(∫ x, df x * (ψ x * gm m x)) := hw
      _ = -(∫ x, b x * gm m x) := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only [b]
          ring
  have hA := tendsto_integral_mul_of_l2 ha hg2 hgm2 hgmconv
  have hB := tendsto_integral_mul_of_l2 hb hg2 hgm2 hgmconv
  have hC := tendsto_integral_mul_of_l2 hc hdg2 hdgm2 hdgmconv
  have hlim :
      (∫ x, a x * g x) + (∫ x, c x * dg x) =
        -(∫ x, b x * g x) :=
    tendsto_nhds_unique (hA.add hC)
      (Filter.Tendsto.congr (fun m => (hid m).symm) hB.neg)
  have hleft :
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) = ∫ x, a x * g x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [a]
      ring
  have hright :
      (∫ x, (df x * g x + f x * dg x) * ψ x) =
        (∫ x, b x * g x) + (∫ x, c x * dg x) := by
    calc
      (∫ x, (df x * g x + f x * dg x) * ψ x) =
          ∫ x, b x * g x + c x * dg x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only [b, c]
          ring
      _ = (∫ x, b x * g x) + (∫ x, c x * dg x) :=
        integral_add (hb.integrable_mul hg2) (hc.integrable_mul hdg2)
  rw [hleft, hright]
  linarith



private theorem cutoff_memLp {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    MemLp (fun x => χ x * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hKm : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hind : MemLp ((tsupport χ).indicator f) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hKm).mpr (hf (tsupport χ) hχc)
  have hχlp : MemLp χ (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ.memLp_of_hasCompactSupport hχc
  have hm : MemLp (fun x => χ x * ((tsupport χ).indicator f) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := hind.mul' hχlp
  convert hm using 1
  funext x
  by_cases hx : x ∈ tsupport χ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
      zero_mul, zero_mul]

/-- Bounded weak factors with compact-local L2 derivatives have the actual
weak product derivative, which is itself L2 on every compact set. -/
theorem HasWeakDerivAlong.mul_of_locally_memLp_two {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf_top : MemLp f (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg_top : MemLp g (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => df x * g x + f x * dg x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  have hlocal :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => df x * g x + f x * dg x) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    have hfirst : MemLp (fun x => df x * g x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      simpa only [mul_comm] using (hdf2 S hS).mul' (hg_top.restrict S)
    exact hfirst.add ((hdg2 S hS).mul' (hf_top.restrict S))
  have hproduct : MemLp (fun x => f x * g x) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hg_top.mul' hf_top
  have hdensity : LocallyIntegrable (fun x => df x * g x + f x * dg x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hlocal S hS).integrable (by norm_num)
  refine ⟨⟨hproduct.locallyIntegrable le_top, hdensity, ?_⟩, hlocal⟩
  intro ψ hψ hψc
  obtain ⟨R, hR⟩ := hψc.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    { rIn := max R 0 + 1
      rOut := max R 0 + 2
      rIn_pos := by
        have hnonneg := le_max_right R 0
        linarith
      rIn_lt_rOut := by linarith }
  have hχ : ContDiff ℝ 1 (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    χ.contDiff
  have hχc : HasCompactSupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    χ.hasCompactSupport
  have hχon (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ψ) :
      χ x = 1 ∧ fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v = 0 := by
    have hradius : R ≤ χ.rIn := by
      change R ≤ max R 0 + 1
      have hle := le_max_left R 0
      linarith
    have he := χ.eventuallyEq_one_of_mem_ball
      ((ball_subset_ball hradius) (hR hx))
    refine ⟨he.eq_of_nhds, ?_⟩
    simp [he.fderiv_eq]
  have hχ2 : MemLp (χ : EuclideanSpace ℝ (Fin n) → ℝ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ.continuous.memLp_of_hasCompactSupport hχc
  have hχd : Continuous
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hχdc : HasCompactSupport
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) :=
    hχc.fderiv_apply ℝ v
  have hχd2 : MemLp
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχd.memLp_of_hasCompactSupport hχdc
  have hχf2 : MemLp (fun x => χ x * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hf_top.mul' hχ2
  have hχg2 : MemLp (fun x => χ x * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hg_top.mul' hχ2
  have hχdf2 : MemLp
      (fun x => χ x * df x +
        fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (cutoff_memLp hχ.continuous hχc hdf2).add (hf_top.mul' hχd2)
  have hχdg2 : MemLp
      (fun x => χ x * dg x +
        fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (cutoff_memLp hχ.continuous hχc hdg2).add (hg_top.mul' hχd2)
  have hw := (hf.mul_contDiff hχ hχc).mul_of_memLp_two
    (hg.mul_contDiff hχ hχc) hχf2 hχdf2 hχg2 hχdg2
  have hleft :
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (f x * g x) * fderiv ℝ ψ x v =
        ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v
      by_cases hx : x ∈ tsupport ψ
      · rw [(hχon x hx).1]
        simp only [one_mul]
      · rw [fderiv_of_notMem_tsupport ℝ hx]
        simp only [zero_apply, mul_zero]
  have hright :
      (∫ x, ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x) =
        ∫ x, (df x * g x + f x * dg x) * ψ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x =
        (df x * g x + f x * dg x) * ψ x
      by_cases hx : x ∈ tsupport ψ
      · obtain ⟨hone, hzero⟩ := hχon x hx
        rw [hone, hzero]
        simp only [one_mul, zero_mul, add_zero]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp only [mul_zero]
  calc
    (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := hleft
    _ = -(∫ x, ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x) :=
      hw.2.2 ψ hψ hψc
    _ = -(∫ x, (df x * g x + f x * dg x) * ψ x) :=
      congrArg Neg.neg hright


end FunctionalInequalities.Analysis

end WeakProducts


section WeakFinitePolynomials

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/-- Finite real linear combinations preserve the exact directional weak
derivative and its L2 membership on compact sets. -/
theorem hasWeakDerivAlong_finsetSum_mul {n : ℕ} {ι : Type*}
    (s : Finset ι) (c : ι → ℝ)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => ∑ i ∈ s, c i * f i x)
      (fun x => ∑ i ∈ s, c i * df i x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, c i * df i x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  have hcf : ∀ i ∈ s,
      LocallyIntegrable (fun x => c i * f i x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro i hi
    exact (hf i hi).1.smul (c i)
  have hcdf : ∀ i ∈ s,
      LocallyIntegrable (fun x => c i * df i x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro i hi
    exact (hf i hi).2.1.smul (c i)
  refine ⟨?_, ?_⟩
  · refine ⟨locallyIntegrable_finsetSum s hcf,
      locallyIntegrable_finsetSum s hcdf, ?_⟩
    intro ψ hψ hψc
    have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
      exact (hψc.fderiv ℝ).comp_left (by simp)
    have iF : ∀ i ∈ s,
        Integrable (fun x => (c i * f i x) * fderiv ℝ ψ x v)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro i hi
      simpa only [smul_eq_mul, mul_comm] using
        (hcf i hi).integrable_smul_left_of_hasCompactSupport hψd hψdc
    have iG : ∀ i ∈ s,
        Integrable (fun x => (c i * df i x) * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro i hi
      simpa only [smul_eq_mul, mul_comm] using
        (hcdf i hi).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    calc
      (∫ x, (∑ i ∈ s, c i * f i x) * fderiv ℝ ψ x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ i ∈ s, ∫ x, (c i * f i x) * fderiv ℝ ψ x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        simp only [Finset.sum_mul]
        exact integral_finsetSum s iF
      _ = ∑ i ∈ s, -(∫ x, (c i * df i x) * ψ x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mul_assoc, integral_const_mul,
          (hf i hi).2.2 ψ hψ hψc, mul_neg]
      _ = -(∫ x, (∑ i ∈ s, c i * df i x) * ψ x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        symm
        simp only [Finset.sum_mul]
        exact integral_finsetSum s iG
  · intro S hS
    exact memLp_finsetSum s (fun i hi => (hdf2 i hi S hS).const_mul (c i))


/-- Finite bounded weak factors with compact-local L2 directional derivatives
have the Leibniz weak derivative, including the empty product. -/
theorem hasWeakDerivAlong_finsetProd_of_locally_memLp_two {n : ℕ} {ι : Type*}
    [DecidableEq ι] (s : Finset ι)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
    (hbound : ∀ i ∈ s, MemLp (f i) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => ∏ i ∈ s, f i x)
      (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  revert hf hbound hdf2
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _
      simp only [Finset.prod_empty, Finset.sum_empty]
      constructor
      · simpa using
          (hasWeakDerivAlong_of_contDiff
            (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
            contDiff_const v)
      · intro S _
        exact MemLp.zero
  | @insert i t hi ih =>
      intro hf hbound hdf2
      have hrest := ih
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hbound j (Finset.mem_insert_of_mem hj))
        (fun j hj => hdf2 j (Finset.mem_insert_of_mem hj))
      have hrest_top :
          MemLp (fun x => ∏ j ∈ t, f j x) (⊤ : ENNReal)
            (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        simpa only [ENNReal.inv_top, Finset.sum_const_zero, ENNReal.inv_zero] using
          (MemLp.prod' (p := fun _ : ι => (⊤ : ENNReal))
            (fun j hj => hbound j (Finset.mem_insert_of_mem hj)))
      have hbinary :=
        (hf i (Finset.mem_insert_self i t)).mul_of_locally_memLp_two
          hrest.1
          (hbound i (Finset.mem_insert_self i t))
          hrest_top
          (hdf2 i (Finset.mem_insert_self i t))
          hrest.2
      have hprod :
          (fun x => ∏ j ∈ insert i t, f j x) =
            (fun x => f i x * ∏ j ∈ t, f j x) := by
        funext x
        exact Finset.prod_insert hi
      have hsum :
          (fun x => ∑ j ∈ insert i t, df j x * ∏ k ∈ (insert i t).erase j, f k x) =
            (fun x => df i x * (∏ j ∈ t, f j x) +
              f i x * ∑ j ∈ t, df j x * ∏ k ∈ t.erase j, f k x) := by
        funext x
        rw [Finset.sum_insert hi, Finset.erase_insert hi, Finset.mul_sum]
        apply congrArg (fun r : ℝ => df i x * (∏ j ∈ t, f j x) + r)
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := by
          intro h
          subst j
          exact hi hj
        have hiErase : i ∉ t.erase j := by
          intro h
          exact hi (Finset.mem_of_mem_erase h)
        rw [Finset.erase_insert_of_ne hij, Finset.prod_insert hiErase]
        exact mul_left_comm _ _ _
      rw [hprod, hsum]
      exact hbinary


end FunctionalInequalities.Analysis

end WeakFinitePolynomials


universe u

namespace FunctionalInequalities.Analysis

/-- Weak directional derivatives are invariant under almost-everywhere
changes of both the function and its derivative. Local integrability is produced. -/
theorem HasWeakDerivAlong.congr_ae {E : Type u}
    [instNormedAddCommGroup : NormedAddCommGroup E]
    [instInnerProductSpace : InnerProductSpace ℝ E]
    [instFiniteDimensional : FiniteDimensional ℝ E]
    [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
    {f f' g g' : E → ℝ} {v : E}
    (h : HasWeakDerivAlong f g v)
    (hf : f =ᵐ[(volume : Measure E)] f')
    (hg : g =ᵐ[(volume : Measure E)] g') :
    HasWeakDerivAlong f' g' v := by
  refine ⟨h.1.congr hf, h.2.1.congr hg, ?_⟩
  intro ψ hψ hψc
  have ef :
      (∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, f' x * fderiv ℝ ψ x v ∂(volume : Measure E) := by
    apply integral_congr_ae
    exact hf.mono (fun x hx => congrArg (fun r : ℝ => r * fderiv ℝ ψ x v) hx)
  have eg :
      (∫ x, g x * ψ x ∂(volume : Measure E)) =
        ∫ x, g' x * ψ x ∂(volume : Measure E) := by
    apply integral_congr_ae
    exact hg.mono (fun x hx => congrArg (fun r : ℝ => r * ψ x) hx)
  calc
    (∫ x, f' x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) := ef.symm
    _ = -∫ x, g x * ψ x ∂(volume : Measure E) := h.2.2 ψ hψ hψc
    _ = -∫ x, g' x * ψ x ∂(volume : Measure E) :=
      congrArg (fun r : ℝ => -r) eg


end FunctionalInequalities.Analysis

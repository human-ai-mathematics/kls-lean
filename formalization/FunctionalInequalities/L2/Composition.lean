module

public import FunctionalInequalities.L2.BoundedMultiplier
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Scalar composition along differentiable L2 curves

A differentiable Lipschitz scalar function acts differentiably along an
L2 differentiable curve. This does not assert Frechet differentiability of its
composition map on the whole L2 space. Directional quotients are handled by dominated
convergence and perturbations of affine curves by the Lipschitz bound. Bounded tests
also give differentiable quadratic integrals along L2 curves, with the exact mixed
pairing derivative.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace NNReal
namespace FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Dominated pointwise convergence under an L2 envelope gives convergence of
the associated real L2 classes, along any countably generated filter. -/
theorem tendsto_toLp_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → ℝ} {f b : α → ℝ} (hF : ∀ i, MemLp (F i) 2 μ) (hf : MemLp f 2 μ)
    (hb : MemLp b 2 μ) (hFb : ∀ᶠ i in l, ∀ᵐ x ∂μ, |F i x| ≤ b x)
    (hfb : ∀ᵐ x ∂μ, |f x| ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Tendsto (fun i ↦ (hF i).toLp (F i)) l (𝓝 (hf.toLp f)) := by
  have hi := tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ (2 * b x) ^ 2)
    (Eventually.of_forall fun i ↦ ((hF i).aestronglyMeasurable.sub hf.aestronglyMeasurable).pow 2)
    (hFb.mono fun i hi ↦ by
      filter_upwards [hi, hfb] with x hx hy
      simp only [Pi.pow_apply, Pi.sub_apply, Real.norm_eq_abs, abs_sq]
      have h := (abs_sub (F i x) (f x)).trans (add_le_add hx hy)
      calc (F i x - f x) ^ 2 = |F i x - f x| ^ 2 := (sq_abs _).symm
           _ ≤ (2 * b x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2)
    ((hb.const_mul 2).integrable_sq)
    (hlim.mono fun x hx ↦ by simpa using (hx.sub_const (f x)).pow 2)
  have he (i : ι) : ‖(hF i).toLp (F i) - hf.toLp f‖ ^ 2 = ∫ x, (F i x - f x) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hF i).toLp _) (hf.toLp _),
      (hF i).coeFn_toLp, hf.coeFn_toLp] with x hx hy hz
    simp only [hx, Pi.sub_apply, hy, hz, Real.inner_apply, pow_two]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hi' : Tendsto (fun i ↦ ‖(hF i).toLp (F i) - hf.toLp f‖ ^ 2) l (𝓝 0) := by
    simpa only [he, integral_zero, Pi.pow_apply, Pi.sub_apply] using hi
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hi'.sqrt

/-- Differentiation of a Lipschitz scalar composition along an affine L2 curve.
The derivative is specified by its a.e. representative, not by a pointwise choice. -/
theorem hasDerivAt_compLp_affine {Φ : ℝ → ℝ} {C : ℝ≥0} (hΦ : Differentiable ℝ Φ)
    (hL : LipschitzWith C Φ) (h0 : Φ 0 = 0) (u v w : Lp ℝ 2 μ)
    (hw : ∀ᵐ x ∂μ, w x = deriv Φ (u x) * v x) :
    HasDerivAt (fun s : ℝ ↦ hL.compLp h0 (u + s • v)) w 0 := by
  let Q (s : ℝ) (x : α) := s⁻¹ * (Φ (u x + s * v x) - Φ (u x))
  have hQ (s : ℝ) : MemLp (Q s) 2 μ := by
    refine MemLp.ae_eq ?_ (Lp.memLp (s⁻¹ • (hL.compLp h0 (u + s • v) - hL.compLp h0 u)))
    filter_upwards [Lp.coeFn_smul s⁻¹ (hL.compLp h0 (u + s • v) - hL.compLp h0 u),
      Lp.coeFn_sub (hL.compLp h0 (u + s • v)) (hL.compLp h0 u), hL.coeFn_compLp h0 (u + s • v),
      hL.coeFn_compLp h0 u, Lp.coeFn_add u (s • v), Lp.coeFn_smul s v] with x h₁ h₂ h₃ h₄ h₅ h₆
    simp only [h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃, h₄, Function.comp_def, h₅, Pi.add_apply,
      h₆, smul_eq_mul, Q]
  have hQb (s : ℝ) : ∀ᵐ x ∂μ, |Q s x| ≤ C * |v x| := by
    apply ae_of_all
    intro x
    by_cases hs : s = 0
    · simp only [Q, hs, inv_zero, zero_mul, abs_zero]
      positivity
    · have h := hL.norm_sub_le (u x + s * v x) (u x)
      simp only [Real.norm_eq_abs, add_sub_cancel_left, abs_mul] at h
      calc
        |Q s x| = |s|⁻¹ * |Φ (u x + s * v x) - Φ (u x)| := by simp [Q, abs_mul]
        _ ≤ |s|⁻¹ * (C * (|s| * |v x|)) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = C * |v x| := by field_simp
  have hwb : ∀ᵐ x ∂μ, |w x| ≤ C * |v x| := by
    filter_upwards [hw] with x hx
    rw [hx, abs_mul]
    exact
      mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using (norm_deriv_le_of_lipschitz (x₀ := u x) hL))
        (abs_nonneg _)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun s ↦ Q s x) (𝓝[≠] (0 : ℝ)) (𝓝 (w x)) := by
    filter_upwards [hw] with x hx
    have h :=
      ((hΦ (u x + (0 : ℝ) * v x)).hasDerivAt.comp 0
          (((hasDerivAt_id (0 : ℝ)).mul_const (v x)).const_add (u x))).tendsto_slope_zero
    simpa only [zero_add, zero_mul, add_zero, one_mul, smul_eq_mul, Function.comp_def, id_eq, Q,
      hx] using h
  have ht :=
    tendsto_toLp_of_dominated hQ (Lp.memLp w) ((Lp.memLp v).norm.const_mul (C : ℝ))
      (Eventually.of_forall hQb) hwb hlim
  rw [hasDerivAt_iff_tendsto_slope_zero]
  convert ht using 1
  · funext s
    apply Lp.ext
    filter_upwards [(hQ s).coeFn_toLp,
      Lp.coeFn_smul s⁻¹ (hL.compLp h0 (u + s • v) - hL.compLp h0 u),
      Lp.coeFn_sub (hL.compLp h0 (u + s • v)) (hL.compLp h0 u), hL.coeFn_compLp h0 (u + s • v),
      hL.coeFn_compLp h0 u, Lp.coeFn_add u (s • v), Lp.coeFn_smul s v] with x h₀ h₁ h₂ h₃ h₄ h₅
      h₆
    simpa only [zero_add, zero_smul, add_zero, h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃, h₄,
      Function.comp_def, h₅, Pi.add_apply, h₆, smul_eq_mul, Q] using h₀.symm
  · exact congrArg nhds (Lp.ext (Lp.memLp w).coeFn_toLp.symm)

/-- A Lipschitz scalar composition preserves differentiability along L2 curves.
The a.e. derivative formula is sufficient; no differentiable representative of the
curve and no Frechet differentiability of the full composition map are assumed. -/
theorem hasDerivAt_compLp {Φ : ℝ → ℝ} {C : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith C Φ) (h0 : Φ 0 = 0)
    {F : ℝ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ} {t : ℝ} (hF : HasDerivAt F v t)
    (w : Lp ℝ 2 μ) (hw : ∀ᵐ x ∂μ, w x = deriv Φ (F t x) * v x) :
    HasDerivAt (fun s ↦ hL.compLp h0 (F s)) w t := by
  let a (s : ℝ) := F t + (s - t) • v
  have ha : HasDerivAt (fun s ↦ hL.compLp h0 (a s)) w t := by
    have h := hasDerivAt_compLp_affine hΦ hL h0 (F t) v w hw
    have hs : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := (hasDerivAt_id t).sub_const t
    have hh : HasDerivAt (fun s : ℝ ↦ hL.compLp h0 (F t + s • v)) w (t - t) := by
      simpa only [sub_self] using h
    simpa only [one_smul, a, Function.comp_def] using hh.scomp t (h := fun s : ℝ ↦ s - t) hs
  have hf := hasDerivAt_iff_tendsto.mp hF
  have hb := hasDerivAt_iff_tendsto.mp ha
  have hz := (hf.const_mul (C : ℝ)).add hb
  simp only [mul_zero, add_zero] at hz
  rw [hasDerivAt_iff_tendsto]
  refine squeeze_zero (fun s ↦ mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun s ↦ ?_) hz
  have he : hL.compLp h0 (F s) - hL.compLp h0 (F t) - (s - t) • w =
      (hL.compLp h0 (F s) - hL.compLp h0 (a s)) +
      (hL.compLp h0 (a s) - hL.compLp h0 (a t) - (s - t) • w) := by
    simp only [a, sub_self, zero_smul, add_zero]
    abel
  have hn : ‖hL.compLp h0 (F s) - hL.compLp h0 (F t) - (s - t) • w‖ ≤
      C * ‖F s - F t - (s - t) • v‖ +
        ‖hL.compLp h0 (a s) - hL.compLp h0 (a t) - (s - t) • w‖ := by
    rw [he]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    simpa only [a, sub_add_eq_sub_sub] using hL.norm_compLp_sub_le h0 (F s) (a s)
  have h := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (norm_nonneg (s - t)))
  simpa only [mul_add, mul_left_comm] using h

/-- A bounded scalar test gives a continuous quadratic functional on L2. Its
derivative along an L2 curve is the genuine integrable mixed pairing. -/
theorem hasDerivAt_integral_mul_sq {β : α → ℝ} {C : ℝ}
    (hβ : AEStronglyMeasurable β μ) (hC : ∀ᵐ x ∂μ, |β x| ≤ C)
    {F : ℝ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ} {t : ℝ} (hF : HasDerivAt F v t) :
    HasDerivAt (fun s ↦ ∫ x, β x * (F s x) ^ 2 ∂μ)
      (2 * ∫ x, β x * F t x * v x ∂μ) t := by
  let B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := bddSmulL hβ hC
  have hB := (B.hasFDerivAt).comp_hasDerivAt t hF
  have h := hF.inner (𝕜 := ℝ) hB
  have he (s : ℝ) : ⟪F s, B (F s)⟫ = ∫ x, β x * (F s x) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_bddSmulL hβ hC (F s)] with x hx
    simp only [B, hx, Real.inner_apply, smul_eq_mul]
    ring
  have he₁ : ⟪F t, B v⟫ = ∫ x, β x * F t x * v x ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_bddSmulL hβ hC v] with x hx
    simp only [B, hx, Real.inner_apply, smul_eq_mul]
    ring
  have he₂ : ⟪v, B (F t)⟫ = ∫ x, β x * F t x * v x ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_bddSmulL hβ hC (F t)] with x hx
    simp only [B, hx, Real.inner_apply, smul_eq_mul]
    ring
  simp only [Function.comp_def] at h
  rw [show (fun s ↦ ⟪F s, B (F s)⟫) = _ from funext he, he₁, he₂] at h
  exact h.congr_deriv (by ring)

/-- The bounded-test square integral is a continuous functional on real L2. -/
theorem continuous_integral_mul_sq {β : α → ℝ} {C : ℝ}
    (hβ : AEStronglyMeasurable β μ) (hC : ∀ᵐ x ∂μ, |β x| ≤ C) :
    Continuous (fun f : Lp ℝ 2 μ ↦ ∫ x, β x * (f x) ^ 2 ∂μ) := by
  let B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := bddSmulL hβ hC
  have he (f : Lp ℝ 2 μ) : ⟪f, B f⟫ = ∫ x, β x * (f x) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_bddSmulL hβ hC f] with x hx
    simp only [B, hx, Real.inner_apply, smul_eq_mul]
    ring
  simpa only [id_eq, he] using (continuous_id.inner (𝕜 := ℝ) B.continuous)

end FunctionalInequalities.L2

import FunctionalInequalities.Analysis.Semigroup.VonNeumann
import Mathlib.MeasureTheory.Function.L2Space
import FunctionalInequalities.L2.BoundedMultiplier
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The weak carré du champ of square-integrable vector fields

`Gamma.lean` defines the pointwise `Γ(f, g) = ⟪∇f, ∇g⟫` of two classically differentiable
functions. This module defines the **weak** carré du champ

`WeakGamma.apply u v = fun x => ⟪u x, v x⟫`

of two elements `u v : Lp H 2 μ`, which is the object available when the gradient is only a
closed operator on `L²`. The intended use is `u = T̄ f`, `v = T̄ g` for the closed weighted
gradient of `KLS/LogConcave/WeightedGradient/Closure.lean`; nothing in this module refers to a
gradient, so the statements apply verbatim to any pair of square-integrable vector fields.

What is proved:

* legality of the definition: `aestronglyMeasurable`, `integrable` (the pairing of two `L²`
  fields is `L¹`, *not* `L²`), representative independence `ae_eq_of_ae_eq`, `comm`,
  `self_eq_norm_sq`, `self_nonneg` and the Cauchy–Schwarz bound `abs_le_mul`;
* the two integral identities `integral_eq_inner` and `integral_self_eq_norm_sq`, which say that
  the `L¹` integral of the weak `Γ` is the `L²` inner product, so the energy `‖u‖²` is the
  integral of `Γ(u, u)`;
* `integrable_mul`: testing against an a.e. bounded `φ` is legal, and this is exactly the
  hypothesis that makes `∫ φ Γ(f, g) dν` meaningful — no `L²` membership of `Γ` is claimed and
  none is available;
* the `L¹` stability estimates `integral_abs_sub_le` and `abs_integral_mul_sub_le`, with the
  consequence `tendsto_integral_mul`: convergence of the *fields* in `L²` gives convergence of
  the tested weak `Γ` integrals; `tendsto_integral_mul_of_tendsto_multiplier` lets a uniformly
  bounded multiplier converge in `L²` at the same time, and
  `hasDerivWithinAt_integral_mul_apply_self` is the resulting product rule for
  `s ↦ ∫ q s Γ(u s, u s) dμ`, with uniformly bounded difference quotients of `q`. These are the engine for transporting a `Γ`-inequality proved
  on a smaller class to its `L²` closure;
* `integral_eq_integral_mul_adjointComp`: for `f ∈ D(T†T)` and `x ∈ D(T)`,
  `∫ Γ(T f, T x) dμ = ∫ (T†T f) x dμ`. This is the weak integration-by-parts interface in the
  nonnegative-generator convention `A = T†T`, `ℒ = -A`.

## What this is not

No product or chain rule, no `Γ₂`, and no semigroup statement is made here. `Γ(u, v)` is only
`L¹`; applying an `L²` semigroup to it is not meaningful and is not attempted.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u v

namespace WeakGamma

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The **weak carré du champ** of two square-integrable vector fields: the pointwise inner
product of the chosen representatives, `Γ(u, v)(x) = ⟪u x, v x⟫`. -/
def apply (u v : Lp H 2 μ) : α → ℝ := fun x => ⟪u x, v x⟫

theorem apply_def (u v : Lp H 2 μ) (x : α) : apply u v x = ⟪u x, v x⟫ := rfl

theorem comm (u v : Lp H 2 μ) : apply u v = apply v u :=
  funext fun _ => real_inner_comm _ _

theorem aestronglyMeasurable (u v : Lp H 2 μ) : AEStronglyMeasurable (apply u v) μ :=
  (Lp.aestronglyMeasurable u).inner (Lp.aestronglyMeasurable v)

/-- The weak `Γ` of two `L²` fields is integrable. It is **not** claimed to be in `L²`. -/
theorem integrable (u v : Lp H 2 μ) : Integrable (apply u v) μ :=
  L2.integrable_inner u v

/-- Representative independence: the weak `Γ` only depends on the `L²` classes, and it may be
computed from any pair of a.e. representatives. -/
theorem ae_eq_of_ae_eq {u v : Lp H 2 μ} {U V : α → H} (hu : (u : α → H) =ᵐ[μ] U)
    (hv : (v : α → H) =ᵐ[μ] V) : apply u v =ᵐ[μ] fun x => ⟪U x, V x⟫ := by
  filter_upwards [hu, hv] with x hx hy
  rw [apply_def, hx, hy]

theorem self_eq_norm_sq (u : Lp H 2 μ) (x : α) : apply u u x = ‖u x‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

theorem self_nonneg (u : Lp H 2 μ) (x : α) : 0 ≤ apply u u x :=
  real_inner_self_nonneg

theorem abs_le_mul (u v : Lp H 2 μ) (x : α) : |apply u v x| ≤ ‖u x‖ * ‖v x‖ :=
  abs_real_inner_le_norm _ _

/-- For a scalar `L²` class the weak `Γ` with itself is the pointwise square. -/
theorem apply_self_real (u : Lp ℝ 2 μ) (x : α) : apply u u x = (u x) ^ 2 := by
  rw [self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The integral of the weak `Γ` is the `L²` inner product. -/
theorem integral_eq_inner (u v : Lp H 2 μ) : ∫ x, apply u v x ∂μ = ⟪u, v⟫ :=
  (L2.inner_def u v).symm

/-- The energy `‖u‖²` is the integral of `Γ(u, u)`. -/
theorem integral_self_eq_norm_sq (u : Lp H 2 μ) : ∫ x, apply u u x ∂μ = ‖u‖ ^ 2 := by
  rw [integral_eq_inner, real_inner_self_eq_norm_sq]

/-- Testing the weak `Γ` against an a.e. bounded function is legal. -/
theorem integrable_mul {φ : α → ℝ} (hφ : AEStronglyMeasurable φ μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, |φ x| ≤ C) (u v : Lp H 2 μ) :
    Integrable (fun x => φ x * apply u v x) μ :=
  (integrable u v).bdd_mul hφ (by simpa only [Real.norm_eq_abs] using hC)

/-! ### `L¹` stability -/

omit [InnerProductSpace ℝ H] in
/-- The pointwise product of the norms of two `L²` fields is integrable. The two fields may take
values in different normed spaces; this is what lets a scalar `L²` class be paired with a vector
`L²` field. -/
theorem integrable_norm_mul_norm {H' : Type*} [NormedAddCommGroup H'] (u : Lp H 2 μ)
    (v : Lp H' 2 μ) : Integrable (fun x => ‖u x‖ * ‖v x‖) μ := by
  have hu : MemLp (fun x => ‖u x‖) 2 μ := (Lp.memLp u).norm
  have hv : MemLp (fun x => ‖v x‖) 2 μ := (Lp.memLp v).norm
  refine (L2.integrable_inner (𝕜 := ℝ) (hu.toLp _) (hv.toLp _)).congr ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
  rw [hx, hy, Real.inner_apply]

omit [InnerProductSpace ℝ H] in
/-- Cauchy–Schwarz in `L²` for the pointwise norms, for fields with values in two possibly
different normed spaces. -/
theorem integral_norm_mul_norm_le {H' : Type*} [NormedAddCommGroup H'] (u : Lp H 2 μ)
    (v : Lp H' 2 μ) : ∫ x, ‖u x‖ * ‖v x‖ ∂μ ≤ ‖u‖ * ‖v‖ := by
  have hu : MemLp (fun x => ‖u x‖) 2 μ := (Lp.memLp u).norm
  have hv : MemLp (fun x => ‖v x‖) 2 μ := (Lp.memLp v).norm
  have hnu : ‖hu.toLp _‖ = ‖u‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have hnv : ‖hv.toLp _‖ = ‖v‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have hint : ∫ x, ‖u x‖ * ‖v x‖ ∂μ = ⟪hu.toLp _, hv.toLp _⟫ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
    rw [hx, hy, Real.inner_apply]
  rw [hint, ← hnu, ← hnv]
  exact real_inner_le_norm _ _

/-- **`L¹` stability of the weak `Γ`**: the `L¹` distance of two weak carrés du champ is
controlled by the `L²` distances of the fields. -/
theorem integral_abs_sub_le (u u' v v' : Lp H 2 μ) :
    ∫ x, |apply u v x - apply u' v' x| ∂μ ≤ ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ := by
  have hpt : (fun x => |apply u v x - apply u' v' x|)
      ≤ᵐ[μ] fun x => ‖(u - u') x‖ * ‖v x‖ + ‖u' x‖ * ‖(v - v') x‖ := by
    filter_upwards [Lp.coeFn_sub u u', Lp.coeFn_sub v v'] with x hx hy
    have hsplit : apply u v x - apply u' v' x =
        ⟪u x - u' x, v x⟫ + ⟪u' x, v x - v' x⟫ := by
      simp only [apply_def, inner_sub_left, inner_sub_right]
      ring
    have h1 : |⟪u x - u' x, v x⟫| ≤ ‖(u - u') x‖ * ‖v x‖ := by
      rw [hx, Pi.sub_apply]
      exact abs_real_inner_le_norm _ _
    have h2 : |⟪u' x, v x - v' x⟫| ≤ ‖u' x‖ * ‖(v - v') x‖ := by
      rw [hy, Pi.sub_apply]
      exact abs_real_inner_le_norm _ _
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hsum : Integrable (fun x => ‖(u - u') x‖ * ‖v x‖ + ‖u' x‖ * ‖(v - v') x‖) μ :=
    (integrable_norm_mul_norm (u - u') v).add (integrable_norm_mul_norm u' (v - v'))
  calc ∫ x, |apply u v x - apply u' v' x| ∂μ
      ≤ ∫ x, (‖(u - u') x‖ * ‖v x‖ + ‖u' x‖ * ‖(v - v') x‖) ∂μ :=
        integral_mono_ae ((integrable u v).sub (integrable u' v')).abs hsum hpt
    _ = (∫ x, ‖(u - u') x‖ * ‖v x‖ ∂μ) + ∫ x, ‖u' x‖ * ‖(v - v') x‖ ∂μ :=
        integral_add (integrable_norm_mul_norm _ _) (integrable_norm_mul_norm _ _)
    _ ≤ ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ := by
        gcongr <;> exact integral_norm_mul_norm_le _ _

/-- The tested form of `integral_abs_sub_le`, for a nonnegative a.e. bound `C` on `φ`. -/
theorem abs_integral_mul_sub_le {φ : α → ℝ} (hφ : AEStronglyMeasurable φ μ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, |φ x| ≤ C) (u u' v v' : Lp H 2 μ) :
    |(∫ x, φ x * apply u v x ∂μ) - ∫ x, φ x * apply u' v' x ∂μ| ≤
      C * (‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖) := by
  rw [← integral_sub (integrable_mul hφ hC u v) (integrable_mul hφ hC u' v')]
  have hb : ∀ᵐ x ∂μ, |φ x * apply u v x - φ x * apply u' v' x|
      ≤ C * |apply u v x - apply u' v' x| := by
    filter_upwards [hC] with x hx
    rw [← mul_sub, abs_mul]
    gcongr
  calc |∫ x, (φ x * apply u v x - φ x * apply u' v' x) ∂μ|
      ≤ ∫ x, |φ x * apply u v x - φ x * apply u' v' x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C * |apply u v x - apply u' v' x| ∂μ :=
        integral_mono_ae ((integrable_mul hφ hC u v).sub (integrable_mul hφ hC u' v')).abs
          (((integrable u v).sub (integrable u' v')).abs.const_mul C) hb
    _ = C * ∫ x, |apply u v x - apply u' v' x| ∂μ := integral_const_mul _ _
    _ ≤ C * (‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖) := by
        gcongr
        exact integral_abs_sub_le u u' v v'

/-- **Transport of tested weak `Γ` integrals along `L²` convergence of the fields.** This is the
only convergence input a `Γ`-inequality proved on a subclass needs in order to pass to a limit:
both fields must converge in `L²`, and the test function must be a.e. bounded. -/
theorem tendsto_integral_mul {φ : α → ℝ} (hφ : AEStronglyMeasurable φ μ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, |φ x| ≤ C) {u v : ℕ → Lp H 2 μ} {u₀ v₀ : Lp H 2 μ}
    (hu : Tendsto (fun n => ‖u n - u₀‖) atTop (𝓝 0))
    (hv : Tendsto (fun n => ‖v n - v₀‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, φ x * apply (u n) (v n) x ∂μ) atTop
      (𝓝 (∫ x, φ x * apply u₀ v₀ x ∂μ)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbd : ∀ n, dist (∫ x, φ x * apply (u n) (v n) x ∂μ) (∫ x, φ x * apply u₀ v₀ x ∂μ)
      ≤ C * (‖u n - u₀‖ * ‖v n‖ + ‖u₀‖ * ‖v n - v₀‖) := by
    intro n
    rw [Real.dist_eq]
    exact abs_integral_mul_sub_le hφ hC0 hC (u n) u₀ (v n) v₀
  refine squeeze_zero (fun n => dist_nonneg) hbd ?_
  have hvn : Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖v₀‖) :=
    (continuous_norm.tendsto _).comp (tendsto_iff_norm_sub_tendsto_zero.mpr hv)
  have h1 : Tendsto (fun n => ‖u n - u₀‖ * ‖v n‖ + ‖u₀‖ * ‖v n - v₀‖) atTop
      (𝓝 (0 * ‖v₀‖ + ‖u₀‖ * 0)) := (hu.mul hvn).add (tendsto_const_nhds.mul hv)
  simpa using h1.const_mul C

/-- Bounded a.e.-convergent multipliers can vary together with both L2 fields.
No L2 membership of their weak Gamma is required. -/
theorem tendsto_integral_mul_of_ae {φ : ℕ → α → ℝ} {φ₀ : α → ℝ}
    (hφ : ∀ n, AEStronglyMeasurable (φ n) μ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n, ∀ᵐ x ∂μ, |φ n x| ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ φ n x) atTop (𝓝 (φ₀ x)))
    {u v : ℕ → Lp H 2 μ} {u₀ v₀ : Lp H 2 μ}
    (hu : Tendsto (fun n ↦ ‖u n - u₀‖) atTop (𝓝 0))
    (hv : Tendsto (fun n ↦ ‖v n - v₀‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, φ n x * apply (u n) (v n) x ∂μ) atTop
      (𝓝 (∫ x, φ₀ x * apply u₀ v₀ x ∂μ)) := by
  have hfixed : Tendsto (fun n ↦ ∫ x, φ n x * apply u₀ v₀ x ∂μ) atTop
      (𝓝 (∫ x, φ₀ x * apply u₀ v₀ x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ C * |apply u₀ v₀ x|)
      (fun n ↦ (hφ n).mul (aestronglyMeasurable u₀ v₀))
      ((integrable u₀ v₀).abs.const_mul C)
    · intro n
      filter_upwards [hC n] with x hx
      simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
        mul_le_mul_of_nonneg_right hx (abs_nonneg (apply u₀ v₀ x))
    · filter_upwards [hlim] with x hx
      exact hx.mul_const _
  have hvn : Tendsto (fun n ↦ ‖v n‖) atTop (𝓝 ‖v₀‖) :=
    (continuous_norm.tendsto _).comp (tendsto_iff_norm_sub_tendsto_zero.mpr hv)
  have hbound : Tendsto (fun n ↦ C * (‖u n - u₀‖ * ‖v n‖ + ‖u₀‖ * ‖v n - v₀‖))
      atTop (𝓝 0) := by
    simpa using ((hu.mul hvn).add (tendsto_const_nhds.mul hv)).const_mul C
  have hdiff : Tendsto (fun n ↦ (∫ x, φ n x * apply (u n) (v n) x ∂μ) -
      ∫ x, φ n x * apply u₀ v₀ x ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) hbound
    rw [Real.norm_eq_abs]
    exact abs_integral_mul_sub_le (hφ n) hC0 (hC n) (u n) u₀ (v n) v₀
  simpa using hdiff.add hfixed

/-- **Joint convergence of multipliers and fields.** On a finite measure, let the multipliers
`qᵢ → q₀` converge in `L²` with a uniform a.e. bound `D`, and let the fields `uᵢ → u₀`,
`vᵢ → v₀` converge in `L²`, along any filter. Then `∫ qᵢ Γ(uᵢ, vᵢ) dμ → ∫ q₀ Γ(u₀, v₀) dμ`.
The multiplier convergence is only in `L²` while `Γ(u₀, v₀)` is only `L¹`; the uniform bound
is what makes the pairing converge (`L2.tendsto_integral_mul_of_tendsto`). -/
theorem tendsto_integral_mul_of_tendsto_multiplier [IsFiniteMeasure μ] {ι : Type*}
    {l : Filter ι} {q : ι → Lp ℝ 2 μ} {q₀ : Lp ℝ 2 μ} (hq : Tendsto q l (𝓝 q₀)) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ᶠ i in l, ∀ᵐ x ∂μ, |q i x| ≤ D) (hD₀ : ∀ᵐ x ∂μ, |q₀ x| ≤ D)
    {u v : ι → Lp H 2 μ} {u₀ v₀ : Lp H 2 μ} (hu : Tendsto u l (𝓝 u₀))
    (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => ∫ x, q i x * apply (u i) (v i) x ∂μ) l
      (𝓝 (∫ x, q₀ x * apply u₀ v₀ x ∂μ)) := by
  have hB := FunctionalInequalities.L2.tendsto_integral_mul_of_tendsto hq hD hD₀
    (integrable u₀ v₀)
  have hu' := tendsto_iff_norm_sub_tendsto_zero.mp hu
  have hv' := tendsto_iff_norm_sub_tendsto_zero.mp hv
  have hvn : Tendsto (fun i => ‖v i‖) l (𝓝 ‖v₀‖) := (continuous_norm.tendsto _).comp hv
  have hA : Tendsto (fun i => D * (‖u i - u₀‖ * ‖v i‖ + ‖u₀‖ * ‖v i - v₀‖)) l (𝓝 0) := by
    simpa using ((hu'.mul hvn).add (tendsto_const_nhds.mul hv')).const_mul D
  have hdiff : Tendsto (fun i => (∫ x, q i x * apply (u i) (v i) x ∂μ) -
      ∫ x, q i x * apply u₀ v₀ x ∂μ) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hA
    filter_upwards [hD] with i hi
    rw [Real.norm_eq_abs]
    exact abs_integral_mul_sub_le (Lp.aestronglyMeasurable _) hD0 hi (u i) u₀ (v i) v₀
  simpa using hdiff.add hB

/-- **Product rule for a tested weak `Γ`.** On a finite measure, let `s ↦ q s ∈ L²` and
`s ↦ u s ∈ L²(H)` have derivatives `q'` and `u'` at `r` within `S`, with `q r`, `q'` and the
difference quotients of `q` near `r` a.e. bounded by one constant `D`. Then
`s ↦ ∫ q s Γ(u s, u s) dμ` has derivative `∫ q' Γ(u r, u r) dμ + 2 ∫ q r Γ(u r, u') dμ` at `r`
within `S`. The uniform bound on the difference quotients is what lets them converge against
the `L¹` function `Γ(u r, u r)`. -/
theorem hasDerivWithinAt_integral_mul_apply_self [IsFiniteMeasure μ] {q : ℝ → Lp ℝ 2 μ}
    {u : ℝ → Lp H 2 μ} {S : Set ℝ} {r : ℝ} {q' : Lp ℝ 2 μ} {u' : Lp H 2 μ}
    (hq : HasDerivWithinAt q q' S r) (hu : HasDerivWithinAt u u' S r) {D : ℝ} (hD0 : 0 ≤ D)
    (hqb : ∀ᵐ x ∂μ, |q r x| ≤ D)
    (hslope : ∀ᶠ s in 𝓝[S \ {r}] r, ∀ᵐ x ∂μ, |slope q r s x| ≤ D)
    (hq'b : ∀ᵐ x ∂μ, |q' x| ≤ D) :
    HasDerivWithinAt (fun s => ∫ x, q s x * apply (u s) (u s) x ∂μ)
      ((∫ x, q' x * apply (u r) (u r) x ∂μ) + 2 * ∫ x, q r x * apply (u r) u' x ∂μ) S r := by
  have hc : Tendsto u (𝓝[S \ {r}] r) (𝓝 (u r)) :=
    hu.continuousWithinAt.tendsto.mono_left (nhdsWithin_mono _ Set.sdiff_subset)
  rw [hasDerivWithinAt_iff_tendsto_slope] at hq hu ⊢
  have h1 := tendsto_integral_mul_of_tendsto_multiplier hq hD0 hslope hq'b hc hc
  have h2 := tendsto_integral_mul_of_tendsto_multiplier (tendsto_const_nhds (x := q r)) hD0
    (Eventually.of_forall fun _ => hqb) hqb hu hc
  have h3 := tendsto_integral_mul_of_tendsto_multiplier (tendsto_const_nhds (x := q r)) hD0
    (Eventually.of_forall fun _ => hqb) hqb (tendsto_const_nhds (x := u r)) hu
  have hlim : (∫ x, q' x * apply (u r) (u r) x ∂μ) + 2 * ∫ x, q r x * apply (u r) u' x ∂μ =
      (∫ x, q' x * apply (u r) (u r) x ∂μ) + (∫ x, q r x * apply u' (u r) x ∂μ) +
        ∫ x, q r x * apply (u r) u' x ∂μ := by
    rw [comm u' (u r)]; ring
  rw [hlim]
  refine ((h1.add h2).add h3).congr' ?_
  filter_upwards [hslope, self_mem_nhdsWithin] with s hs hsS
  set c := (s - r)⁻¹ with hcdef
  have hsl : ∀ᵐ x ∂μ, slope q r s x = c * (q s x - q r x) := by
    rw [slope_def_module]
    filter_upwards [Lp.coeFn_smul c (q s - q r), Lp.coeFn_sub (q s) (q r)] with x h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, smul_eq_mul]
  have hslu : ∀ᵐ x ∂μ, slope u r s x = c • (u s x - u r x) := by
    rw [slope_def_module]
    filter_upwards [Lp.coeFn_smul c (u s - u r), Lp.coeFn_sub (u s) (u r)] with x h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply]
  have hqs : ∀ᵐ x ∂μ, |q s x| ≤ D + |s - r| * D := by
    filter_upwards [hsl, hs, hqb] with x h1 h2 h3
    have hne : s - r ≠ 0 := sub_ne_zero.mpr hsS.2
    have heq : q s x = q r x + (s - r) * slope q r s x := by
      rw [h1, hcdef]; field_simp; ring
    rw [heq]
    calc |q r x + (s - r) * slope q r s x| ≤ |q r x| + |s - r| * |slope q r s x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ D + |s - r| * D := by gcongr
  have i₀ := integrable_mul (Lp.aestronglyMeasurable (q s)) hqs (u s) (u s)
  have i₀' := integrable_mul (Lp.aestronglyMeasurable (q r)) hqb (u r) (u r)
  have i₁ := integrable_mul (Lp.aestronglyMeasurable (slope q r s)) hs (u s) (u s)
  have i₂ := integrable_mul (Lp.aestronglyMeasurable (q r)) hqb (slope u r s) (u s)
  have i₃ := integrable_mul (Lp.aestronglyMeasurable (q r)) hqb (u r) (slope u r s)
  simp only [slope_def_field]
  rw [div_eq_inv_mul, ← hcdef, ← integral_sub i₀ i₀', ← integral_const_mul]
  have hsum : ∫ x, (slope q r s x * apply (u s) (u s) x + q r x * apply (slope u r s) (u s) x +
      q r x * apply (u r) (slope u r s) x) ∂μ =
      (∫ x, slope q r s x * apply (u s) (u s) x ∂μ) +
        (∫ x, q r x * apply (slope u r s) (u s) x ∂μ) +
        ∫ x, q r x * apply (u r) (slope u r s) x ∂μ := by
    have i₁₂ : Integrable (fun x => slope q r s x * apply (u s) (u s) x +
        q r x * apply (slope u r s) (u s) x) μ := i₁.add i₂
    rw [integral_add i₁₂ i₃, integral_add i₁ i₂]
  rw [← hsum]
  refine integral_congr_ae ?_
  filter_upwards [hsl, hslu] with x h1 h2
  simp only [apply_def, h1, h2, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, RCLike.conj_to_real]
  ring

/-! ### Pairing a square-integrable multiplier with an a.e. bounded field -/

/-- Testing `Γ(u, β)` against an `L²` multiplier `a` is legal as soon as the **second field** `β`
is a.e. bounded: then `Γ(u, β)` is itself in `L²`, and the product with `a` is in `L¹`. This is
the pairing that appears when a Leibniz rule moves the gradient of a compactly supported test
function out of a weak `Γ`. -/
theorem integrable_mul_of_bdd_right {β : Lp H 2 μ} {M : ℝ}
    (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) (a : Lp ℝ 2 μ) (u : Lp H 2 μ) :
    Integrable (fun x => a x * apply u β x) μ := by
  refine Integrable.mono' ((integrable_norm_mul_norm a u).const_mul M)
    ((Lp.aestronglyMeasurable a).mul (aestronglyMeasurable u β)) ?_
  filter_upwards [hM] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  calc |a x| * |apply u β x| ≤ |a x| * (‖u x‖ * ‖β x‖) := by
        gcongr
        exact abs_le_mul u β x
    _ = (|a x| * ‖u x‖) * ‖β x‖ := by ring
    _ ≤ (|a x| * ‖u x‖) * M := by gcongr
    _ = M * (‖a x‖ * ‖u x‖) := by rw [Real.norm_eq_abs]; ring

/-- **`L¹` stability of `a · Γ(u, β)` for an a.e. bounded field `β`**: the `L²` distances of the
multiplier and of the first field control the difference of the tested integrals. -/
theorem abs_integral_mul_sub_le_of_bdd_right {β : Lp H 2 μ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) (a a' : Lp ℝ 2 μ) (u u' : Lp H 2 μ) :
    |(∫ x, a x * apply u β x ∂μ) - ∫ x, a' x * apply u' β x ∂μ| ≤
      M * (‖a - a'‖ * ‖u‖ + ‖a'‖ * ‖u - u'‖) := by
  rw [← integral_sub (integrable_mul_of_bdd_right hM a u)
    (integrable_mul_of_bdd_right hM a' u')]
  have hb : ∀ᵐ x ∂μ, |a x * apply u β x - a' x * apply u' β x|
      ≤ M * (‖(a - a') x‖ * ‖u x‖ + ‖a' x‖ * ‖(u - u') x‖) := by
    filter_upwards [hM, Lp.coeFn_sub a a', Lp.coeFn_sub u u'] with x hx ha hu
    have hsplit : a x * apply u β x - a' x * apply u' β x =
        (a x - a' x) * apply u β x + a' x * apply (u - u') β x := by
      have : apply (u - u') β x = apply u β x - apply u' β x := by
        simp only [apply_def, hu, Pi.sub_apply, inner_sub_left]
      rw [this]
      ring
    have h1 : |(a x - a' x) * apply u β x| ≤ ‖(a - a') x‖ * ‖u x‖ * M := by
      rw [abs_mul, ha, Pi.sub_apply, Real.norm_eq_abs]
      calc |a x - a' x| * |apply u β x| ≤ |a x - a' x| * (‖u x‖ * ‖β x‖) := by
            gcongr
            exact abs_le_mul u β x
        _ ≤ |a x - a' x| * ‖u x‖ * M := by
            rw [mul_assoc]
            gcongr
    have h2 : |a' x * apply (u - u') β x| ≤ ‖a' x‖ * ‖(u - u') x‖ * M := by
      rw [abs_mul, Real.norm_eq_abs]
      calc |a' x| * |apply (u - u') β x| ≤ |a' x| * (‖(u - u') x‖ * ‖β x‖) := by
            gcongr
            exact abs_le_mul (u - u') β x
        _ ≤ |a' x| * ‖(u - u') x‖ * M := by
            rw [mul_assoc]
            gcongr
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have := add_le_add h1 h2
    nlinarith [this, norm_nonneg ((a - a') x), norm_nonneg (u x), norm_nonneg (a' x),
      norm_nonneg ((u - u') x)]
  have hsum : Integrable (fun x =>
      M * (‖(a - a') x‖ * ‖u x‖ + ‖a' x‖ * ‖(u - u') x‖)) μ :=
    (((integrable_norm_mul_norm (a - a') u).add
      (integrable_norm_mul_norm a' (u - u')))).const_mul M
  calc |∫ x, (a x * apply u β x - a' x * apply u' β x) ∂μ|
      ≤ ∫ x, |a x * apply u β x - a' x * apply u' β x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, M * (‖(a - a') x‖ * ‖u x‖ + ‖a' x‖ * ‖(u - u') x‖) ∂μ :=
        integral_mono_ae ((integrable_mul_of_bdd_right hM a u).sub
          (integrable_mul_of_bdd_right hM a' u')).abs hsum hb
    _ = M * ∫ x, (‖(a - a') x‖ * ‖u x‖ + ‖a' x‖ * ‖(u - u') x‖) ∂μ := integral_const_mul _ _
    _ = M * ((∫ x, ‖(a - a') x‖ * ‖u x‖ ∂μ) + ∫ x, ‖a' x‖ * ‖(u - u') x‖ ∂μ) := by
        rw [integral_add (integrable_norm_mul_norm _ _) (integrable_norm_mul_norm _ _)]
    _ ≤ M * (‖a - a'‖ * ‖u‖ + ‖a'‖ * ‖u - u'‖) := by
        gcongr <;> exact integral_norm_mul_norm_le _ _

/-- **Transport of `∫ a · Γ(u, β)` along `L²` convergence**, for a fixed a.e. bounded field `β`.
Only the multiplier and the first field move, and both move in `L²`. -/
theorem tendsto_integral_mul_of_bdd_right {β : Lp H 2 μ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) {a : ℕ → Lp ℝ 2 μ} {u : ℕ → Lp H 2 μ} {a₀ : Lp ℝ 2 μ}
    {u₀ : Lp H 2 μ} (ha : Tendsto (fun n => ‖a n - a₀‖) atTop (𝓝 0))
    (hu : Tendsto (fun n => ‖u n - u₀‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, a n x * apply (u n) β x ∂μ) atTop
      (𝓝 (∫ x, a₀ x * apply u₀ β x ∂μ)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbd : ∀ n, dist (∫ x, a n x * apply (u n) β x ∂μ) (∫ x, a₀ x * apply u₀ β x ∂μ)
      ≤ M * (‖a n - a₀‖ * ‖u n‖ + ‖a₀‖ * ‖u n - u₀‖) := by
    intro n
    rw [Real.dist_eq]
    exact abs_integral_mul_sub_le_of_bdd_right hM0 hM (a n) a₀ (u n) u₀
  refine squeeze_zero (fun n => dist_nonneg) hbd ?_
  have hun : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖u₀‖) :=
    (continuous_norm.tendsto _).comp (tendsto_iff_norm_sub_tendsto_zero.mpr hu)
  have h1 : Tendsto (fun n => ‖a n - a₀‖ * ‖u n‖ + ‖a₀‖ * ‖u n - u₀‖) atTop
      (𝓝 (0 * ‖u₀‖ + ‖a₀‖ * 0)) := (ha.mul hun).add (tendsto_const_nhds.mul hu)
  simpa using h1.const_mul M

/-! ### The weak `Γ` of a closed operator and its nonnegative generator -/

section Operator

open FunctionalInequalities.Analysis.Semigroup

variable {T : Lp ℝ 2 μ →ₗ.[ℝ] Lp H 2 μ}

/-- **Weak integration by parts in the nonnegative-generator convention.** For `f ∈ D(T†T)` and
`x ∈ D(T)`, `∫ Γ(T f, T x) dμ = ∫ (T†T f) · x dμ`. With `A = T†T` and `ℒ = -A` this is
`∫ Γ(f, x) dμ = ∫ (A f) x dμ = -∫ (ℒ f) x dμ`. Only density of `D(T)` is used. -/
theorem integral_eq_integral_mul_adjointComp (hd : Dense (T.domain : Set (Lp ℝ 2 μ)))
    (f : (adjointComp T).domain) (x : T.domain) :
    ∫ a, apply (T ⟨(f : Lp ℝ 2 μ), f.2.2⟩) (T x) a ∂μ =
      ∫ a, (adjointComp T f : Lp ℝ 2 μ) a * (x : Lp ℝ 2 μ) a ∂μ := by
  rw [integral_eq_inner, ← inner_adjointComp hd f x.2, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => Real.inner_apply _ _)

/-- The Dirichlet form read as an integral of the weak `Γ`: `∫ Γ(T f, T f) dμ = ‖T f‖²`. -/
theorem integral_self_eq_norm_map_sq (f : T.domain) :
    ∫ a, apply (T f) (T f) a ∂μ = ‖T f‖ ^ 2 :=
  integral_self_eq_norm_sq _

end Operator

end WeakGamma

end FunctionalInequalities.Analysis.BakryEmery

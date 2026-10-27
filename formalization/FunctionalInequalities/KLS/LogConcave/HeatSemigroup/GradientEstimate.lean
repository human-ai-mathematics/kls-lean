import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.TestClassExtension
import FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative

/-!
# Time interpolation and the square gradient estimate `Γ(P_t f) ≤ P_t Γ(f)`

Let `ν = m.tilted (-U)` be a full-dimensional log-concave probability law with a smooth convex
potential and unit weight, `T̄` the closed gradient, `A = T̄†T̄` and `P_t = exp (-t A)`. For a
nonnegative `φ ∈ C_c^∞(V)` and data `f`, the interpolation

`Ψ(r) = ∫ (P_{t-r} φ) Γ(T̄ P_r f, T̄ P_r f) dν`

is nonincreasing in `r ∈ (0, t]`. Its right derivative is
`∫ (A P_{t-r} φ) Γ(T̄F, T̄F) dν - 2 ∫ (P_{t-r} φ) Γ(T̄F, T̄AF) dν` with `F = P_r f`, which is
`-2` times the heat-test frontend `integral_weakGamma_operator_nonneg`, hence `≤ 0`.
The consequences are:

* `integral_mul_weakGamma_le_of_pos`: for arbitrary `g ∈ L²(ν)` and `0 < a ≤ t`,
  `∫ φ Γ(T̄P_t g) dν ≤ ∫ (P_{t-a} φ) Γ(T̄P_a g) dν`;
* `integral_mul_weakGamma_le`: for `f ∈ D(T̄)` and `t ≥ 0`,
  `∫ φ Γ(T̄P_t f) dν ≤ ∫ (P_t φ) Γ(T̄f) dν`, the integrated form of `Γ(P_t f) ≤ P_t Γ(f)`.

`Γ(T̄f)` is only `L¹`, so `P_t Γ(f)` is not an `L²` object; the estimate is stated against the
bounded test `P_t φ`, which is its meaning by symmetry of `P_t`.

The analytic inputs are the difference-quotient bound `ae_abs_operator_sub_le`
(`|P_h ψ - ψ| ≤ h D` when `|Aψ| ≤ D`, from Markov contraction), the time derivatives of
`Generated/TimeDerivative.lean`, and the tested product rule
`WeakGamma.hasDerivWithinAt_integral_mul_apply_self`.

Not proved: the `L¹`-type estimate `|T̄P_t f| ≤ P_t |T̄f|`, the reverse
(Bakry–Gentil–Ledoux) estimate, small-time bounds, or any Buser or KLS statement.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section Difference

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- **Difference-quotient bound.** If `ψ ∈ D(A)` and `|Aψ| ≤ D` a.e., then
`|P_h ψ - ψ| ≤ h D` a.e. for every `h ≥ 0`. Testing against the indicator of a set `s`, the
real function `τ ↦ ∫_s (P_τ ψ - ψ) dν` has right derivative `-∫_s P_τ(Aψ) dν`, of absolute
value at most `D ν(s)` by Markov contraction, and vanishes at `τ = 0`. -/
theorem ae_abs_operator_sub_le (ψ : (adjointComp (hν.closedWeightedOperator m B hi)).domain)
    {D : ℝ} (hD : 0 ≤ D)
    (hAψ : ∀ᵐ x ∂(ν : Measure V),
      |(adjointComp (hν.closedWeightedOperator m B hi) ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ D)
    {h : ℝ} (hh : 0 ≤ h) :
    ∀ᵐ x ∂(ν : Measure V),
      |operator m B hν hi hh ψ x - (ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ h * D := by
  revert ψ
  set T := hν.closedWeightedOperator m B hi
  set hT := hν.closedWeightedOperator_isClosed m B hi
  set hd := hν.dense_domain_closedWeightedOperator m B hi
  intro ψ hAψ
  set g : Lp ℝ 2 (ν : Measure V) := operator m B hν hi hh ψ - ψ with hgdef
  have key : ∀ s : Set V, MeasurableSet s →
      |∫ x in s, g x ∂(ν : Measure V)| ≤ h * D * (ν : Measure V).real s := by
    intro s hs
    set χ := indicatorConstLp 2 hs (measure_ne_top (ν : Measure V) s) (1 : ℝ)
    set F : ℝ → ℝ := fun τ => ⟪χ, Generated.apply T hT hd τ (ψ : Lp ℝ 2 (ν : Measure V))⟫
      with hFdef
    have hF' : ∀ τ ∈ Ici (0 : ℝ), HasDerivWithinAt F
        (-⟪χ, Generated.apply T hT hd τ (adjointComp T ψ)⟫) (Ici τ) τ := by
      intro τ hτ
      have hP := Generated.hasDerivWithinAt_apply_Ici T hT hd ψ hτ
      have h' := (innerSL ℝ χ).hasFDerivAt.comp_hasDerivWithinAt τ hP
      rw [Generated.generator_comm T hT hd ψ hτ] at h'
      simpa [F, Function.comp_def, inner_neg_right] using h'
    have hbd : ∀ τ ∈ Ici (0 : ℝ),
        |⟪χ, Generated.apply T hT hd τ (adjointComp T ψ)⟫| ≤ D * (ν : Measure V).real s := by
      intro τ hτ
      rw [L2.inner_indicatorConstLp_one]
      have hb := ae_abs_operator_le m B hν hi hτ (adjointComp T ψ) hD hAψ
      refine (Real.norm_eq_abs _ ▸ norm_setIntegral_le_of_norm_le_const_ae
        (measure_lt_top _ _) ?_)
      exact ae_restrict_of_ae (by
        filter_upwards [hb] with x hx
        rw [Real.norm_eq_abs]; exact hx)
    have hcont : ContinuousOn F (Icc 0 h) :=
      ((innerSL ℝ χ).continuous.comp_continuousOn
        (Generated.continuousOn T hT hd (ψ : Lp ℝ 2 (ν : Measure V)))).mono Icc_subset_Ici_self
    have hB : ContinuousOn (fun τ : ℝ => F 0 + τ * (D * (ν : Measure V).real s)) (Icc 0 h) :=
      (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
    have hB' : ∀ τ ∈ Ico (0 : ℝ) h, HasDerivWithinAt
        (fun τ : ℝ => F 0 + τ * (D * (ν : Measure V).real s)) (D * (ν : Measure V).real s)
        (Ici τ) τ := fun τ _ => by
      simpa using ((hasDerivAt_id τ).mul_const (D * (ν : Measure V).real s)).const_add
        (F 0) |>.hasDerivWithinAt
    have hC : ContinuousOn (fun τ : ℝ => F 0 - τ * (D * (ν : Measure V).real s)) (Icc 0 h) :=
      (continuous_const.sub (continuous_id.mul continuous_const)).continuousOn
    have hC' : ∀ τ ∈ Ico (0 : ℝ) h, HasDerivWithinAt
        (fun τ : ℝ => F 0 - τ * (D * (ν : Measure V).real s)) (-(D * (ν : Measure V).real s))
        (Ici τ) τ := fun τ _ => by
      simpa using ((hasDerivAt_id τ).mul_const (D * (ν : Measure V).real s)).const_sub
        (F 0) |>.hasDerivWithinAt
    have hup := image_le_of_deriv_right_le_deriv_boundary hcont
      (fun τ hτ => hF' τ hτ.1) (le_of_eq (by simp)) hB hB'
      (fun τ hτ => by linarith [(_root_.abs_le.mp (hbd τ hτ.1)).1]) (right_mem_Icc.mpr hh)
    have hneg : ContinuousOn (fun τ => -F τ) (Icc 0 h) := hcont.neg
    have hlow := image_le_of_deriv_right_le_deriv_boundary hneg
      (fun τ hτ => (hF' τ hτ.1).neg) (le_of_eq (by simp)) hC.neg (fun τ hτ => (hC' τ hτ).neg)
      (fun τ hτ => by simp only [neg_neg]; linarith [(_root_.abs_le.mp (hbd τ hτ.1)).2])
      (right_mem_Icc.mpr hh)
    have hFh : ∫ x in s, g x ∂(ν : Measure V) = F h - F 0 := by
      rw [← L2.inner_indicatorConstLp_one hs (measure_ne_top _ s), hgdef, inner_sub_right]
      simp only [F, Generated.zero_time]
      rfl
    simp only [Pi.neg_apply] at hlow
    rw [hFh, _root_.abs_le]
    constructor <;> nlinarith [hup, hlow]
  have hgint : Integrable (fun x => (g : V → ℝ) x) (ν : Measure V) :=
    (Lp.memLp g).integrable one_le_two
  have hup : 0 ≤ᵐ[(ν : Measure V)] fun x => h * D - g x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg ((integrable_const _).sub hgint)
      fun s hs _ => ?_
    rw [integral_sub (integrable_const _).integrableOn hgint.integrableOn, setIntegral_const,
      smul_eq_mul]
    nlinarith [(_root_.abs_le.mp (key s hs)).2]
  have hlow : 0 ≤ᵐ[(ν : Measure V)] fun x => h * D + g x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg ((integrable_const _).add hgint)
      fun s hs _ => ?_
    rw [integral_add (integrable_const _).integrableOn hgint.integrableOn, setIntegral_const,
      smul_eq_mul]
    nlinarith [(_root_.abs_le.mp (key s hs)).1]
  filter_upwards [hup, hlow, Lp.coeFn_sub (operator m B hν hi hh ψ) (ψ : Lp ℝ 2 (ν : Measure V))]
    with x h1 h2 h3
  rw [← Pi.sub_apply, ← h3]
  exact _root_.abs_le.mpr ⟨by simp only [Pi.zero_apply] at h2; linarith,
    by simp only [Pi.zero_apply] at h1; linarith⟩

/-- A bounded generator gives a uniform pointwise slope bound for the backward orbit. -/
theorem ae_abs_slope_operator_backwards_le
    (ψ : (adjointComp (hν.closedWeightedOperator m B hi)).domain)
    {D r s t : ℝ} (hD : 0 ≤ D)
    (hAψ : ∀ᵐ x ∂(ν : Measure V),
      |(adjointComp (hν.closedWeightedOperator m B hi) ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ D)
    (hrs : r < s) (hst : s ≤ t) :
    ∀ᵐ x ∂(ν : Measure V),
      |slope (fun a => Generated.apply (hν.closedWeightedOperator m B hi)
        (hν.closedWeightedOperator_isClosed m B hi)
        (hν.dense_domain_closedWeightedOperator m B hi) (t - a)
        (ψ : Lp ℝ 2 (ν : Measure V))) r s x| ≤ D := by
  revert ψ
  set T := hν.closedWeightedOperator m B hi
  set hT := hν.closedWeightedOperator_isClosed m B hi
  set hd := hν.dense_domain_closedWeightedOperator m B hi
  intro ψ hAψ
  set q : ℝ → Lp ℝ 2 (ν : Measure V) :=
    fun a => Generated.apply T hT hd (t - a) (ψ : Lp ℝ 2 (ν : Measure V))
  have hsr : 0 < s - r := sub_pos.mpr hrs
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  have hsplit : Generated.apply T hT hd (t - r) (ψ : Lp ℝ 2 (ν : Measure V)) =
      Generated.apply T hT hd (t - s)
        (Generated.apply T hT hd (s - r) (ψ : Lp ℝ 2 (ν : Measure V))) := by
    rw [← Generated.add_time T hT hd hts hsr.le]; congr 1; ring
  have hkey : slope q r s = operator m B hν hi hts
      ((s - r)⁻¹ • ((ψ : Lp ℝ 2 (ν : Measure V)) -
        Generated.apply T hT hd (s - r) (ψ : Lp ℝ 2 (ν : Measure V)))) := by
    rw [slope_def_module, HeatSemigroup.apply, Generated.map_smul T hT hd hts,
      Generated.map_sub T hT hd hts, ← hsplit]
  have hdiff := ae_abs_operator_sub_le m B hν hi ψ hD hAψ hsr.le
  have hk : ∀ᵐ x ∂(ν : Measure V), |((s - r)⁻¹ • ((ψ : Lp ℝ 2 (ν : Measure V)) -
      Generated.apply T hT hd (s - r) (ψ : Lp ℝ 2 (ν : Measure V))) :
        Lp ℝ 2 (ν : Measure V)) x| ≤ D := by
    filter_upwards [hdiff, Lp.coeFn_smul (s - r)⁻¹ ((ψ : Lp ℝ 2 (ν : Measure V)) -
      Generated.apply T hT hd (s - r) (ψ : Lp ℝ 2 (ν : Measure V))),
      Lp.coeFn_sub (ψ : Lp ℝ 2 (ν : Measure V))
        (Generated.apply T hT hd (s - r) (ψ : Lp ℝ 2 (ν : Measure V)))] with x h1 h2 h3
    rw [h2, Pi.smul_apply, h3, Pi.sub_apply, smul_eq_mul, abs_mul, abs_inv,
      abs_of_pos hsr, abs_sub_comm]
    rw [inv_mul_le_iff₀ hsr]
    exact h1
  rw [hkey]
  exact ae_abs_operator_le m _ hν hi hts _ hD hk

end Difference

section Interpolation

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **Monotonicity of the interpolation, positive-time data.** For arbitrary `g ∈ L²(ν)`,
`0 < a ≤ t` and nonnegative `φ ∈ C_c^∞`,
`∫ φ Γ(T̄P_t g, T̄P_t g) dν ≤ ∫ (P_{t-a} φ) Γ(T̄P_a g, T̄P_a g) dν`. This is
`Ψ(t) ≤ Ψ(a)` for `Ψ(r) = ∫ (P_{t-r} φ) Γ(T̄P_r g, T̄P_r g) dν`, whose right derivative on
`[a, t)` is `-2` times the heat-test frontend. -/
theorem integral_mul_weakGamma_le_of_pos
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) (g : Lp ℝ 2 (ν : Measure V))
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    ∫ x, φ x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
            (ha.trans_le hat)⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
            (ha.trans_le hat)⟩) x ∂(ν : Measure V) ≤
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi (sub_nonneg.mpr hat)
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
        WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ha⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ha⟩) x
          ∂(ν : Measure V) := by
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  set hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  set hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have ht : 0 < t := ha.trans_le hat
  set Φ : (adjointComp T).domain :=
    ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU1 hφ hφc⟩ with hΦdef
  obtain ⟨C, D, hC, hD, hb⟩ := exists_bounds_operator_toLp m hν hi hνU hU1 hφ hφc
  have hAΦ : ∀ᵐ x ∂(ν : Measure V), |(adjointComp T Φ : Lp ℝ 2 (ν : Measure V)) x| ≤ D := by
    have h0 := (hb 0 le_rfl).2
    have e : (⟨operator m (ContinuousLinearMap.id ℝ V) hν hi le_rfl (Φ : Lp ℝ 2 (ν : Measure V)),
        preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi Φ le_rfl⟩ :
        (adjointComp T).domain) = Φ := Subtype.ext (HeatSemigroup.zero m _ hν hi _)
    rwa [e] at h0
  set q : ℝ → Lp ℝ 2 (ν : Measure V) :=
    fun r => Generated.apply T hT hd (t - r) (Φ : Lp ℝ 2 (ν : Measure V)) with hqdef
  set u : ℝ → Lp V 2 (ν : Measure V) := fun r =>
    if h : 0 < r then T ⟨Generated.apply T hT hd r g, Generated.mem_domain_apply_of_pos T hT hd g h⟩
    else 0 with hudef
  have hu : ∀ r (hr : 0 < r), u r = T ⟨Generated.apply T hT hd r g,
      Generated.mem_domain_apply_of_pos T hT hd g hr⟩ := fun r hr => by
    simp only [hudef, dif_pos hr]
  set Ψ : ℝ → ℝ := fun r => ∫ x, q r x * WeakGamma.apply (u r) (u r) x ∂(ν : Measure V)
    with hΨdef
  -- bounds on the test factor
  have hqb : ∀ r, r ≤ t → ∀ᵐ x ∂(ν : Measure V), |q r x| ≤ C := fun r hr =>
    (hb (t - r) (sub_nonneg.mpr hr)).1
  -- right derivative of `Ψ` on `[a, t)`
  have hderiv : ∀ r (hr : r ∈ Ico a t), HasDerivWithinAt Ψ
      ((∫ x, (adjointComp T ⟨_, preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi Φ
          (sub_nonneg.mpr (le_of_lt hr.2))⟩ : Lp ℝ 2 (ν : Measure V)) x *
          WeakGamma.apply (u r) (u r) x ∂(ν : Measure V)) +
        2 * ∫ x, q r x * WeakGamma.apply (u r)
          (-T ⟨adjointComp T ⟨Generated.apply T hT hd r g,
            Generated.mem_adjointComp_domain_apply_of_pos T hT hd g
              (ha.trans_le hr.1)⟩,
            Generated.mem_domain_adjointComp_apply_of_pos T hT hd g
              (ha.trans_le hr.1) _⟩) x ∂(ν : Measure V)) (Ici r) r := by
    intro r hr
    have hr0 : 0 < r := ha.trans_le hr.1
    have htr : 0 < t - r := sub_pos.mpr hr.2
    have hq : HasDerivWithinAt q _ (Ici r) r :=
      Generated.hasDerivWithinAt_apply_sub_Ici T hT hd Φ htr
    have huder := Generated.hasDerivWithinAt_map_apply_Ici T hT hd g hu hr0
    have hslope : ∀ᶠ s in 𝓝[Ici r \ {r}] r, ∀ᵐ x ∂(ν : Measure V), |slope q r s x| ≤ D := by
      rw [Ici_sdiff_left]
      filter_upwards [Ioo_mem_nhdsGT hr.2] with s hs
      exact ae_abs_slope_operator_backwards_le m (ContinuousLinearMap.id ℝ V)
        hν hi Φ hD hAΦ hs.1 hs.2.le
    have hq'b : ∀ᵐ x ∂(ν : Measure V), |(adjointComp T ⟨_, preserves_domain m
        (ContinuousLinearMap.id ℝ V) hν hi Φ htr.le⟩ : Lp ℝ 2 (ν : Measure V)) x| ≤ D :=
      (hb (t - r) htr.le).2
    have hK : 0 ≤ max C D := le_max_of_le_right hD
    refine WeakGamma.hasDerivWithinAt_integral_mul_apply_self hq huder hK ?_ ?_ ?_
    · filter_upwards [hqb r hr.2.le] with x hx using hx.trans (le_max_left _ _)
    · filter_upwards [hslope] with s hs
      filter_upwards [hs] with x hx using hx.trans (le_max_right _ _)
    · filter_upwards [hq'b] with x hx using hx.trans (le_max_right _ _)
  -- the right derivative is `-2` times the frontend, hence nonpositive
  have hsign : ∀ r (hr : r ∈ Ico a t),
      ((∫ x, (adjointComp T ⟨_, preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi Φ
          (sub_nonneg.mpr (le_of_lt hr.2))⟩ : Lp ℝ 2 (ν : Measure V)) x *
          WeakGamma.apply (u r) (u r) x ∂(ν : Measure V)) +
        2 * ∫ x, q r x * WeakGamma.apply (u r)
          (-T ⟨adjointComp T ⟨Generated.apply T hT hd r g,
            Generated.mem_adjointComp_domain_apply_of_pos T hT hd g (ha.trans_le hr.1)⟩,
            Generated.mem_domain_adjointComp_apply_of_pos T hT hd g
              (ha.trans_le hr.1) _⟩) x ∂(ν : Measure V)) ≤ 0 := by
    intro r hr
    have hr0 : 0 < r := ha.trans_le hr.1
    have htr : 0 ≤ t - r := sub_nonneg.mpr hr.2.le
    have hfr := (integral_weakGamma_operator_nonneg m hν hi hνU hU hconv g hr0 hφ hφc hφ0
      htr).2.2
    have hneg : ∫ x, q r x * WeakGamma.apply (u r)
        (-T ⟨adjointComp T ⟨Generated.apply T hT hd r g,
          Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hr0⟩,
          Generated.mem_domain_adjointComp_apply_of_pos T hT hd g hr0 _⟩) x ∂(ν : Measure V) =
        -∫ x, q r x * WeakGamma.apply (u r)
          (T ⟨adjointComp T ⟨Generated.apply T hT hd r g,
            Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hr0⟩,
            Generated.mem_domain_adjointComp_apply_of_pos T hT hd g hr0 _⟩) x
          ∂(ν : Measure V) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_neg (T ⟨adjointComp T ⟨Generated.apply T hT hd r g,
          Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hr0⟩,
          Generated.mem_domain_adjointComp_apply_of_pos T hT hd g hr0 _⟩)] with x hx
      rw [WeakGamma.apply_def, WeakGamma.apply_def, hx, Pi.neg_apply, inner_neg_right, mul_neg]
    rw [hneg, hu r hr0]
    have key : ∀ X Y : ℝ, 0 ≤ -X / 2 + Y → X + 2 * -Y ≤ 0 := fun X Y h => by linarith
    exact key _ _ hfr
  -- continuity of `Ψ` on `[a, t]`
  have hcont : ContinuousOn Ψ (Icc a t) := by
    intro r hr
    have hqc : ContinuousWithinAt q (Icc a t) r :=
      Generated.continuousOn_apply_sub T hT hd (Φ : Lp ℝ 2 (ν : Measure V)) r hr
    have huc : ContinuousWithinAt u (Icc a t) r :=
      ((Generated.continuousOn_map_apply T hT hd g hu).mono
        (fun s hs => (show (0 : ℝ) < s from ha.trans_le hs.1))) r hr
    have hbd : ∀ᶠ s in 𝓝[Icc a t] r, ∀ᵐ x ∂(ν : Measure V), |q s x| ≤ C := by
      filter_upwards [self_mem_nhdsWithin] with s hs using hqb s hs.2
    exact WeakGamma.tendsto_integral_mul_of_tendsto_multiplier hqc hC hbd (hqb r hr.2) huc huc
  -- monotonicity
  set Ψ' : ℝ → ℝ := fun r => if hr : r ∈ Ico a t then
      ((∫ x, (adjointComp T ⟨_, preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi Φ
          (sub_nonneg.mpr (le_of_lt hr.2))⟩ : Lp ℝ 2 (ν : Measure V)) x *
          WeakGamma.apply (u r) (u r) x ∂(ν : Measure V)) +
        2 * ∫ x, q r x * WeakGamma.apply (u r)
          (-T ⟨adjointComp T ⟨Generated.apply T hT hd r g,
            Generated.mem_adjointComp_domain_apply_of_pos T hT hd g (ha.trans_le hr.1)⟩,
            Generated.mem_domain_adjointComp_apply_of_pos T hT hd g
              (ha.trans_le hr.1) _⟩) x ∂(ν : Measure V)) else 0 with hΨ'def
  have hmono := image_le_of_deriv_right_le_deriv_boundary (f := Ψ) (f' := Ψ')
    (B := fun _ => Ψ a) (B' := fun _ => 0) hcont
    (fun r hr => by simp only [hΨ'def, dif_pos hr]; exact hderiv r hr) le_rfl
    continuousOn_const (fun r _ => hasDerivWithinAt_const _ _ _)
    (fun r hr => by simp only [hΨ'def, dif_pos hr]; exact hsign r hr) (right_mem_Icc.mpr hat)
  -- identify the endpoints
  have hΨt : Ψ t = ∫ x, φ x * WeakGamma.apply
      (T ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht⟩)
      (T ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht⟩)
        x ∂(ν : Measure V) := by
    simp only [hΨdef, hqdef, sub_self, Generated.zero_time]
    rw [hu t ht]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    rw [hx]
    rfl
  have hΨa : Ψ a = ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi (sub_nonneg.mpr hat)
        ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
      WeakGamma.apply
        (T ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ha⟩)
        (T ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ha⟩)
        x ∂(ν : Measure V) := by
    simp only [hΨdef, hqdef]
    rw [hu a ha]
    rfl
  rw [← hΨt, ← hΨa]
  exact hmono

/-- **The square gradient estimate `Γ(P_t f) ≤ P_t Γ(f)`, integrated form.** For the closed
unit-weight gradient `T̄` of `ν = m.tilted (-U)` with a smooth convex potential, every
`f ∈ D(T̄)`, every `t ≥ 0` and every nonnegative `φ ∈ C_c^∞(V)`:
`∫ φ Γ(T̄P_t f, T̄P_t f) dν ≤ ∫ (P_t φ) Γ(T̄f, T̄f) dν`. The case `t > 0` is the limit `a → 0⁺`
of `integral_mul_weakGamma_le_of_pos`, using form-domain continuity `T̄P_a f → T̄f`. -/
theorem integral_mul_weakGamma_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, φ x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) ≤
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
        WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f) x ∂(ν : Measure V) := by
  revert f
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  set hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  set hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  intro f
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have e1 : (⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ : T.domain) =
        f := Subtype.ext (HeatSemigroup.zero m _ hν hi _)
    rw [e1]
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    rw [HeatSemigroup.zero m _ hν hi, hx]
  obtain ⟨C, D, hC, hD, hb⟩ := exists_bounds_operator_toLp m hν hi hνU hU1 hφ hφc
  set q : ℝ → Lp ℝ 2 (ν : Measure V) := fun a => Generated.apply T hT hd (t - a)
    ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) with hqdef
  set u : ℝ → Lp V 2 (ν : Measure V) := fun a =>
    if h : 0 ≤ a then T ⟨Generated.apply T hT hd a (f : Lp ℝ 2 (ν : Measure V)),
      Generated.preserves_form_domain T hT hd f h⟩ else 0 with hudef
  have hu : ∀ a (ha : 0 ≤ a), u a = T ⟨Generated.apply T hT hd a (f : Lp ℝ 2 (ν : Measure V)),
      Generated.preserves_form_domain T hT hd f ha⟩ := fun a ha => by
    simp only [hudef, dif_pos ha]
  have hul : Tendsto u (𝓝[>] 0) (𝓝 (T f)) :=
    (Generated.tendsto_map_apply_zero T hT hd f hu).mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hql : Tendsto q (𝓝[>] 0) (𝓝 (Generated.apply T hT hd t
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ))) :=
    Generated.tendsto_apply_sub_zero T hT hd _ hpos
  have hqb : ∀ᶠ a in 𝓝[>] 0, ∀ᵐ x ∂(ν : Measure V), |q a x| ≤ C := by
    filter_upwards [Ioo_mem_nhdsGT hpos] with a ha
    exact (hb (t - a) (sub_nonneg.mpr ha.2.le)).1
  have hlim := WeakGamma.tendsto_integral_mul_of_tendsto_multiplier hql hC hqb (hb t ht).1 hul hul
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hpos] with a ha
  have h := integral_mul_weakGamma_le_of_pos m hν hi hνU hU hconv (f : Lp ℝ 2 (ν : Measure V))
    hφ hφc hφ0 ha.1 ha.2.le
  simp only [hqdef, hu a ha.1.le]
  exact h

end Interpolation

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup

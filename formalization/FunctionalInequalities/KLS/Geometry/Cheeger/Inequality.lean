import FunctionalInequalities.KLS.Geometry.MinkowskiConstant
import FunctionalInequalities.KLS.Geometry.Median
import FunctionalInequalities.Poincare.SmoothTest.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison
import FunctionalInequalities.KLS.LogConcave.BorellRepresentation

/-!
# Cheeger's inequality for the Minkowski Cheeger infimum

Hole-free layer on top of `KLS/Geometry/MinkowskiConstant.lean` and `KLS/Geometry/Median.lean`:
for an arbitrary Borel probability law `ν` on a finite-dimensional real Hilbert space, the
smooth-test Poincaré constant of `Poincare/SmoothTest/Basic.lean` is bounded by `4 / h_M(ν)²`,
where `h_M = minkowskiConstant ν` is the Minkowski Cheeger infimum.  No density, no absolute
continuity, no nonatomicity and no log-concavity are assumed; dimension zero, where
`h_M = ⊤`, is included and gives the constant `0`.

Read the module in this order.

* `minkowskiConstant_mul_lintegral_le` — the `L¹` Cheeger inequality `h_M ∫ u ≤ ∫ ‖∇u‖` for a
  nonnegative `C¹` Lipschitz `u` whose support has mass at most `1/2`.  For a level `t > 0` the
  superlevel set `{u ≥ t}` has mass at most `1/2`, so the balance `min(s, 1 - s)` of
  `minkowskiConstant_mul_min_le` is the mass itself; the layer-cake formula and the Minkowski
  coarea inequality `lintegral_minkowskiContent_superlevel_le` do the rest.
* `hasDerivAt_sq_posPart`, `contDiff_sq_posPart` — the squared positive part `t ↦ (t⁺)²` is `C¹`
  with derivative `2 t⁺`.
* `minkowskiConstant_sq_mul_lintegral_posPart_sq_le` — `h_M² ∫ (g − m)₊² ≤ 4 ∫_{g > m} ‖∇g‖²`
  for a bounded `C¹` Lipschitz `g` and a level `m` of mass at most `1/2`, by the `L¹` inequality
  applied to `(g − m)₊²`, the chain rule and Cauchy–Schwarz.
* `minkowskiConstant_sq_mul_evariance_le` — `h_M² Var(g) ≤ 4 ∫ ‖∇g‖²` for bounded `C¹` Lipschitz
  `g`, by splitting the second moment about a median (`exists_median`) into its two positive-part
  squares.
* `minkowskiConstant_sq_mul_evariance_le_of_admissible` — the same for every admissible smooth
  test, by cutting off with the smooth bump `scaled R` of
  `Energy/Euclidean/LipschitzApproximation.lean`: the cutoff is bounded, Lipschitz and compactly
  supported, its gradient energy converges by dominated convergence and its variance dominates
  that of the test in the limit by Fatou's lemma.
* `smoothTest_constant_le`, `smoothTest_constant_eq_zero_of_minkowskiConstant_eq_top` — the
  resulting bound on the smooth-test constant and its degenerate case.

The Buser half `Ψ_KLS(μ)² ≤ π C_P(μ)` is **not** part of this module and is not claimed anywhere
in it.  Nothing here depends on the weighted coarea formula, on Sard's theorem, on the relative
perimeter or on any work-in-progress layer.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.KLS.Isoperimetry

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-! ### The `L¹` Cheeger inequality -/

/-- `L¹` Cheeger inequality for a nonnegative `C¹` Lipschitz function whose support carries mass
at most `1/2`: `h_M ∫ u dν ≤ ∫ ‖∇u‖ dν`.  On every superlevel set `{u ≥ t}` with `t > 0` the
balance `min(s, 1 - s)` is the mass itself, so the layer-cake formula turns the defining infimum
of `h_M` into the Minkowski coarea inequality. -/
theorem minkowskiConstant_mul_lintegral_le (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u) (hu0 : ∀ x, 0 ≤ u x)
    (hmass : (ν : Measure V) {x | 0 < u x} ≤ 1 / 2) :
    minkowskiConstant ν * ∫⁻ x, ENNReal.ofReal (u x) ∂(ν : Measure V) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  have humeas : Measurable u := hu.continuous.measurable
  have hanti : Antitone fun t : ℝ => (ν : Measure V) {x | t ≤ u x} := fun t₁ t₂ h =>
    measure_mono fun x hx => le_trans h hx
  have hkey : ∀ t ∈ Set.Ioi (0 : ℝ),
      minkowskiConstant ν * (ν : Measure V) {x | t ≤ u x} ≤
        minkowskiContent ν {x | t ≤ u x} := by
    intro t ht
    have hsub : {x | t ≤ u x} ⊆ {x | 0 < u x} := fun x hx =>
      lt_of_lt_of_le (Set.mem_Ioi.mp ht) hx
    have hle : (ν : Measure V) {x | t ≤ u x} ≤ 1 / 2 :=
      le_trans (measure_mono hsub) hmass
    have hmin : min ((ν : Measure V) {x | t ≤ u x}) (1 - (ν : Measure V) {x | t ≤ u x}) =
        (ν : Measure V) {x | t ≤ u x} := by
      refine min_eq_left ?_
      have h1 : (1 : ℝ≥0∞) - (ν : Measure V) {x | t ≤ u x} ≥ 1 - 1 / 2 := by gcongr
      have h2 : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 :=
        ENNReal.sub_eq_of_eq_add (by simp) (ENNReal.add_halves 1).symm
      rw [h2] at h1
      exact hle.trans h1
    calc minkowskiConstant ν * (ν : Measure V) {x | t ≤ u x}
        = minkowskiConstant ν *
            min ((ν : Measure V) {x | t ≤ u x}) (1 - (ν : Measure V) {x | t ≤ u x}) := by
          rw [hmin]
      _ ≤ minkowskiContent ν {x | t ≤ u x} :=
          minkowskiConstant_mul_min_le ν (measurableSet_le measurable_const humeas)
  calc minkowskiConstant ν * ∫⁻ x, ENNReal.ofReal (u x) ∂(ν : Measure V)
      = minkowskiConstant ν * ∫⁻ t in Set.Ioi (0 : ℝ), (ν : Measure V) {x | t ≤ u x} := by
        rw [lintegral_eq_lintegral_meas_le _ (Eventually.of_forall hu0) humeas.aemeasurable]
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiConstant ν * (ν : Measure V) {x | t ≤ u x} :=
        (lintegral_const_mul _ hanti.measurable).symm
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} :=
        setLIntegral_mono' measurableSet_Ioi hkey
    _ ≤ ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) :=
        lintegral_minkowskiContent_superlevel_le ν hu hK

/-! ### The square of the positive part -/

/-- The squared positive part `t ↦ (t⁺)²` is differentiable with derivative `2 t⁺`; the only
nontrivial point is the origin, where the slope is bounded by `|t|`. -/
theorem hasDerivAt_sq_posPart (t : ℝ) :
    HasDerivAt (fun s : ℝ => max s 0 ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have heq : (fun s : ℝ => max s 0 ^ 2) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [max_eq_right (le_of_lt (Set.mem_Iio.mp hs))]
    have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
    have h2 : (2 : ℝ) * max t 0 = 0 := by simp [max_eq_right ht.le]
    rw [h2]
    exact h0.congr_of_eventuallyEq heq
  · subst ht
    rw [hasDerivAt_iff_tendsto_slope]
    simp only [max_self, mul_zero]
    refine squeeze_zero_norm (a := fun s : ℝ => ‖s‖) (fun s => ?_) ?_
    · rw [slope_def_field]
      simp only [max_self]
      rcases le_or_gt s 0 with hs | hs
      · simp [max_eq_right hs]
      · rw [max_eq_left hs.le]
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero, sub_zero,
          pow_two, mul_div_assoc, div_self (ne_of_gt hs), mul_one]
    · have hc : Tendsto (fun s : ℝ => ‖s‖) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_norm (E := ℝ)).tendsto 0
      exact hc.mono_left nhdsWithin_le_nhds
  · have heq : (fun s : ℝ => max s 0 ^ 2) =ᶠ[𝓝 t] fun s => s ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp [max_eq_left (Set.mem_Ioi.mp hs).le]
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : (2 : ℝ) * max t 0 = 2 * t := by rw [max_eq_left ht.le]
    rw [h2]
    exact h1.congr_of_eventuallyEq heq

/-- The squared positive part is `C¹`: its derivative `2 t⁺` is continuous. -/
theorem contDiff_sq_posPart : ContDiff ℝ 1 (fun s : ℝ => max s 0 ^ 2) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_sq_posPart t).differentiableAt, ?_⟩
  have hd : deriv (fun s : ℝ => max s 0 ^ 2) = fun t => 2 * max t 0 :=
    funext fun t => (hasDerivAt_sq_posPart t).deriv
  rw [hd]
  fun_prop

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Enorm of the gradient rewritten through the Fréchet derivative, the form in which the
measurability of the gradient norm is available. -/
theorem enorm_gradient_eq_enorm_fderiv (f : V → ℝ) (x : V) :
    ‖gradient f x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Poincare.SmoothTest.norm_fderiv_eq_norm_gradient]

omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The gradient enorm of a `C¹` function is measurable. -/
theorem measurable_enorm_gradient {f : V → ℝ} (hf : ContDiff ℝ 1 f) :
    Measurable fun x => ‖gradient f x‖ₑ := by
  have hcont : Continuous fun x => ‖fderiv ℝ f x‖ₑ :=
    continuous_enorm.comp (hf.continuous_fderiv (by simp))
  simpa only [enorm_gradient_eq_enorm_fderiv] using hcont.measurable

/-! ### The positive-part square -/

/-- Cheeger's inequality for the square of the positive part of `g - m` above a level `m` of
mass at most `1/2`: `h_M² ∫ (g − m)₊² ≤ 4 ∫_{g > m} ‖∇g‖²`.  The function `v = (g − m)₊²` is `C¹`,
Lipschitz (because `g` is bounded and Lipschitz), nonnegative and supported exactly on `{g > m}`,
so the `L¹` Cheeger inequality applies; the chain rule `∇v = 2 (g − m)₊ ∇g` and Cauchy–Schwarz
then produce the squared form. -/
theorem minkowskiConstant_sq_mul_lintegral_posPart_sq_le (ν : ProbabilityMeasure V) {g : V → ℝ}
    (hg : ContDiff ℝ 1 g) {K : ℝ≥0} (hK : LipschitzWith K g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (m : ℝ) (hmass : (ν : Measure V) {x | m < g x} ≤ 1 / 2) :
    minkowskiConstant ν ^ 2 * ∫⁻ x, ENNReal.ofReal (max (g x - m) 0 ^ 2) ∂(ν : Measure V) ≤
      4 * ∫⁻ x in {x | m < g x}, ‖gradient g x‖ₑ ^ 2 ∂(ν : Measure V) := by
  set μ : Measure V := (ν : Measure V) with hμ
  set v : V → ℝ := fun x => max (g x - m) 0 ^ 2 with hvdef
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hMnn : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- the derivative of `v`
  have hfd : ∀ x, HasFDerivAt v ((2 * max (g x - m) 0) • fderiv ℝ g x) x := by
    intro x
    have h1 : HasFDerivAt (fun y => g y - m) (fderiv ℝ g x) x :=
      HasFDerivAt.sub_const m (hgd x).hasFDerivAt
    exact (hasDerivAt_sq_posPart (g x - m)).comp_hasFDerivAt x h1
  have hnormfd : ∀ x, ‖fderiv ℝ v x‖ = 2 * max (g x - m) 0 * ‖fderiv ℝ g x‖ := by
    intro x
    rw [(hfd x).fderiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnormgrad : ∀ x, ‖gradient v x‖ = 2 * max (g x - m) 0 * ‖gradient g x‖ := by
    intro x
    rw [← Poincare.SmoothTest.norm_fderiv_eq_norm_gradient,
      ← Poincare.SmoothTest.norm_fderiv_eq_norm_gradient, hnormfd]
  -- `v` is `C¹`, nonnegative, Lipschitz, and supported on `{g > m}`
  have hv : ContDiff ℝ 1 v := contDiff_sq_posPart.comp (hg.sub contDiff_const)
  have hv0 : ∀ x, 0 ≤ v x := fun x => sq_nonneg _
  have hbnd : ∀ x, max (g x - m) 0 ≤ M + |m| := by
    intro x
    refine max_le ?_ (by positivity)
    have h1 : g x ≤ M := le_trans (le_abs_self _) (hM x)
    have h2 : -|m| ≤ m := neg_abs_le m
    linarith
  have hvLip : LipschitzWith (Real.toNNReal (2 * (M + |m|)) * K) v := by
    refine lipschitzWith_of_nnnorm_fderiv_le (fun x => (hfd x).differentiableAt) fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul,
      Real.coe_toNNReal _ (by positivity), hnormfd]
    have h1 : ‖fderiv ℝ g x‖ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ hK
    have h2 : 2 * max (g x - m) 0 ≤ 2 * (M + |m|) := by linarith [hbnd x]
    have h3 : (0 : ℝ) ≤ 2 * max (g x - m) 0 := by positivity
    calc 2 * max (g x - m) 0 * ‖fderiv ℝ g x‖
        ≤ 2 * max (g x - m) 0 * (K : ℝ) := by gcongr
      _ ≤ 2 * (M + |m|) * (K : ℝ) := by gcongr
  have hsupp : {x | 0 < v x} = {x | m < g x} := by
    ext x
    show 0 < v x ↔ m < g x
    rcases le_or_gt (g x - m) 0 with h | h
    · have hz : v x = 0 := by
        show max (g x - m) 0 ^ 2 = 0
        rw [max_eq_right h]
        norm_num
      rw [hz]
      constructor
      · intro hx
        exact absurd hx (lt_irrefl 0)
      · intro hx
        linarith
    · constructor
      · intro _
        linarith
      · intro _
        show 0 < max (g x - m) 0 ^ 2
        rw [max_eq_left h.le]
        positivity
  -- the `L¹` Cheeger inequality applied to `v`
  have hP3 := minkowskiConstant_mul_lintegral_le ν hv hvLip hv0 (by rw [hsupp]; exact hmass)
  -- the Cauchy--Schwarz splitting of `∫ ‖∇v‖`
  set F : V → ℝ≥0∞ := fun x => ENNReal.ofReal (2 * max (g x - m) 0) with hF
  set G : V → ℝ≥0∞ := Set.indicator {x | m < g x} (fun x => ‖gradient g x‖ₑ) with hG
  have hmset : MeasurableSet {x : V | m < g x} :=
    measurableSet_lt measurable_const hg.continuous.measurable
  have hgradmeas : Measurable fun x => ‖gradient g x‖ₑ := measurable_enorm_gradient hg
  have hFmeas : Measurable F := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (measurable_const.mul ((hg.continuous.measurable.sub measurable_const).max
      measurable_const))
  have hGmeas : Measurable G := hgradmeas.indicator hmset
  have hsplit : ∀ x, ‖gradient v x‖ₑ = F x * G x := by
    intro x
    have hbase : ‖gradient v x‖ₑ = F x * ‖gradient g x‖ₑ := by
      rw [← ofReal_norm, hnormgrad, ENNReal.ofReal_mul (by positivity), ofReal_norm]
    rcases le_or_gt (g x - m) 0 with h | h
    · have hFz : F x = 0 := by rw [hF]; simp [max_eq_right h]
      rw [hbase, hFz, zero_mul, zero_mul]
    · have hmem : x ∈ {x : V | m < g x} := by show m < g x; linarith
      rw [hbase, hG, Set.indicator_of_mem hmem]
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (max (g x - m) 0 ^ 2) ∂μ with hA
  set B : ℝ≥0∞ := ∫⁻ x in {x | m < g x}, ‖gradient g x‖ₑ ^ 2 ∂μ with hB
  have hAmeas : Measurable fun x => ENNReal.ofReal (max (g x - m) 0 ^ 2) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (((hg.continuous.measurable.sub measurable_const).max measurable_const).pow
      measurable_const)
  have hFsq : ∫⁻ x, F x ^ 2 ∂μ = 4 * A := by
    have hpt : ∀ x, F x ^ 2 = 4 * ENNReal.ofReal (max (g x - m) 0 ^ 2) := by
      intro x
      rw [hF]
      simp only
      rw [← ENNReal.ofReal_pow (by positivity), mul_pow,
        ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 ^ 2)]
      norm_num
    calc ∫⁻ x, F x ^ 2 ∂μ = ∫⁻ x, 4 * ENNReal.ofReal (max (g x - m) 0 ^ 2) ∂μ := by
          exact lintegral_congr fun x => hpt x
      _ = 4 * A := lintegral_const_mul _ hAmeas
  have hGsq : ∫⁻ x, G x ^ 2 ∂μ = B := by
    have hpt : ∀ x, G x ^ 2 = Set.indicator {x : V | m < g x} (fun x => ‖gradient g x‖ₑ ^ 2) x := by
      intro x
      by_cases hx : x ∈ {x : V | m < g x}
      · rw [hG, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [hG, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        norm_num
    calc ∫⁻ x, G x ^ 2 ∂μ
        = ∫⁻ x, Set.indicator {x : V | m < g x} (fun x => ‖gradient g x‖ₑ ^ 2) x ∂μ :=
          lintegral_congr fun x => hpt x
      _ = B := lintegral_indicator hmset _
  have hholder : ∫⁻ x, (F * G) x ∂μ ≤
      (∫⁻ x, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hFmeas.aemeasurable
      hGmeas.aemeasurable
  have hrpow : ∀ a : ℝ≥0∞, a ^ (2 : ℝ) = a ^ (2 : ℕ) := fun a => by
    rw [← ENNReal.rpow_natCast a 2]
    norm_num
  have hcs : minkowskiConstant ν * A ≤ (4 * A) ^ (1 / (2 : ℝ)) * B ^ (1 / (2 : ℝ)) := by
    refine le_trans hP3 ?_
    have hrw : ∫⁻ x, ‖gradient v x‖ₑ ∂μ = ∫⁻ x, (F * G) x ∂μ :=
      lintegral_congr fun x => hsplit x
    rw [hrw]
    refine le_trans hholder ?_
    have e1 : ∫⁻ x, F x ^ (2 : ℝ) ∂μ = 4 * A := by
      simpa only [hrpow] using hFsq
    have e2 : ∫⁻ x, G x ^ (2 : ℝ) ∂μ = B := by
      simpa only [hrpow] using hGsq
    rw [e1, e2]
  -- squaring and cancelling the (finite) factor `A`
  have hsq : ∀ a : ℝ≥0∞, (a ^ (1 / (2 : ℝ))) ^ (2 : ℕ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast (a ^ (1 / (2 : ℝ))) 2, ← ENNReal.rpow_mul]
    norm_num
  have hsquared : (minkowskiConstant ν * A) ^ (2 : ℕ) ≤ 4 * A * B := by
    calc (minkowskiConstant ν * A) ^ (2 : ℕ)
        ≤ ((4 * A) ^ (1 / (2 : ℝ)) * B ^ (1 / (2 : ℝ))) ^ (2 : ℕ) := by gcongr
      _ = 4 * A * B := by rw [mul_pow, hsq, hsq]
  have hAtop : A ≠ ⊤ := by
    have hle : A ≤ ENNReal.ofReal ((M + |m|) ^ 2) := by
      calc A ≤ ∫⁻ _ : V, ENNReal.ofReal ((M + |m|) ^ 2) ∂μ := by
            refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
            have h0 : (0 : ℝ) ≤ max (g x - m) 0 := le_max_right _ _
            nlinarith [hbnd x]
        _ = ENNReal.ofReal ((M + |m|) ^ 2) := by simp [hμ]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  rcases eq_or_ne A 0 with hA0 | hA0
  · rw [hA0, mul_zero]
    exact zero_le
  · refine (ENNReal.mul_le_mul_iff_left hA0 hAtop).mp ?_
    calc minkowskiConstant ν ^ 2 * A * A = (minkowskiConstant ν * A) ^ (2 : ℕ) := by ring
      _ ≤ 4 * A * B := hsquared
      _ = 4 * B * A := by ring

/-! ### From the two positive parts to the variance -/

/-- The variational characterization of the variance in `ℝ≥0∞` form: the mean minimizes the
quadratic deviation, so the extended variance is bounded by the second moment about any level. -/
theorem evariance_le_lintegral_ofReal_sub_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {X : α → ℝ} (hX : MemLp X 2 μ) (c : ℝ) :
    evariance X μ ≤ ∫⁻ y, ENNReal.ofReal ((X y - c) ^ 2) ∂μ := by
  have hXc : MemLp (fun y => X y - c) 2 μ := hX.sub (memLp_const c)
  have hint : Integrable (fun y => (X y - c) ^ 2) μ := hXc.integrable_sq
  rw [← ofReal_variance hX,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc variance X μ = variance (fun y => X y - c) μ :=
        (variance_sub_const hX.aestronglyMeasurable c).symm
    _ ≤ ∫ y, ((fun y => X y - c) ^ 2) y ∂μ :=
        variance_le_expectation_sq hXc.aestronglyMeasurable
    _ = ∫ y, (X y - c) ^ 2 ∂μ := rfl

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The gradient enorm is invariant under a sign change. -/
theorem enorm_gradient_neg (f : V → ℝ) (x : V) :
    ‖gradient (fun y => -f y) x‖ₑ = ‖gradient f x‖ₑ := by
  rw [enorm_gradient_eq_enorm_fderiv, enorm_gradient_eq_enorm_fderiv,
    show (fun y => -f y) = -f from rfl, fderiv_neg, enorm_neg]

/-- Cheeger's inequality for bounded `C¹` Lipschitz functions: `h_M² Var(g) ≤ 4 ∫ ‖∇g‖²`.
At a median `m` the variance is bounded by the second moment about `m`, which splits into the
two positive-part squares of `g − m` and `m − g`; the first is handled by the positive-part
inequality for `g` at `m`, the second by the same inequality for `−g` at `−m`, and the two
gradient integrals live on the disjoint sets `{g > m}` and `{g < m}`. -/
theorem minkowskiConstant_sq_mul_evariance_le (ν : ProbabilityMeasure V) {g : V → ℝ}
    (hg : ContDiff ℝ 1 g) {K : ℝ≥0} (hK : LipschitzWith K g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    minkowskiConstant ν ^ 2 * evariance g (ν : Measure V) ≤
      4 * ∫⁻ x, ‖gradient g x‖ₑ ^ 2 ∂(ν : Measure V) := by
  set μ : Measure V := (ν : Measure V) with hμ
  have hmeasg : Measurable g := hg.continuous.measurable
  obtain ⟨m, hm1, hm2⟩ := exists_median μ hmeasg
  have hLp : MemLp g 2 μ :=
    MemLp.of_bound hmeasg.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
  -- the two positive-part integrals
  set Ap : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (max (g x - m) 0 ^ 2) ∂μ with hAp
  set An : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (max (m - g x) 0 ^ 2) ∂μ with hAn
  have hApmeas : Measurable fun x => ENNReal.ofReal (max (g x - m) 0 ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((hmeasg.sub measurable_const).max measurable_const).pow measurable_const)
  have hsplit : evariance g μ ≤ Ap + An := by
    refine le_trans (evariance_le_lintegral_ofReal_sub_sq μ hLp m) ?_
    have hpt : ∀ x, ENNReal.ofReal ((g x - m) ^ 2) =
        ENNReal.ofReal (max (g x - m) 0 ^ 2) + ENNReal.ofReal (max (m - g x) 0 ^ 2) := by
      intro x
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rcases le_or_gt (g x - m) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ m - g x)]
        ring
      · rw [max_eq_left h.le, max_eq_right (by linarith : m - g x ≤ (0:ℝ))]
        ring
    calc ∫⁻ x, ENNReal.ofReal ((g x - m) ^ 2) ∂μ
        = ∫⁻ x, (ENNReal.ofReal (max (g x - m) 0 ^ 2)
            + ENNReal.ofReal (max (m - g x) 0 ^ 2)) ∂μ := lintegral_congr fun x => hpt x
      _ = Ap + An := lintegral_add_left hApmeas _
      _ ≤ Ap + An := le_rfl
  -- the positive part of `g - m`
  have hP : minkowskiConstant ν ^ 2 * Ap ≤
      4 * ∫⁻ x in {x | m < g x}, ‖gradient g x‖ₑ ^ 2 ∂μ :=
    minkowskiConstant_sq_mul_lintegral_posPart_sq_le ν hg hK hM m hm1
  -- the positive part of `m - g`, obtained from the same inequality for `-g` at `-m`
  have hsetneg : {x : V | -m < -g x} = {x : V | g x < m} := by
    ext x
    show -m < -g x ↔ g x < m
    constructor
    · intro h; linarith
    · intro h; linarith
  have hmassneg : μ {x : V | -m < (fun y => -g y) x} ≤ 1 / 2 := by
    show μ {x : V | -m < -g x} ≤ 1 / 2
    rw [hsetneg]
    exact hm2
  have hN0 := minkowskiConstant_sq_mul_lintegral_posPart_sq_le ν
    (hg.neg) (hK.neg) (M := M) (fun x => by simpa [abs_neg] using hM x) (-m) hmassneg
  have hN : minkowskiConstant ν ^ 2 * An ≤
      4 * ∫⁻ x in {x | g x < m}, ‖gradient g x‖ₑ ^ 2 ∂μ := by
    have hrwl : ∫⁻ x, ENNReal.ofReal (max ((fun y => -g y) x - -m) 0 ^ 2) ∂μ = An := by
      refine lintegral_congr fun x => ?_
      show ENNReal.ofReal (max (-g x - -m) 0 ^ 2) = ENNReal.ofReal (max (m - g x) 0 ^ 2)
      rw [show -g x - -m = m - g x from by ring]
    have hrwr : ∫⁻ x in {x | -m < (fun y => -g y) x},
        ‖gradient (fun y => -g y) x‖ₑ ^ 2 ∂μ
          = ∫⁻ x in {x | g x < m}, ‖gradient g x‖ₑ ^ 2 ∂μ := by
      rw [show {x : V | -m < (fun y => -g y) x} = {x : V | g x < m} from hsetneg]
      exact lintegral_congr fun x => by rw [enorm_gradient_neg]
    rw [← hrwl, ← hrwr]
    exact hN0
  -- the two gradient integrals live on disjoint sets
  have hdisj : Disjoint {x : V | m < g x} {x : V | g x < m} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : m < g x := hx
    have h2 : g x < m := hx'
    linarith
  have hsetmeas : MeasurableSet {x : V | g x < m} := measurableSet_lt hmeasg measurable_const
  have hsum : ∫⁻ x in {x | m < g x}, ‖gradient g x‖ₑ ^ 2 ∂μ
      + ∫⁻ x in {x | g x < m}, ‖gradient g x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, ‖gradient g x‖ₑ ^ 2 ∂μ := by
    rw [← lintegral_union hsetmeas hdisj]
    exact setLIntegral_le_lintegral _ _
  calc minkowskiConstant ν ^ 2 * evariance g μ
      ≤ minkowskiConstant ν ^ 2 * (Ap + An) := by gcongr
    _ = minkowskiConstant ν ^ 2 * Ap + minkowskiConstant ν ^ 2 * An := mul_add _ _ _
    _ ≤ 4 * ∫⁻ x in {x | m < g x}, ‖gradient g x‖ₑ ^ 2 ∂μ
        + 4 * ∫⁻ x in {x | g x < m}, ‖gradient g x‖ₑ ^ 2 ∂μ := by gcongr
    _ = 4 * (∫⁻ x in {x | m < g x}, ‖gradient g x‖ₑ ^ 2 ∂μ
        + ∫⁻ x in {x | g x < m}, ‖gradient g x‖ₑ ^ 2 ∂μ) := (mul_add _ _ _).symm
    _ ≤ 4 * ∫⁻ x, ‖gradient g x‖ₑ ^ 2 ∂μ := by gcongr

/-! ### From bounded Lipschitz functions to all admissible smooth tests -/

/-- A crude `ℝ≥0∞` form of the elementary inequality `(a + b)² ≤ 4 (a² + b²)`, used to dominate
the gradient of a cutoff by a fixed integrable function. -/
theorem add_sq_le_four_mul_add_sq (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ 2 ≤ (b + b) ^ 2 := by gcongr
      _ = 4 * b ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := by
          gcongr
          exact le_add_self
  · calc (a + b) ^ 2 ≤ (a + a) ^ 2 := by gcongr
      _ = 4 * a ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := by
          gcongr
          exact le_self_add

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- A `C¹` function with compact support is bounded and globally Lipschitz: both its values and
its Fréchet derivative are continuous with compact support, hence bounded. -/
theorem exists_lipschitz_bound_of_hasCompactSupport {u : V → ℝ} (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u) :
    ∃ (C : ℝ≥0) (M : ℝ), LipschitzWith C u ∧ ∀ x, |u x| ≤ M := by
  obtain ⟨M, hM⟩ := hu.continuous.bounded_above_of_compact_support hsupp
  obtain ⟨C, hC⟩ := (hu.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hsupp.fderiv ℝ)
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine ⟨Real.toNNReal C, M, ?_, fun x => by simpa [Real.norm_eq_abs] using hM x⟩
  refine lipschitzWith_of_nnnorm_fderiv_le (hu.differentiable (by simp)) fun x => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hC0]
  exact hC x

open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation in
/-- Cheeger's inequality for every admissible smooth test: `h_M² Var(f) ≤ 4 ∫ ‖∇f‖²`.
The test is cut off with the smooth bump `scaled R`, which makes it bounded, Lipschitz and
compactly supported, so the bounded Lipschitz inequality applies to every cutoff.  Its gradient
energy converges to that of the test by dominated convergence (the cutoff gradient is dominated
by `‖∇f‖ + M |f|`, which is square-integrable because the test is `L²` with finite energy) and
its variance dominates that of the test in the limit by Fatou's lemma. -/
theorem minkowskiConstant_sq_mul_evariance_le_of_admissible (ν : ProbabilityMeasure V)
    {f : V → ℝ} (hf : Poincare.SmoothTest.Admissible (ν : Measure V) f) :
    minkowskiConstant ν ^ 2 * evariance f (ν : Measure V) ≤
      4 * ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂(ν : Measure V) := by
  classical
  set μ : Measure V := (ν : Measure V) with hμ
  obtain ⟨M, hM0, hMbd⟩ := exists_bound_fderiv_bump (E := V)
  have hfC1 : ContDiff ℝ 1 f := hf.smooth'.of_le (by simp)
  have hfmeas : Measurable f := hfC1.continuous.measurable
  have hfdiff : Differentiable ℝ f := hfC1.differentiable (by simp)
  -- the cutoff sequence
  set R : ℕ → ℝ := fun n => (n : ℝ) + 1 with hRdef
  have hRpos : ∀ n, 0 < R n := fun n => by rw [hRdef]; positivity
  have hRone : ∀ n, 1 ≤ R n := fun n => by
    rw [hRdef]
    simp only
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  set g : ℕ → V → ℝ := fun n x => scaled (R n) x * f x with hgdef
  have hgC1 : ∀ n, ContDiff ℝ 1 (g n) := fun n =>
    ((contDiff_scaled (R n)).of_le (by simp)).mul hfC1
  have hgsupp : ∀ n, HasCompactSupport (g n) := fun n =>
    (hasCompactSupport_scaled (hRpos n)).mul_right
  have hgmeas : ∀ n, Measurable (g n) := fun n => (hgC1 n).continuous.measurable
  -- the bounded Lipschitz Cheeger inequality applied to each cutoff
  have hcut : ∀ n, minkowskiConstant ν ^ 2 * evariance (g n) μ ≤
      4 * ∫⁻ x, ‖gradient (g n) x‖ₑ ^ 2 ∂μ := by
    intro n
    obtain ⟨C, N, hlip, hbd⟩ := exists_lipschitz_bound_of_hasCompactSupport (hgC1 n) (hgsupp n)
    exact minkowskiConstant_sq_mul_evariance_le ν (hgC1 n) hlip hbd
  -- the dominating function for the gradients
  have hgradbd : ∀ n, ∀ x, ‖gradient (g n) x‖ₑ ≤
      ‖gradient f x‖ₑ + ‖f x‖ₑ * ENNReal.ofReal M := by
    intro n x
    have hgr : gradient (g n) x =
        scaled (R n) x • gradient f x + f x • gradient (scaled (R n)) x :=
      gradient_scaled_mul (hfdiff x)
    have hns : ‖gradient (scaled (R n)) x‖ ≤ M := by
      rw [← Poincare.SmoothTest.norm_fderiv_eq_norm_gradient]
      refine le_trans (norm_fderiv_scaled_le (hRpos n) hMbd x) ?_
      have h1 : (R n)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr (hRone n)
      nlinarith
    have hreal : ‖gradient (g n) x‖ ≤ ‖gradient f x‖ + |f x| * M := by
      rw [hgr]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |scaled (R n) x| ≤ 1 := by
        rw [abs_of_nonneg (scaled_nonneg _ _)]
        exact scaled_le_one _ _
      have h2 : |scaled (R n) x| * ‖gradient f x‖ ≤ ‖gradient f x‖ := by
        nlinarith [norm_nonneg (gradient f x)]
      have h3 : |f x| * ‖gradient (scaled (R n)) x‖ ≤ |f x| * M := by
        exact mul_le_mul_of_nonneg_left hns (abs_nonneg _)
      linarith
    calc ‖gradient (g n) x‖ₑ = ENNReal.ofReal ‖gradient (g n) x‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (‖gradient f x‖ + |f x| * M) := ENNReal.ofReal_le_ofReal hreal
      _ = ‖gradient f x‖ₑ + ‖f x‖ₑ * ENNReal.ofReal M := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity),
            ENNReal.ofReal_mul (abs_nonneg _), ofReal_norm]
          congr 1
          rw [← ofReal_norm, Real.norm_eq_abs]
  set bnd : V → ℝ≥0∞ := fun x => (‖gradient f x‖ₑ + ‖f x‖ₑ * ENNReal.ofReal M) ^ 2 with hbnd
  -- finiteness of the two square integrals
  have hEfin : ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have h := hf.energy_integrable.hasFiniteIntegral
    have hcongr : ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ
        = ∫⁻ x, ‖(‖gradient f x‖ ^ 2 : ℝ)‖ₑ ∂μ := by
      refine lintegral_congr fun x => ?_
      have h1 : ‖(‖gradient f x‖ ^ 2 : ℝ)‖ₑ = ENNReal.ofReal (‖gradient f x‖ ^ 2) := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [hcongr]
    exact (lt_of_le_of_lt le_rfl h).ne
  have hJfin : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have h := hf.memLp_two.integrable_sq.hasFiniteIntegral
    have hcongr : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(f x ^ 2 : ℝ)‖ₑ ∂μ := by
      refine lintegral_congr fun x => ?_
      have h1 : ‖(f x ^ 2 : ℝ)‖ₑ = ENNReal.ofReal (f x ^ 2) := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 : f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
      rw [h1, h2, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]
    rw [hcongr]
    exact (lt_of_le_of_lt le_rfl h).ne
  have hgradfmeas : Measurable fun x => ‖gradient f x‖ₑ := measurable_enorm_gradient hfC1
  have hbndfin : ∫⁻ x, bnd x ∂μ ≠ ⊤ := by
    have hle : ∫⁻ x, bnd x ∂μ ≤
        4 * (∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ
          + ENNReal.ofReal M ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) := by
      calc ∫⁻ x, bnd x ∂μ
          ≤ ∫⁻ x, 4 * (‖gradient f x‖ₑ ^ 2 + (‖f x‖ₑ * ENNReal.ofReal M) ^ 2) ∂μ :=
            lintegral_mono fun x => add_sq_le_four_mul_add_sq _ _
        _ = 4 * ∫⁻ x, (‖gradient f x‖ₑ ^ 2 + (‖f x‖ₑ * ENNReal.ofReal M) ^ 2) ∂μ := by
            refine lintegral_const_mul _ ?_
            exact (hgradfmeas.pow_const 2).add
              (((hfmeas.enorm).mul measurable_const).pow_const 2)
        _ = 4 * (∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ
              + ∫⁻ x, (‖f x‖ₑ * ENNReal.ofReal M) ^ 2 ∂μ) := by
            rw [lintegral_add_left (hgradfmeas.pow_const 2)]
        _ = 4 * (∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ
              + ENNReal.ofReal M ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) := by
            congr 2
            rw [← lintegral_const_mul _ (hfmeas.enorm.pow_const 2)]
            exact lintegral_congr fun x => by ring
    refine ne_top_of_le_ne_top ?_ hle
    refine ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨hEfin, ?_⟩)
    exact ENNReal.mul_ne_top (by simp [ENNReal.pow_eq_top_iff]) hJfin
  -- pointwise stabilization of the cutoff
  have hstab : ∀ x : V, ∀ n : ℕ, ‖x‖ < R n → g n =ᶠ[𝓝 x] f := by
    intro x n hx
    have hball : Metric.ball (0 : V) (R n) ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hx)
    filter_upwards [hball] with y hy
    have hy' : ‖y‖ ≤ R n := le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy)
    show scaled (R n) y * f y = f y
    rw [scaled_eq_one (hRpos n) hy', one_mul]
  have hexN : ∀ x : V, ∃ N : ℕ, ∀ n ≥ N, ‖x‖ < R n := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine ⟨N, fun n hn => ?_⟩
    have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hRdef]
    simp only
    linarith
  -- the gradient energies converge
  have hAfin : ∀ n, ∫⁻ x, ‖gradient (g n) x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top hbndfin (lintegral_mono fun x => ?_)
    exact pow_le_pow_left' (hgradbd n x) 2
  have hAtend : Tendsto (fun n => ∫⁻ x, ‖gradient (g n) x‖ₑ ^ 2 ∂μ) atTop
      (𝓝 (∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence bnd
      (fun n => (measurable_enorm_gradient (hgC1 n)).pow_const 2)
      (fun n => Eventually.of_forall fun x => pow_le_pow_left' (hgradbd n x) 2) hbndfin ?_
    refine Eventually.of_forall fun x => ?_
    obtain ⟨N, hN⟩ := hexN x
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    have heq := hstab x n (hN n hn)
    rw [enorm_gradient_eq_enorm_fderiv, enorm_gradient_eq_enorm_fderiv, heq.fderiv_eq]
  -- the variances converge pointwise, and Fatou transfers the bound
  have hfint : Integrable f μ := hf.memLp_two.integrable (by norm_num)
  have hmeanTend : Tendsto (fun n => ∫ x, g n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (hgmeas n).aestronglyMeasurable) hfint.abs ?_ ?_
    · intro n
      refine Eventually.of_forall fun x => ?_
      show ‖scaled (R n) x * f x‖ ≤ |f x|
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaled_nonneg _ _)]
      nlinarith [scaled_le_one (R n) x, scaled_nonneg (R n) x, abs_nonneg (f x)]
    · refine Eventually.of_forall fun x => ?_
      obtain ⟨N, hN⟩ := hexN x
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop N] with n hn
      exact ((hstab x n (hN n hn)).eq_of_nhds).symm
  have hFatou : evariance f μ ≤ liminf (fun n => evariance (g n) μ) atTop := by
    have hlim : ∀ x : V, Tendsto
        (fun n => ENNReal.ofReal ((g n x - ∫ y, g n y ∂μ) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((f x - ∫ y, f y ∂μ) ^ 2))) := by
      intro x
      obtain ⟨N, hN⟩ := hexN x
      have hgx : Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop N] with n hn
        exact ((hstab x n (hN n hn)).eq_of_nhds).symm
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (((hgx.sub hmeanTend).pow 2))
    have hcongr : evariance f μ
        = ∫⁻ x, liminf (fun n => ENNReal.ofReal ((g n x - ∫ y, g n y ∂μ) ^ 2)) atTop ∂μ := by
      rw [evariance_eq_lintegral_ofReal]
      exact lintegral_congr fun x => ((hlim x).liminf_eq).symm
    rw [hcongr]
    refine le_trans (lintegral_liminf_le (fun n => ?_)) ?_
    · exact ENNReal.measurable_ofReal.comp (((hgmeas n).sub measurable_const).pow measurable_const)
    · refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
      rw [evariance_eq_lintegral_ofReal]
  -- the three cases of the Minkowski constant
  rcases eq_or_ne (minkowskiConstant ν ^ 2) 0 with hh0 | hh0
  · rw [hh0, zero_mul]
    exact zero_le
  rcases eq_or_ne (minkowskiConstant ν ^ 2) ⊤ with hhtop | hhtop
  · have hzero : ∀ n, evariance (g n) μ = 0 := by
      intro n
      by_contra hne
      have h1 : minkowskiConstant ν ^ 2 * evariance (g n) μ = ⊤ := by
        rw [hhtop, ENNReal.top_mul hne]
      have h2 : (4 : ℝ≥0∞) * ∫⁻ x, ‖gradient (g n) x‖ₑ ^ 2 ∂μ ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) (hAfin n)
      exact h2 (top_le_iff.mp (h1 ▸ hcut n))
    have hv0 : evariance f μ = 0 := by
      refine le_antisymm (le_trans hFatou ?_) (zero_le)
      simp only [hzero]
      exact (liminf_const (0 : ℝ≥0∞)).le
    rw [hv0, mul_zero]
    exact zero_le
  · -- the finite positive case: divide, take the limit, and multiply back
    have hdiv : ∀ n, evariance (g n) μ ≤
        4 * (∫⁻ x, ‖gradient (g n) x‖ₑ ^ 2 ∂μ) / minkowskiConstant ν ^ 2 := by
      intro n
      rw [ENNReal.le_div_iff_mul_le (Or.inl hh0) (Or.inl hhtop), mul_comm]
      exact hcut n
    have hlimdiv : Tendsto
        (fun n => 4 * (∫⁻ x, ‖gradient (g n) x‖ₑ ^ 2 ∂μ) / minkowskiConstant ν ^ 2) atTop
        (𝓝 (4 * (∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ) / minkowskiConstant ν ^ 2)) := by
      have h1 : Tendsto (fun n => (4 : ℝ≥0∞) * ∫⁻ x, ‖gradient (g n) x‖ₑ ^ 2 ∂μ) atTop
          (𝓝 (4 * ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ)) :=
        ENNReal.Tendsto.const_mul hAtend (Or.inr (by norm_num))
      simpa only [div_eq_mul_inv] using
        ENNReal.Tendsto.mul_const h1 (Or.inr (ENNReal.inv_ne_top.mpr hh0))
    have hfinal : evariance f μ ≤
        4 * (∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ) / minkowskiConstant ν ^ 2 := by
      refine le_trans hFatou ?_
      rw [← hlimdiv.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall hdiv)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hh0) (Or.inl hhtop), mul_comm] at hfinal
    exact hfinal

/-! ### The smooth-test Poincaré constant -/

omit [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The gradient energy of an admissible test as an `ℝ≥0∞` integral. -/
theorem ofReal_energy_eq_lintegral (ν : ProbabilityMeasure V) {f : V → ℝ}
    (hf : Poincare.SmoothTest.Admissible (ν : Measure V) f) :
    ENNReal.ofReal (Poincare.SmoothTest.energy (ν : Measure V) f) =
      ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂(ν : Measure V) := by
  rw [Poincare.SmoothTest.energy,
    ofReal_integral_eq_lintegral_ofReal hf.energy_integrable
      (Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Cheeger's inequality for the smooth-test Poincaré constant of an arbitrary Borel probability
law: `C_P^smooth(ν) ≤ 4 / h_M(ν)²`.  No density, no absolute continuity and no log-concavity are
assumed; when `h_M = 0` the right-hand side is `⊤` and the statement is vacuous, and when
`h_M = ⊤` the admissible tests all have vanishing variance and the constant is `0`. -/
theorem smoothTest_constant_le (ν : ProbabilityMeasure V) :
    Poincare.SmoothTest.constant (ν : Measure V) ≤ 4 / minkowskiConstant ν ^ 2 := by
  set μ : Measure V := (ν : Measure V) with hμ
  set h : ℝ≥0∞ := minkowskiConstant ν ^ 2 with hhdef
  rcases eq_or_ne h 0 with h0 | h0
  · rw [h0, ENNReal.div_zero (by norm_num)]
    exact le_top
  have hctop : (4 : ℝ≥0∞) / h ≠ ⊤ := ENNReal.div_ne_top (by norm_num) h0
  set C : ℝ≥0 := (4 / h).toNNReal with hCdef
  have hCcoe : (C : ℝ≥0∞) = 4 / h := ENNReal.coe_toNNReal hctop
  have hholds : Poincare.SmoothTest.Holds μ (C : ℝ) := by
    refine ⟨inferInstance, C.coe_nonneg, ?_⟩
    intro f hfadm
    have hE : ENNReal.ofReal (Poincare.SmoothTest.energy μ f) =
        ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂μ := ofReal_energy_eq_lintegral ν hfadm
    have hV : ENNReal.ofReal (variance f μ) = evariance f μ := ofReal_variance hfadm.memLp_two
    have hkey := minkowskiConstant_sq_mul_evariance_le_of_admissible ν hfadm
    rw [← hV, ← hE, ← hhdef] at hkey
    have hVar0 : 0 ≤ variance f μ := variance_nonneg _ _
    have hEn0 : 0 ≤ Poincare.SmoothTest.energy μ f := Poincare.SmoothTest.energy_nonneg _ _
    rcases eq_or_ne h ⊤ with htop | htop
    · have hVz : ENNReal.ofReal (variance f μ) = 0 := by
        by_contra hne
        rw [htop, ENNReal.top_mul hne] at hkey
        exact (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) (top_le_iff.mp hkey)
      have hvle : variance f μ ≤ 0 := ENNReal.ofReal_eq_zero.mp hVz
      have hC0 : (C : ℝ) = 0 := by
        have : (C : ℝ≥0∞) = 0 := by rw [hCcoe, htop, ENNReal.div_top]
        simpa using congrArg ENNReal.toReal this
      rw [hC0, zero_mul]
      exact hvle
    · have hle : ENNReal.ofReal (variance f μ) ≤
          4 / h * ENNReal.ofReal (Poincare.SmoothTest.energy μ f) := by
        have hle' : ENNReal.ofReal (variance f μ) ≤
            4 * ENNReal.ofReal (Poincare.SmoothTest.energy μ f) / h := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop), mul_comm]
          exact hkey
        have hrw : 4 * ENNReal.ofReal (Poincare.SmoothTest.energy μ f) / h =
            4 / h * ENNReal.ofReal (Poincare.SmoothTest.energy μ f) := by
          simp only [div_eq_mul_inv]
          ring
        rwa [hrw] at hle'
      calc variance f μ = (ENNReal.ofReal (variance f μ)).toReal :=
            (ENNReal.toReal_ofReal hVar0).symm
        _ ≤ (4 / h * ENNReal.ofReal (Poincare.SmoothTest.energy μ f)).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top hctop ENNReal.ofReal_ne_top) hle
        _ = (C : ℝ) * Poincare.SmoothTest.energy μ f := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hEn0, ← hCcoe]
            simp
  calc Poincare.SmoothTest.constant μ ≤ (C : ℝ≥0∞) := Poincare.SmoothTest.constant_le hholds
    _ = 4 / h := hCcoe

/-- An infinite Minkowski Cheeger infimum forces a vanishing smooth-test Poincaré constant:
`4 / ⊤ = 0`.  In particular this covers dimension zero, where `minkowskiConstant ν = ⊤`. -/
theorem smoothTest_constant_eq_zero_of_minkowskiConstant_eq_top (ν : ProbabilityMeasure V)
    (h : minkowskiConstant ν = ⊤) :
    Poincare.SmoothTest.constant (ν : Measure V) = 0 := by
  refine le_antisymm ?_ zero_le
  have hle := smoothTest_constant_le ν
  rwa [h, ENNReal.top_pow (by norm_num), ENNReal.div_top] at hle

end FunctionalInequalities.KLS.Isoperimetry

namespace FunctionalInequalities.KLS.LogConcave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- **Cheeger's inequality for log-concave laws**, the Cheeger half of
`thm:logconcave-cheeger-poincare-comparison`: `C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²`.  The literature
constant of `def:literature-poincare-constant` is the smooth-test constant of the intrinsic law
(`Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope`, under the absolute continuity
every log-concave law has), the isoperimetric constant `h_μ` is the Minkowski constant of the
intrinsic law (`Isoperimetry.constant_eq_minkowskiConstant_intrinsic`), and
`Isoperimetry.smoothTest_constant_le` gives the bound on the coordinate space.  Dirac laws are
included with both sides `0`.  The Buser half `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` is **not** proved. -/
theorem literatureConstant_le_four_mul_inverseScale_sq {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * Isoperimetry.inverseScale μ ^ 2 := by
  have hac := hμ.intrinsic_absolutelyContinuous Measure.addHaar
  have h := (Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope μ Measure.addHaar hac).2
  rw [← h, Isoperimetry.inverseScale, Isoperimetry.constant_eq_minkowskiConstant_intrinsic μ,
    ← ENNReal.inv_pow, ← div_eq_mul_inv]
  exact Isoperimetry.smoothTest_constant_le _

end FunctionalInequalities.KLS.LogConcave

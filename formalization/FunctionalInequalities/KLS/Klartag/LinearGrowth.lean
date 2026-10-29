import FunctionalInequalities.Analysis.Convex.Coercivity
import Mathlib.Analysis.Convex.Gauge
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Linear growth of centered convex potentials

Klartag, *Logarithmically-concave moment measures I*, arXiv:1309.2767v1, Lemma 2.2. A convex
`ψ : E → ℝ` on a finite-dimensional real inner-product space is *centered* (Klartag (7)) if
`∫ e^{-ψ} = 1` and `∫ x e^{-ψ(x)} dx = 0` for an additive Haar measure. For
`K(ψ) = {x ; ψ(x) ≤ 2n + inf ψ}` and its Minkowski functional `‖x‖_ψ = gauge K(ψ) x`,
`ψ(x) ≥ n ‖x‖_ψ + ψ(0) - 2n` for every `x` (`MomentMeasure.linear_growth_of_centered`).

The input (10) `ψ(0) ≤ n + inf ψ`, which Klartag quotes from Fradelizi, is proved here for
centered `ψ` (`MomentMeasure.le_finrank_add_iInf_of_centered`): Jensen's inequality for the
probability measure `e^{-ψ} dx` gives `ψ(0) ≤ ∫ ψ e^{-ψ}`, and the dilation inequality
`∫ e^{-s u} ≥ s^{-n} ∫ e^{-u}` (`s ≥ 1`) about a minimiser, with `u = ψ - inf ψ`, gives
`∫ u e^{-u} ≤ n ∫ e^{-u}` in the limit `s ↓ 1`. The minimiser and compact sublevels come from
`Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`.
The deduction of (9) from (10) is Klartag's convexity argument
(`MomentMeasure.linear_growth_of_le_finrank_add_iInf`, for any real normed space), applied at the
points `x/λ ∉ K(ψ)`, `1 < λ < ‖x‖_ψ`, so that continuity of `ψ` is not invoked there.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Convexity about a minimiser: `u(x₀ + s(x - x₀)) ≤ s u(x)` for `s ∈ [0,1]` when `u(x₀) = 0`. -/
private theorem convex_scale_le {F : Type*} [AddCommGroup F] [Module ℝ F] {u : F → ℝ} (hu : ConvexOn ℝ univ u) {x₀ : F} (hx₀ : u x₀ = 0)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : F) : u (x₀ + s • (x - x₀)) ≤ s * u x := by
  have h := hu.2 (mem_univ x₀) (mem_univ x) (sub_nonneg.mpr hs1) hs0 (by ring)
  have he : (1 - s) • x₀ + s • x = x₀ + s • (x - x₀) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [he, hx₀, smul_eq_mul, smul_eq_mul, mul_zero, zero_add] at h
  exact h

/-- `e^{-s u}` is integrable for `0 < s ≤ 1` when `e^{-u}` is, `u ≥ 0` convex with `u(x₀) = 0`. -/
private theorem integrable_exp_neg_smul (m : Measure E) [m.IsAddHaarMeasure] {u : E → ℝ}
    (hu : ConvexOn ℝ univ u) (hcont : Continuous u) {x₀ : E} (hx₀ : u x₀ = 0)
    (hint : Integrable (fun x => Real.exp (-u x)) m) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Integrable (fun x => Real.exp (-(s * u x))) m := by
  have hg : Integrable (fun x => Real.exp (-u (x₀ + s • (x - x₀)))) m := by
    have h1 : Integrable (fun y => Real.exp (-u (x₀ + y))) m :=
      hint.comp_add_left x₀
    have h2 : Integrable (fun x => Real.exp (-u (x₀ + s • x))) m := h1.comp_smul hs0.ne'
    have h3 := h2.comp_sub_right x₀
    simpa using h3
  refine hg.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (neg_le_neg (convex_scale_le hu hx₀ hs0.le hs1 x))

/-- `t e^{-t} ≤ 2 e^{-t/2}` for `t ≥ 0`. -/
private theorem mul_exp_neg_le (t : ℝ) :
    t * Real.exp (-t) ≤ 2 * Real.exp (-(1 / 2 * t)) := by
  have h1 : t ≤ 2 * Real.exp (1 / 2 * t) := by
    have := Real.add_one_le_exp (1 / 2 * t); linarith
  have he : Real.exp (-t) = Real.exp (-(1 / 2 * t)) * Real.exp (-(1 / 2 * t)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (1 / 2 * t) * Real.exp (-(1 / 2 * t)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-(1 / 2 * t))
  calc t * Real.exp (-t) = t * Real.exp (-(1 / 2 * t)) * Real.exp (-(1 / 2 * t)) := by
        rw [he]; ring
    _ ≤ 2 * Real.exp (1 / 2 * t) * Real.exp (-(1 / 2 * t)) * Real.exp (-(1 / 2 * t)) := by
        gcongr
    _ = 2 * Real.exp (-(1 / 2 * t)) := by
        rw [mul_assoc 2, h3, mul_one]

/-- Linear growth about a minimiser from a bounded sublevel. -/
private theorem exists_norm_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : F → ℝ} (hu : ConvexOn ℝ univ u) {x₀ : F}
    (hx₀ : u x₀ = 0) (hnn : ∀ x, 0 ≤ u x) (hS : Bornology.IsBounded {y | u y ≤ 1}) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, ‖x - x₀‖ ≤ R * (u x + 1) := by
  obtain ⟨R0, hR0⟩ := hS.subset_closedBall x₀
  refine ⟨max R0 0 + 1, by positivity, fun x => ?_⟩
  set R := max R0 0 + 1 with hR
  have hRpos : 0 < R := by positivity
  by_cases hx : ‖x - x₀‖ ≤ R
  · nlinarith [hnn x]
  · push Not at hx
    have hd : 0 < ‖x - x₀‖ := lt_trans hRpos hx
    set s := R / ‖x - x₀‖ with hs
    have hs0 : 0 < s := div_pos hRpos hd
    have hs1 : s < 1 := (div_lt_one hd).mpr hx
    have hz : ‖(x₀ + s • (x - x₀)) - x₀‖ = R := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hs,
        div_mul_cancel₀ _ hd.ne']
    have hnot : x₀ + s • (x - x₀) ∉ {y | u y ≤ 1} := by
      intro hmem
      have := hR0 hmem
      rw [Metric.mem_closedBall, dist_eq_norm, hz] at this
      have : R0 < R := by rw [hR]; linarith [le_max_left R0 0]
      linarith
    have hgt : 1 < u (x₀ + s • (x - x₀)) := not_le.mp hnot
    have hle := convex_scale_le hu hx₀ hs0.le hs1.le x
    have h1 : 1 < s * u x := lt_of_lt_of_le hgt hle
    have h2 : ‖x - x₀‖ < R * u x := by
      have := mul_lt_mul_of_pos_left h1 hd
      rw [hs, ← mul_assoc, mul_div_cancel₀ _ hd.ne', mul_one] at this
      linarith
    nlinarith

/-- Dilation about a minimiser: `∫ e^{-su} ≥ s^{-n} ∫ e^{-u}` for `s ≥ 1`. -/
private theorem integral_exp_neg_smul_ge (m : Measure E) [m.IsAddHaarMeasure] {u : E → ℝ}
    (hu : ConvexOn ℝ univ u) (hcont : Continuous u) {x₀ : E} (hx₀ : u x₀ = 0)
    (hnn : ∀ x, 0 ≤ u x) (hint : Integrable (fun x => Real.exp (-u x)) m) {s : ℝ} (hs : 1 ≤ s) :
    (s ^ Module.finrank ℝ E)⁻¹ * ∫ x, Real.exp (-u x) ∂m ≤ ∫ x, Real.exp (-(s * u x)) ∂m := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hsint : Integrable (fun x => Real.exp (-(s * u x))) m :=
    hint.mono' (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (neg_le_neg (le_mul_of_one_le_left (hnn x) hs)))
  -- translate to the minimiser and dilate by `s⁻¹`
  have htr (f : E → ℝ) : ∫ x, f x ∂m = ∫ y, f (x₀ + y) ∂m :=
    (integral_add_left_eq_self (μ := m) f x₀).symm
  have hdil : ∫ y, Real.exp (-(s * u (x₀ + s⁻¹ • y))) ∂m =
      s ^ Module.finrank ℝ E * ∫ y, Real.exp (-(s * u (x₀ + y))) ∂m := by
    rw [Measure.integral_comp_smul (μ := m) (fun y => Real.exp (-(s * u (x₀ + y)))) s⁻¹]
    rw [inv_pow, inv_inv, abs_of_pos (pow_pos hs0 _), smul_eq_mul]
  have hmono : ∫ y, Real.exp (-u (x₀ + y)) ∂m ≤
      ∫ y, Real.exp (-(s * u (x₀ + s⁻¹ • y))) ∂m := by
    refine integral_mono (hint.comp_add_left x₀) ?_ (fun y => ?_)
    · exact ((hsint.comp_add_left x₀).comp_smul (inv_ne_zero hs0.ne'))
    · have h := convex_scale_le hu hx₀ (inv_nonneg.mpr hs0.le) (inv_le_one_of_one_le₀ hs) (x₀ + y)
      rw [add_sub_cancel_left] at h
      have : s * u (x₀ + s⁻¹ • y) ≤ u (x₀ + y) := by
        have := mul_le_mul_of_nonneg_left h hs0.le
        rwa [← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul] at this
      exact Real.exp_le_exp.mpr (neg_le_neg this)
  rw [htr (fun x => Real.exp (-u x)), htr (fun x => Real.exp (-(s * u x)))]
  rw [hdil] at hmono
  have hpow : 0 < s ^ Module.finrank ℝ E := pow_pos hs0 _
  calc (s ^ Module.finrank ℝ E)⁻¹ * ∫ y, Real.exp (-u (x₀ + y)) ∂m
      ≤ (s ^ Module.finrank ℝ E)⁻¹ *
          (s ^ Module.finrank ℝ E * ∫ y, Real.exp (-(s * u (x₀ + y))) ∂m) :=
        mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hpow.le)
    _ = ∫ y, Real.exp (-(s * u (x₀ + y))) ∂m := by
        rw [← mul_assoc, inv_mul_cancel₀ hpow.ne', one_mul]

/-- `u e^{-u}` is integrable (dominated by `2 e^{-u/2}`). -/
private theorem integrable_mul_exp_neg (m : Measure E) [m.IsAddHaarMeasure] {u : E → ℝ}
    (hu : ConvexOn ℝ univ u) (hcont : Continuous u) {x₀ : E} (hx₀ : u x₀ = 0)
    (hnn : ∀ x, 0 ≤ u x) (hint : Integrable (fun x => Real.exp (-u x)) m) :
    Integrable (fun x => u x * Real.exp (-u x)) m := by
  have hhalf := integrable_exp_neg_smul m hu hcont hx₀ hint (s := 1 / 2) (by norm_num) (by norm_num)
  exact (hhalf.const_mul 2).mono' (by fun_prop) (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn x) (Real.exp_pos _).le)]
    exact mul_exp_neg_le (u x))

/-- **Entropy bound about a minimiser**: `∫ u e^{-u} ≤ n ∫ e^{-u}` for convex `u ≥ 0` with
`u(x₀) = 0` and `e^{-u}` integrable. -/
private theorem integral_mul_exp_neg_le (m : Measure E) [m.IsAddHaarMeasure] {u : E → ℝ}
    (hu : ConvexOn ℝ univ u) (hcont : Continuous u) {x₀ : E} (hx₀ : u x₀ = 0)
    (hnn : ∀ x, 0 ≤ u x) (hint : Integrable (fun x => Real.exp (-u x)) m) :
    ∫ x, u x * Real.exp (-u x) ∂m ≤
      (Module.finrank ℝ E : ℝ) * ∫ x, Real.exp (-u x) ∂m := by
  set n : ℕ := Module.finrank ℝ E with hn
  set G1 := ∫ x, Real.exp (-u x) ∂m with hG1
  have hG1nn : 0 ≤ G1 := integral_nonneg fun x => (Real.exp_pos _).le
  have hdom := integrable_mul_exp_neg m hu hcont hx₀ hnn hint
  -- for every `s > 1`, `∫ u e^{-su} ≤ n G1`
  have hstep : ∀ s : ℝ, 1 < s → ∫ x, u x * Real.exp (-(s * u x)) ∂m ≤ n * G1 := by
    intro s hs
    have hs0 : 0 < s := lt_trans one_pos hs
    have hsint : Integrable (fun x => Real.exp (-(s * u x))) m :=
      hint.mono' (by fun_prop) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (neg_le_neg (le_mul_of_one_le_left (hnn x) hs.le)))
    have hsuint : Integrable (fun x => u x * Real.exp (-(s * u x))) m :=
      hdom.mono' (by fun_prop) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn x) (Real.exp_pos _).le)]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (neg_le_neg (le_mul_of_one_le_left (hnn x) hs.le))) (hnn x))
    -- pointwise convexity of `exp`
    have hpt : ∀ x, Real.exp (-(s * u x)) * ((s - 1) * u x + 1) ≤ Real.exp (-u x) := by
      intro x
      have h := Real.add_one_le_exp ((s - 1) * u x)
      have h2 : Real.exp (-(s * u x)) * Real.exp ((s - 1) * u x) = Real.exp (-u x) := by
        rw [← Real.exp_add]; ring_nf
      calc Real.exp (-(s * u x)) * ((s - 1) * u x + 1)
          ≤ Real.exp (-(s * u x)) * Real.exp ((s - 1) * u x) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = Real.exp (-u x) := h2
    have hupper : (s - 1) * ∫ x, u x * Real.exp (-(s * u x)) ∂m +
        ∫ x, Real.exp (-(s * u x)) ∂m ≤ G1 := by
      rw [← integral_const_mul, ← integral_add (hsuint.const_mul _) hsint]
      refine integral_mono ((hsuint.const_mul _).add hsint) hint (fun x => ?_)
      have := hpt x
      simp only
      nlinarith [this]
    have hlower := integral_exp_neg_smul_ge m hu hcont hx₀ hnn hint hs.le
    -- Bernoulli: `1 - s^{-n} ≤ n (s - 1)`
    have hbern : 1 - (s ^ n)⁻¹ ≤ n * (s - 1) := by
      have hb := one_add_mul_le_pow (a := s⁻¹ - 1) (by
        have : 0 < s⁻¹ := inv_pos.mpr hs0
        linarith) n
      rw [add_sub_cancel, inv_pow] at hb
      have hinv : s⁻¹ - 1 ≥ -(s - 1) := by
        have : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs.le
        have : 0 < s⁻¹ := inv_pos.mpr hs0
        have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
        nlinarith
      have : (n : ℝ) * (s⁻¹ - 1) ≥ (n : ℝ) * (-(s - 1)) :=
        mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg n)
      linarith
    have hkey : (s - 1) * ∫ x, u x * Real.exp (-(s * u x)) ∂m ≤ (s - 1) * (n * G1) := by
      nlinarith [mul_le_mul_of_nonneg_right hbern hG1nn]
    exact le_of_mul_le_mul_left hkey (by linarith)
  -- let `s ↓ 1` along `1 + 1/(k+1)`
  set sk : ℕ → ℝ := fun k => 1 + 1 / ((k : ℝ) + 1) with hsk
  have hsk1 (k : ℕ) : 1 < sk k := by
    simp only [hsk]; have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hlim : Tendsto (fun k => ∫ x, u x * Real.exp (-(sk k * u x)) ∂m) atTop
      (𝓝 (∫ x, u x * Real.exp (-u x) ∂m)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => u x * Real.exp (-u x))
      (fun k => by fun_prop) hdom (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn x) (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (neg_le_neg (le_mul_of_one_le_left (hnn x) (hsk1 k).le))) (hnn x)
    · have hs : Tendsto sk atTop (𝓝 1) := by
        have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [hsk] using h0.const_add 1
      have := ((hs.mul_const (u x)).neg.rexp).const_mul (u x)
      simpa using this
  exact le_of_tendsto' hlim fun k => hstep (sk k) (hsk1 k)

/-- **Fradelizi's inequality for a centered convex potential** (Klartag arXiv:1309.2767v1, (10),
quoting Fradelizi): if `ψ` is convex with `∫ e^{-ψ} = 1` and `∫ x e^{-ψ(x)} dx = 0` (Klartag's
"centered", (7)), then `ψ(0) ≤ n + inf ψ`. -/
theorem le_finrank_add_iInf_of_centered (m : Measure E) [m.IsAddHaarMeasure] {ψ : E → ℝ}
    (hψ : ConvexOn ℝ univ ψ) (hnorm : ∫ x, Real.exp (-ψ x) ∂m = 1)
    (hbar : ∫ x, Real.exp (-ψ x) • x ∂m = 0) :
    BddBelow (range ψ) ∧ ψ 0 ≤ (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y := by
  have hint : Integrable (fun x => Real.exp (-ψ x)) m := by
    by_contra h
    rw [integral_undef h] at hnorm
    norm_num at hnorm
  obtain ⟨⟨x₀, hx₀⟩, hcomp⟩ :=
    FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
      m hψ hint
  have hcont : Continuous ψ := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hψ)
  have hbdd : BddBelow (range ψ) := ⟨ψ x₀, by rintro _ ⟨y, rfl⟩; exact hx₀ y⟩
  have hinf : ⨅ y, ψ y = ψ x₀ := le_antisymm (ciInf_le hbdd x₀) (le_ciInf hx₀)
  refine ⟨hbdd, ?_⟩
  rw [hinf]
  -- the normalised potential `u = ψ - ψ x₀`
  set c := ψ x₀ with hc
  set u : E → ℝ := fun x => ψ x - c with hu_def
  have hu : ConvexOn ℝ univ u := hψ.sub (concaveOn_const c convex_univ)
  have hucont : Continuous u := hcont.sub continuous_const
  have hux₀ : u x₀ = 0 := sub_self c
  have hunn : ∀ x, 0 ≤ u x := fun x => sub_nonneg.mpr (hx₀ x)
  have hexp (x : E) : Real.exp (-u x) = Real.exp c * Real.exp (-ψ x) := by
    rw [← Real.exp_add]; simp [hu_def]; ring_nf
  have huint : Integrable (fun x => Real.exp (-u x)) m := by
    simpa only [hexp] using hint.const_mul (Real.exp c)
  have hent := integral_mul_exp_neg_le m hu hucont hux₀ hunn huint
  have hudom := integrable_mul_exp_neg m hu hucont hux₀ hunn huint
  -- `∫ u e^{-ψ} ≤ n`
  have hec : 0 < Real.exp c := Real.exp_pos c
  have hent' : ∫ x, u x * Real.exp (-ψ x) ∂m ≤ (Module.finrank ℝ E : ℝ) := by
    have h1 : ∫ x, u x * Real.exp (-u x) ∂m = Real.exp c * ∫ x, u x * Real.exp (-ψ x) ∂m := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hexp]; ring)
    have h2 : ∫ x, Real.exp (-u x) ∂m = Real.exp c := by
      simp only [hexp]; rw [integral_const_mul, hnorm, mul_one]
    rw [h1, h2] at hent
    nlinarith
  have hψint : Integrable (fun x => ψ x * Real.exp (-ψ x)) m := by
    have h1 : Integrable (fun x => u x * Real.exp (-ψ x)) m := by
      have := hudom.const_mul (Real.exp (-c))
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [hexp]
      rw [← mul_assoc, mul_comm (Real.exp (-c)), mul_assoc, ← mul_assoc (Real.exp (-c)),
        ← Real.exp_add]
      simp
    exact (h1.add (hint.const_mul c)).congr (Eventually.of_forall fun x => by
      simp only [Pi.add_apply, hu_def]; ring)
  have hψbound : ∫ x, ψ x * Real.exp (-ψ x) ∂m ≤ c + (Module.finrank ℝ E : ℝ) := by
    have : ∫ x, ψ x * Real.exp (-ψ x) ∂m =
        ∫ x, u x * Real.exp (-ψ x) ∂m + c * ∫ x, Real.exp (-ψ x) ∂m := by
      rw [← integral_const_mul, ← integral_add _ (hint.const_mul c)]
      · exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hu_def]; ring)
      · exact (hψint.sub (hint.const_mul c)).congr (Eventually.of_forall fun x => by
          simp only [Pi.sub_apply, hu_def]; ring)
    rw [this, hnorm, mul_one]
    linarith
  -- integrability of the first moment, from linear growth
  have hS : Bornology.IsBounded {y | u y ≤ 1} := by
    have : {y | u y ≤ 1} = {y | ψ y ≤ c + 1} := by
      ext y; simp only [mem_ofPred_eq, hu_def, sub_le_iff_le_add']
    rw [this]; exact (hcomp (c + 1)).isBounded
  obtain ⟨R, hR, hgrow⟩ := exists_norm_sub_le hu hux₀ hunn hS
  have hue : Integrable (fun x => u x * Real.exp (-ψ x)) m := by
    have := hudom.const_mul (Real.exp (-c))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [hexp]
    rw [← mul_assoc, mul_comm (Real.exp (-c)), mul_assoc, ← mul_assoc (Real.exp (-c)),
      ← Real.exp_add]
    simp
  have hxint : Integrable (fun x => Real.exp (-ψ x) • x) m := by
    refine ((hint.const_mul (‖x₀‖ + R)).add (hue.const_mul R)).mono' (by fun_prop)
      (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : ‖x‖ ≤ ‖x₀‖ + R * (u x + 1) := by
      have := norm_le_norm_add_norm_sub' x x₀
      have h2 := hgrow x
      linarith [norm_sub_rev x x₀]
    have hpos := (Real.exp_pos (-ψ x)).le
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos]
  -- Jensen for the probability measure `e^{-ψ} dm`
  set f : E → NNReal := fun x => (Real.exp (-ψ x)).toNNReal with hf_def
  have hfcoe (x : E) : (f x : ℝ) = Real.exp (-ψ x) :=
    Real.coe_toNNReal _ (Real.exp_pos _).le
  have hfmeas : Measurable f := (by fun_prop : Measurable fun x => (Real.exp (-ψ x)).toNNReal)
  set μ := m.withDensity (fun x => (f x : ENNReal)) with hμ
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_coe_eq_integral _ (by simpa only [hfcoe] using hint)]
    simp only [hfcoe, hnorm, ENNReal.ofReal_one]
  have hsmulE : (fun x : E => f x • x) = fun x => Real.exp (-ψ x) • x := by
    funext x; rw [NNReal.smul_def, hfcoe]
  have hsmulR : (fun x : E => f x • ψ x) = fun x => ψ x * Real.exp (-ψ x) := by
    funext x; rw [NNReal.smul_def, hfcoe, smul_eq_mul, mul_comm]
  have hidμ : Integrable (fun x : E => x) μ := by
    rw [hμ, integrable_withDensity_iff_integrable_smul hfmeas, hsmulE]
    exact hxint
  have hψμ : Integrable (fun x => ψ x) μ := by
    rw [hμ, integrable_withDensity_iff_integrable_smul hfmeas, hsmulR]
    exact hψint
  have hbarμ : ∫ x, x ∂μ = 0 := by
    rw [hμ, integral_withDensity_eq_integral_smul hfmeas, hsmulE]
    exact hbar
  have hψμeq : ∫ x, ψ x ∂μ = ∫ x, ψ x * Real.exp (-ψ x) ∂m := by
    rw [hμ, integral_withDensity_eq_integral_smul hfmeas, hsmulR]
  have hjensen := hψ.map_integral_le (μ := μ) (f := fun x => x) hcont.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hidμ hψμ
  simp only [hbarμ] at hjensen
  rw [hψμeq] at hjensen
  linarith


section Conditional

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Klartag arXiv:1309.2767v1, Lemma 2.2**, given (10): if `ψ` is convex and bounded below with
`ψ(0) ≤ n + inf ψ`, then `ψ(x) ≥ n ‖x‖_ψ + ψ(0) - 2n` for every `x`, where `‖·‖_ψ` is the gauge of
`K(ψ) = {x ; ψ(x) ≤ 2n + inf ψ}`. -/
theorem linear_growth_of_le_finrank_add_iInf {ψ : F → ℝ} (hψ : ConvexOn ℝ Set.univ ψ)
    (hbdd : BddBelow (Set.range ψ))
    (hfrad : ψ 0 ≤ (Module.finrank ℝ F : ℝ) + ⨅ y, ψ y) (x : F) :
    (Module.finrank ℝ F : ℝ) *
        gauge {y | ψ y ≤ 2 * (Module.finrank ℝ F : ℝ) + ⨅ y, ψ y} x + ψ 0 -
          2 * (Module.finrank ℝ F : ℝ) ≤ ψ x := by
  set n : ℝ := (Module.finrank ℝ F : ℝ) with hn
  set m : ℝ := ⨅ y, ψ y with hm
  set K : Set F := {y | ψ y ≤ 2 * n + m} with hK
  set t : ℝ := gauge K x with ht
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hmx : m ≤ ψ x := ciInf_le hbdd x
  by_cases ht1 : t ≤ 1
  · nlinarith [mul_le_mul_of_nonneg_left ht1 hn0]
  replace ht1 := not_le.mp ht1
  -- for `1 < l < t`, `x / l ∉ K`, and convexity gives `ψ x > ψ 0 + n l`
  have hl : ∀ l : ℝ, 1 < l → l < t → ψ 0 + n * l < ψ x := by
    intro l hl1 hlt
    have hl0 : 0 < l := lt_trans one_pos hl1
    have hnot : (l⁻¹ • x) ∉ K := by
      intro hmem
      have hx : x ∈ l • K := (Set.mem_smul_set_iff_inv_smul_mem₀ hl0.ne' K x).mpr hmem
      exact absurd (gauge_le_of_mem hl0.le hx) (not_le.mpr hlt)
    have hgt : 2 * n + m < ψ (l⁻¹ • x) := not_le.mp hnot
    have hconv : ψ (l⁻¹ • x) ≤ (1 - l⁻¹) * ψ 0 + l⁻¹ * ψ x := by
      have hinv0 : 0 ≤ l⁻¹ := inv_nonneg.mpr hl0.le
      have hinv1 : l⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl1.le
      have h := hψ.2 (Set.mem_univ (0 : F)) (Set.mem_univ x) (sub_nonneg.mpr hinv1) hinv0
        (by ring)
      simpa [smul_eq_mul] using h
    have hkey : n < l⁻¹ * (ψ x - ψ 0) := by nlinarith
    have hmul := mul_lt_mul_of_pos_left hkey hl0
    rw [← mul_assoc, mul_inv_cancel₀ hl0.ne', one_mul] at hmul
    nlinarith
  -- let `l ↑ t`
  have hlim : ψ 0 + n * t ≤ ψ x := by
    by_contra hcon
    replace hcon := not_le.mp hcon
    set d := ψ 0 + n * t - ψ x with hd
    have hd0 : 0 < d := by linarith
    have hmid := hl ((1 + t) / 2) (by linarith) (by linarith)
    have hnpos : 0 < n := by
      by_contra hn0'
      have : n = 0 := le_antisymm (not_lt.mp hn0') hn0
      rw [this] at hmid hcon
      linarith
    set l := max ((1 + t) / 2) (t - d / (2 * n)) with hl_def
    have hl1 : 1 < l := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hlt : l < t := max_lt (by linarith) (by
      have : 0 < d / (2 * n) := div_pos hd0 (by linarith)
      linarith)
    have hbound := hl l hl1 hlt
    have hge : n * (t - d / (2 * n)) ≤ n * l := mul_le_mul_of_nonneg_left (le_max_right _ _) hn0
    have heq : n * (t - d / (2 * n)) = n * t - d / 2 := by field_simp
    linarith
  nlinarith

end Conditional

/-- **Klartag arXiv:1309.2767v1, Lemma 2.2**: a centered convex `ψ` satisfies
`ψ(x) ≥ n ‖x‖_ψ + ψ(0) - 2n` for every `x`, with `‖·‖_ψ` the gauge of
`K(ψ) = {x ; ψ(x) ≤ 2n + inf ψ}`. -/
theorem linear_growth_of_centered (m : Measure E) [m.IsAddHaarMeasure] {ψ : E → ℝ}
    (hψ : ConvexOn ℝ univ ψ) (hnorm : ∫ x, Real.exp (-ψ x) ∂m = 1)
    (hbar : ∫ x, Real.exp (-ψ x) • x ∂m = 0) (x : E) :
    (Module.finrank ℝ E : ℝ) *
        gauge {y | ψ y ≤ 2 * (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y} x + ψ 0 -
          2 * (Module.finrank ℝ E : ℝ) ≤ ψ x :=
  have h := le_finrank_add_iInf_of_centered m hψ hnorm hbar
  linear_growth_of_le_finrank_add_iInf hψ h.1 h.2 x

end FunctionalInequalities.Probability.MomentMeasure

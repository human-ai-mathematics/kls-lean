import FunctionalInequalities.KLS.LogConcave.Density.Bounds
import FunctionalInequalities.Analysis.Convex.LipschitzEnvelope
import FunctionalInequalities.Analysis.Mollification.Convex
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Smooth log-concave approximation from below in density

Let `ν = ρ · m` be a probability law on a finite-dimensional real inner product space `V` with a
Borell density `ρ` (`IsBorellDensity`) relative to an additive Haar measure `m`, and with an
exponential moment `∫ e^{t ‖x‖} dν < ∞` (`t > 0`). This module constructs smooth finite convex
potentials `W_k` with

* `ρ ≤ e^{-W_k}` everywhere (domination **from below in density**: `ν ≤ Z_k · m.tilted (-W_k)`
  with `Z_k = ∫ e^{-W_k} dm`, `Z_k ≥ 1`), precisely
  `ofReal Z_k • m.tilted (-W_k) = ν + m.withDensity (e^{-W_k} - ρ)`;
* `Z_k → 1`;
* a uniform bound on the second moments of the laws `m.tilted (-W_k)`.

Construction (Barthe–Klartag, Proposition 10, approximation step, as used for Letwin
arXiv:2607.24164v1, Proposition 2.8):

1. **Tail bound** (`IsBorellDensity.exists_le_mul_exp_neg_norm`): `ρ(x) ≤ B e^{-(t/2)‖x‖}`.
   Log-concavity gives `ρ(x) ≤ K ρ(z)` on a ball of radius `r/2` around `(x + a)/2`, where
   `ρ ≥ b₀ > 0` on `B(a, r)`; integrating, `ρ(x) ≤ K ν(B((x+a)/2, r/2)) / m(B(0, r/2))`, and
   Markov's inequality for `e^{t‖·‖}` bounds the ball mass.
2. **Lipschitz envelope**: `W^L(x) = inf_{ρ(y) > 0} (-log ρ(y) + L ‖x - y‖)` is convex,
   `L`-Lipschitz, `≤ -log ρ` on `{ρ > 0}`, `≥ (t/2)‖x‖ - log B` for `L ≥ t/2`, and
   `e^{-W^L} → ρ` pointwise as `L → ∞` by upper semicontinuity of `ρ`.
3. **Mollification**: `W_k = ρ_{s_k} ⋆ W^{L_k} - L_k s_k` with `L_k s_k = 1/(k+1)`, so
   `W^{L_k} - 2/(k+1) ≤ W_k ≤ W^{L_k}`, `W_k` is `C^∞` and convex.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Convolution ContDiff

namespace FunctionalInequalities.KLS

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Integrability

/-- `(1 + ‖x‖)^k e^{-a ‖x‖}` is integrable for every additive Haar measure, `a > 0`, `k ∈ ℕ`. -/
private theorem integrable_one_add_norm_pow_mul_exp_neg (m : Measure V) [m.IsAddHaarMeasure] {a : ℝ}
    (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : V => (1 + ‖x‖) ^ k * Real.exp (-a * ‖x‖)) m := by
  set N : ℕ := Module.finrank ℝ V + 1 with hN
  set C : ℝ := ((k + N).factorial : ℝ) * Real.exp a / a ^ (k + N) with hC
  have hint : Integrable (fun x : V => C * (1 + ‖x‖) ^ (-(N : ℝ))) m :=
    (integrable_one_add_norm (μ := m) (by rw [hN]; push_cast; linarith)).const_mul C
  refine hint.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  set s : ℝ := ‖x‖
  have hs : 0 ≤ s := norm_nonneg x
  have h1s : 0 < 1 + s := by linarith
  have hexp := Real.pow_div_factorial_le_exp (x := a * (1 + s)) (by positivity) (k + N)
  have hfac : (0 : ℝ) < (k + N).factorial := by exact_mod_cast Nat.factorial_pos _
  have hpow : (1 + s) ^ (k + N) * a ^ (k + N) ≤
      ((k + N).factorial : ℝ) * (Real.exp a * Real.exp (a * s)) := by
    rw [← Real.exp_add, show a + a * s = a * (1 + s) by ring, ← mul_pow, mul_comm (1 + s) a]
    rw [div_le_iff₀ hfac] at hexp
    linarith
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg h1s.le, Real.rpow_natCast]
  have hN0 : 0 < (1 + s) ^ N := by positivity
  rw [hC, ← div_eq_mul_inv, le_div_iff₀ hN0]
  have hsplit : (1 + s) ^ k * Real.exp (-a * s) * (1 + s) ^ N =
      (1 + s) ^ (k + N) * Real.exp (-(a * s)) := by
    rw [pow_add, neg_mul]; ring
  rw [hsplit, le_div_iff₀ (by positivity)]
  have he : Real.exp (-(a * s)) * Real.exp (a * s) = 1 := by
    rw [← Real.exp_add]; simp
  calc (1 + s) ^ (k + N) * Real.exp (-(a * s)) * a ^ (k + N)
      = ((1 + s) ^ (k + N) * a ^ (k + N)) * Real.exp (-(a * s)) := by ring
    _ ≤ (((k + N).factorial : ℝ) * (Real.exp a * Real.exp (a * s))) * Real.exp (-(a * s)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = ((k + N).factorial : ℝ) * Real.exp a * (Real.exp (-(a * s)) * Real.exp (a * s)) := by
        ring
    _ = ((k + N).factorial : ℝ) * Real.exp a := by rw [he, mul_one]

end Integrability

namespace IsBorellDensity

variable {ν : ProbabilityMeasure V} {m : Measure V} [m.IsAddHaarMeasure] {ρ : V → ℝ}

/-- **Exponential tail of a Borell density**: if `ν = ρ · m` has a Borell density and
`∫ e^{t‖x‖} dν < ∞` with `t > 0`, then `ρ(x) ≤ B e^{-(t/2) ‖x‖}` for some `B > 0`. -/
theorem exists_le_mul_exp_neg_norm (h : IsBorellDensity (ν : Measure V) m ρ) {t : ℝ}
    (ht : 0 < t) (hexp : Integrable (fun x => Real.exp (t * ‖x‖)) (ν : Measure V)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, ρ x ≤ B * Real.exp (-(t / 2) * ‖x‖) := by
  obtain ⟨a, r, b₀, hr, hb₀, hball⟩ := h.exists_ball_le
  obtain ⟨M, hM⟩ := h.exists_le
  have hM0 : 0 ≤ M := (h.nonneg a).trans (hM a)
  set K : ℝ := (M / b₀) ^ ((1 - 1 / 2) / (1 / 2) : ℝ) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (div_nonneg hM0 hb₀.le) _
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  set V₀ : ℝ := m.real (ball (0 : V) (r / 2)) with hV₀
  have hV₀pos : 0 < V₀ := by
    rw [hV₀, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos m 0 hr2).ne' measure_ball_lt_top.ne
  set I : ℝ := ∫ x, Real.exp (t * ‖x‖) ∂(ν : Measure V) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => (Real.exp_pos _).le
  -- the local comparison, integrated over the ball
  have hloc : ∀ x : V, ρ x * V₀ ≤
      K * (ν : Measure V).real (ball ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • a) (r / 2)) := by
    intro x
    set c : V := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • a with hc
    have hpt : ∀ z ∈ ball c (r / 2), ρ x ≤ K * ρ z := by
      intro z hz
      set b : V := (2 : ℝ) • z - x with hb
      have hbmem : b ∈ ball a r := by
        rw [mem_ball, dist_eq_norm] at hz ⊢
        have hbe : b - a = (2 : ℝ) • (z - c) := by rw [hb, hc]; module
        rw [hbe, norm_smul]
        simp only [Real.norm_ofNat]
        linarith
      exact h.le_rpow_mul_of_combination (by norm_num) (by norm_num) hb₀ hM (hball b hbmem)
        (by rw [hb]; module)
    have hcball : m (ball c (r / 2)) = m (ball (0 : V) (r / 2)) :=
      Measure.addHaar_ball_center m c (r / 2)
    have hint : ENNReal.ofReal (ρ x) * m (ball c (r / 2)) ≤
        ENNReal.ofReal K * (ν : Measure V) (ball c (r / 2)) := by
      rw [← h.withDensity_eq, withDensity_apply _ isOpen_ball.measurableSet,
        ← lintegral_const_mul _ h.measurable.ennreal_ofReal, ← setLIntegral_const]
      refine setLIntegral_mono (measurable_const.mul h.measurable.ennreal_ofReal) fun z hz => ?_
      rw [← ENNReal.ofReal_mul hK0]
      exact ENNReal.ofReal_le_ofReal (hpt z hz)
    have hfin : (ν : Measure V) (ball c (r / 2)) ≠ ⊤ := measure_ne_top _ _
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hint
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (h.nonneg x),
      ENNReal.toReal_ofReal hK0, hcball, ← measureReal_def, ← measureReal_def] at hreal
  -- Markov's inequality for the exponential moment
  have hmarkov : ∀ c : V, Real.exp (t * (‖c‖ - r / 2)) * (ν : Measure V).real (ball c (r / 2)) ≤ I := by
    intro c
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := (ν : Measure V))
      (Eventually.of_forall fun x => (Real.exp_pos (t * ‖x‖)).le) hexp
      (Real.exp (t * (‖c‖ - r / 2)))
    refine le_trans ?_ hm
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine measureReal_mono (fun z hz => ?_) (measure_ne_top _ _)
    simp only [Set.mem_ofPred_eq]
    apply Real.exp_le_exp.mpr
    rw [mem_ball, dist_eq_norm] at hz
    have := norm_sub_norm_le c z
    rw [norm_sub_rev] at hz
    nlinarith
  refine ⟨K * I / V₀ * Real.exp (t * r / 2 + t * ‖a‖ / 2) + 1, by positivity, fun x => ?_⟩
  set c : V := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • a with hc
  have h1 := hloc x
  have h2 := hmarkov c
  have hcnorm : ‖x‖ / 2 - ‖a‖ / 2 ≤ ‖c‖ := by
    have := norm_sub_le c ((1 / 2 : ℝ) • a)
    rw [show c - (1 / 2 : ℝ) • a = (1 / 2 : ℝ) • x by rw [hc]; abel, norm_smul, norm_smul] at this
    simp only [one_div, norm_inv, Real.norm_ofNat] at this
    linarith
  have hexpc : Real.exp (-(t * (‖c‖ - r / 2))) ≤
      Real.exp (t * r / 2 + t * ‖a‖ / 2) * Real.exp (-(t / 2) * ‖x‖) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hball_le : (ν : Measure V).real (ball c (r / 2)) ≤ I * Real.exp (-(t * (‖c‖ - r / 2))) := by
    have hepos := Real.exp_pos (t * (‖c‖ - r / 2))
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hepos]
    linarith
  have hρ : ρ x ≤ K * I / V₀ * Real.exp (-(t * (‖c‖ - r / 2))) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hV₀pos]
    calc ρ x * V₀ ≤ K * (ν : Measure V).real (ball c (r / 2)) := h1
      _ ≤ K * (I * Real.exp (-(t * (‖c‖ - r / 2)))) := mul_le_mul_of_nonneg_left hball_le hK0
      _ = K * I * Real.exp (-(t * (‖c‖ - r / 2))) := by ring
  calc ρ x ≤ K * I / V₀ * Real.exp (-(t * (‖c‖ - r / 2))) := hρ
    _ ≤ K * I / V₀ * (Real.exp (t * r / 2 + t * ‖a‖ / 2) * Real.exp (-(t / 2) * ‖x‖)) :=
        mul_le_mul_of_nonneg_left hexpc (by positivity)
    _ ≤ (K * I / V₀ * Real.exp (t * r / 2 + t * ‖a‖ / 2) + 1) * Real.exp (-(t / 2) * ‖x‖) := by
        nlinarith [Real.exp_pos (-(t / 2) * ‖x‖)]

end IsBorellDensity

section Envelope

/-! ### The Lipschitz envelope of `-log ρ` -/

open Analysis

/-- The envelope `inf_{ρ(y) > 0} (-log ρ(y) + L ‖x - y‖)` of the potential of `ρ`. -/
private def env (ρ : V → ℝ) (L : ℝ) : V → ℝ :=
  lipschitzEnvelope {y | 0 < ρ y} (fun y => -Real.log (ρ y)) L

variable {ν : ProbabilityMeasure V} {m : Measure V} [m.IsAddHaarMeasure] {ρ : V → ℝ}

/-- The data of the potential `-log ρ` on `{ρ > 0}` used by the envelope. -/
private theorem potential_data (h : IsBorellDensity (ν : Measure V) m ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) {a B : ℝ} (hB : 0 < B) (htail : ∀ x, ρ x ≤ B * Real.exp (-a * ‖x‖)) :
    {y | 0 < ρ y}.Nonempty ∧ (∀ y ∈ {y | 0 < ρ y}, -Real.log M ≤ -Real.log (ρ y)) ∧
      ConvexOn ℝ {y | 0 < ρ y} (fun y => -Real.log (ρ y)) ∧
      ∀ y ∈ {y | 0 < ρ y}, a * ‖y‖ - Real.log B ≤ -Real.log (ρ y) := by
  obtain ⟨c, r, b₀, hr, hb₀, hball⟩ := h.exists_ball_le
  have hc : 0 < ρ c := lt_of_lt_of_le hb₀ (hball c (mem_ball_self hr))
  refine ⟨⟨c, hc⟩, fun y hy => ?_, h.concaveOn_log.neg, fun y hy => ?_⟩
  · have hy' : 0 < ρ y := hy
    exact neg_le_neg (Real.log_le_log hy' (hM y))
  · have hy' : 0 < ρ y := hy
    have hle := Real.log_le_log hy' (htail y)
    rw [Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp] at hle
    linarith

/-- **Pointwise convergence of the envelopes**: `e^{-W^L(x)} → ρ(x)` as `L → ∞`, at every
point, by upper semicontinuity of `ρ`. -/
private theorem tendsto_exp_neg_env (h : IsBorellDensity (ν : Measure V) m ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) {a B : ℝ} (hB : 0 < B) (htail : ∀ x, ρ x ≤ B * Real.exp (-a * ‖x‖))
    (x : V) : Tendsto (fun L => Real.exp (-env ρ L x)) atTop (𝓝 (ρ x)) := by
  obtain ⟨hD, hb, -, -⟩ := potential_data h hM hB htail
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- upper semicontinuity: `ρ < ρ x + ε/2` near `x`
  have husc := h.upperSemicontinuous x (ρ x + ε / 2) (by linarith)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp husc
  set c : ℝ := -Real.log (ρ x + ε / 2) with hcdef
  have hρx := h.nonneg x
  refine ⟨max 0 ((c + Real.log M) / δ), fun L hL => ?_⟩
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hLδ : c - -Real.log M ≤ L * δ := by
    have := (le_max_right _ _).trans hL
    rw [div_le_iff₀ hδ] at this
    linarith
  have hge : c ≤ env ρ L x := by
    refine lipschitzEnvelope.ge_of_ge_on_ball hD hb (δ := δ) (fun y hy hxy => ?_) hLδ hL0
    have hy' : 0 < ρ y := hy
    have hlt : ρ y < ρ x + ε / 2 := hδball (by rw [dist_comm, dist_eq_norm]; exact hxy)
    exact neg_le_neg (Real.log_le_log hy' hlt.le)
  have hupper : Real.exp (-env ρ L x) ≤ ρ x + ε / 2 := by
    calc Real.exp (-env ρ L x) ≤ Real.exp (-c) := Real.exp_le_exp.mpr (by linarith)
      _ = ρ x + ε / 2 := by rw [hcdef, neg_neg, Real.exp_log (by linarith)]
  have hlower : ρ x ≤ Real.exp (-env ρ L x) := by
    rcases hρx.eq_or_lt with h0 | hpos
    · rw [← h0]; exact (Real.exp_pos _).le
    · have hle := lipschitzEnvelope.le_self hL0 hb (show x ∈ {y | 0 < ρ y} from hpos)
      calc ρ x = Real.exp (-(-Real.log (ρ x))) := by rw [neg_neg, Real.exp_log hpos]
        _ ≤ Real.exp (-env ρ L x) := Real.exp_le_exp.mpr (by
            change env ρ L x ≤ -Real.log (ρ x) at hle; linarith)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Envelope

section Smoothing

/-! ### Mollified envelopes -/

open Analysis

/-- The Lipschitz constant `L_k = a + k + 1`. -/
private def lipConst (a : ℝ) (k : ℕ) : ℝ := a + k + 1

/-- The mollification radius `s_k = 1 / ((k + 1) L_k)`, so that `L_k s_k = 1/(k+1)`. -/
private def radius (a : ℝ) (k : ℕ) : ℝ := 1 / (((k : ℝ) + 1) * lipConst a k)

private theorem lipConst_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < lipConst a k := by
  unfold lipConst; positivity

private theorem radius_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < radius a k := by
  have := lipConst_pos ha k
  unfold radius; positivity

private theorem lipConst_mul_radius {a : ℝ} (ha : 0 < a) (k : ℕ) :
    lipConst a k * radius a k = 1 / ((k : ℝ) + 1) := by
  have := lipConst_pos ha k
  unfold radius
  field_simp

/-- The bump of radius `s_k`. -/
private def bump {a : ℝ} (ha : 0 < a) (k : ℕ) : ContDiffBump (0 : V) :=
  ⟨radius a k / 2, radius a k, half_pos (radius_pos ha k), half_lt_self (radius_pos ha k)⟩

/-- The smooth convex approximating potential `W_k = ρ_{s_k} ⋆ W^{L_k} - 1/(k+1)`. -/
private def smoothPotential (m : Measure V) (ρ : V → ℝ) {a : ℝ} (ha : 0 < a) (k : ℕ) : V → ℝ :=
  fun x => ((bump ha k).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] env ρ (lipConst a k)) x -
    1 / ((k : ℝ) + 1)

variable {ν : ProbabilityMeasure V} {m : Measure V} [m.IsAddHaarMeasure] {ρ : V → ℝ}

/-- Properties of the mollified envelopes. -/
private theorem smoothPotential_spec (h : IsBorellDensity (ν : Measure V) m ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (htail : ∀ x, ρ x ≤ B * Real.exp (-a * ‖x‖)) (k : ℕ) :
    ContDiff ℝ ∞ (smoothPotential m ρ ha k) ∧ ConvexOn ℝ univ (smoothPotential m ρ ha k) ∧
      (∀ x, smoothPotential m ρ ha k x ≤ env ρ (lipConst a k) x) ∧
      (∀ x, env ρ (lipConst a k) x - 2 / ((k : ℝ) + 1) ≤ smoothPotential m ρ ha k x) ∧
      ∀ x, a * ‖x‖ - Real.log B ≤ env ρ (lipConst a k) x := by
  obtain ⟨hD, hb, hconv, hgrow⟩ := potential_data h hM hB htail
  have hL := lipConst_pos ha k
  have hcont : Continuous (env ρ (lipConst a k)) := lipschitzEnvelope.continuous hD hL.le hb
  have herr (x : V) : |((bump ha k).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m]
      env ρ (lipConst a k)) x - env ρ (lipConst a k) x| ≤ 1 / ((k : ℝ) + 1) := by
    have := Mollification.abs_normed_convolution_sub_le m (bump ha k) hcont hL.le
      (fun x y => by
        have := lipschitzEnvelope.dist_le hD hL.le hb x y
        rwa [Real.dist_eq, dist_eq_norm] at this) x
    rwa [show (bump ha k).rOut = radius a k from rfl, lipConst_mul_radius ha k] at this
  refine ⟨(Mollification.contDiff_normed_convolution m (bump ha k) hcont).sub contDiff_const,
    ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have hc := Mollification.convexOn_normed_convolution m (bump ha k) hcont
      (lipschitzEnvelope.convexOn hD hL.le hb hconv)
    exact hc.sub (concaveOn_const _ convex_univ)
  · have := (abs_le.mp (herr x)).2
    simp only [smoothPotential]
    linarith
  · have := (abs_le.mp (herr x)).1
    simp only [smoothPotential]
    have h2 : 2 / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by ring
    linarith
  · have hak : a ≤ lipConst a k := by
      unfold lipConst; have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
    exact lipschitzEnvelope.ge_mul_norm_sub hD ha.le hak hgrow x

end Smoothing

section Approximation

open Analysis

variable {ν : ProbabilityMeasure V} {m : Measure V} [m.IsAddHaarMeasure] {ρ : V → ℝ}

/-- **Smooth convex approximation from below in density** (Barthe–Klartag, Proposition 10,
approximation step; Letwin arXiv:2607.24164v1, Proposition 2.8). Let `ν = ρ · m` have a Borell
density relative to an additive Haar measure `m` and an exponential moment
`∫ e^{t ‖x‖} dν < ∞`, `t > 0`. There are `C^∞` convex finite potentials `W_k` such that, with
`Z_k = ∫ e^{-W_k} dm`:

* `e^{-W_k}` is `m`-integrable and dominates `ρ` pointwise, so `1 ≤ Z_k`;
* `Z_k → 1`;
* `Z_k · m.tilted (-W_k) = ν + m.withDensity (e^{-W_k} - ρ)`, i.e. the normalized laws
  `λ_k = m.tilted (-W_k)` dominate `ν / Z_k` from below;
* the laws `λ_k` have finite second moments bounded by one constant `C₂`. -/
theorem IsBorellDensity.exists_smooth_convex_lower_approximation
    (h : IsBorellDensity (ν : Measure V) m ρ) {t : ℝ} (ht : 0 < t)
    (hexp : Integrable (fun x => Real.exp (t * ‖x‖)) (ν : Measure V)) :
    ∃ (W : ℕ → V → ℝ) (C₂ : ℝ),
      (∀ k, ContDiff ℝ ∞ (W k)) ∧ (∀ k, ConvexOn ℝ univ (W k)) ∧
      (∀ k, Integrable (fun x => Real.exp (-W k x)) m) ∧
      (∀ k x, ρ x ≤ Real.exp (-W k x)) ∧
      (∀ k, 1 ≤ ∫ x, Real.exp (-W k x) ∂m) ∧
      Tendsto (fun k => ∫ x, Real.exp (-W k x) ∂m) atTop (𝓝 1) ∧
      (∀ k, ENNReal.ofReal (∫ x, Real.exp (-W k x) ∂m) • m.tilted (-W k) =
        (ν : Measure V) + m.withDensity (fun x => ENNReal.ofReal (Real.exp (-W k x) - ρ x))) ∧
      ∀ k, Integrable (fun x => ‖x‖ ^ 2) (m.tilted (-W k)) ∧
        ∫ x, ‖x‖ ^ 2 ∂(m.tilted (-W k)) ≤ C₂ := by
  obtain ⟨B, hB, htail'⟩ := h.exists_le_mul_exp_neg_norm ht hexp
  set a : ℝ := t / 2 with hadef
  have ha : 0 < a := by positivity
  have htail : ∀ x, ρ x ≤ B * Real.exp (-a * ‖x‖) := htail'
  obtain ⟨M, hM⟩ := h.exists_le
  obtain ⟨hD, hb, -, -⟩ := potential_data h hM hB htail
  set W : ℕ → V → ℝ := smoothPotential m ρ ha with hW
  have spec := smoothPotential_spec h hM ha hB htail
  -- pointwise bounds
  have hdom : ∀ k x, Real.exp (-W k x) ≤ Real.exp 2 * B * Real.exp (-a * ‖x‖) := by
    intro k x
    obtain ⟨-, -, -, hge, hgrow⟩ := spec k
    have h1 := hge x
    have h2 := hgrow x
    have hk : 2 / ((k : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      nlinarith
    calc Real.exp (-W k x) ≤ Real.exp (2 + Real.log B + -a * ‖x‖) :=
          Real.exp_le_exp.mpr (by simp only [hW]; nlinarith)
      _ = Real.exp 2 * B * Real.exp (-a * ‖x‖) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hB]
  have hlow : ∀ k x, ρ x ≤ Real.exp (-W k x) := by
    intro k x
    rcases (h.nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0]; exact (Real.exp_pos _).le
    · obtain ⟨-, -, hle, -, -⟩ := spec k
      have hle2 := lipschitzEnvelope.le_self (lipConst_pos ha k).le hb
        (show x ∈ {y | 0 < ρ y} from hpos)
      change env ρ (lipConst a k) x ≤ -Real.log (ρ x) at hle2
      calc ρ x = Real.exp (-(-Real.log (ρ x))) := by rw [neg_neg, Real.exp_log hpos]
        _ ≤ Real.exp (-W k x) := Real.exp_le_exp.mpr (by linarith [hle x])
  have hlim : ∀ x, Tendsto (fun k => Real.exp (-W k x)) atTop (𝓝 (ρ x)) := by
    intro x
    have hL : Tendsto (fun k : ℕ => lipConst a k) atTop atTop := by
      unfold lipConst
      exact tendsto_atTop_add_const_right _ 1
        (tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop)
    have hg := (tendsto_exp_neg_env h hM hB htail x).comp hL
    have he : Tendsto (fun k : ℕ => Real.exp (2 * (1 / ((k : ℝ) + 1)))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
      have := (Real.continuous_exp.tendsto 0).comp h0
      rwa [Real.exp_zero] at this
    have hup := he.mul hg
    rw [one_mul] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg hup (fun k => ?_) (fun k => ?_)
    · obtain ⟨-, -, hle, -, -⟩ := spec k
      exact Real.exp_le_exp.mpr (by linarith [hle x])
    · obtain ⟨-, -, -, hge, -⟩ := spec k
      simp only [Function.comp]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := hge x
      have h2 : 2 / ((k : ℝ) + 1) = 2 * (1 / ((k : ℝ) + 1)) := by ring
      linarith
  -- integrability
  have hbound : Integrable (fun x : V => Real.exp 2 * B * Real.exp (-a * ‖x‖)) m := by
    refine ((integrable_one_add_norm_pow_mul_exp_neg m ha 0).const_mul (Real.exp 2 * B)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [pow_zero, one_mul]
  have hcontW : ∀ k, Continuous (W k) := fun k => (spec k).1.continuous
  have hint : ∀ k, Integrable (fun x => Real.exp (-W k x)) m := by
    intro k
    refine hbound.mono' ((Real.continuous_exp.comp (hcontW k).neg).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hdom k x
  have hρint : Integrable ρ m :=
    (hint 0).mono' h.measurable.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (h.nonneg x)]; exact hlow 0 x)
  have hρone : ∫ x, ρ x ∂m = 1 := by
    have hlin : ∫⁻ x, ENNReal.ofReal (ρ x) ∂m = 1 := by
      have h1 := congrArg (fun μ : Measure V => μ univ) h.withDensity_eq
      simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        measure_univ] at h1
      exact h1
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h.nonneg)
      h.measurable.aestronglyMeasurable, hlin, ENNReal.toReal_one]
  have hZ1 : ∀ k, 1 ≤ ∫ x, Real.exp (-W k x) ∂m := fun k => by
    rw [← hρone]; exact integral_mono hρint (hint k) (hlow k)
  refine ⟨W, ∫ x, Real.exp 2 * B * ((1 + ‖x‖) ^ 2 * Real.exp (-a * ‖x‖)) ∂m,
    fun k => (spec k).1, fun k => (spec k).2.1, hint, hlow, hZ1, ?_, fun k => ?_, fun k => ?_⟩
  · rw [← hρone]
    refine tendsto_integral_of_dominated_convergence _
      (fun k => (Real.continuous_exp.comp (hcontW k).neg).aestronglyMeasurable) hbound
      (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall hlim)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hdom k x
  · have hZpos : 0 < ∫ x, Real.exp (-W k x) ∂m := lt_of_lt_of_le one_pos (hZ1 k)
    rw [Measure.tilted, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top, ← h.withDensity_eq,
      ← withDensity_add_left h.measurable.ennreal_ofReal]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.neg_apply]
    rw [← ENNReal.ofReal_mul hZpos.le, mul_div_cancel₀ _ hZpos.ne',
      ← ENNReal.ofReal_add (h.nonneg x) (sub_nonneg.mpr (hlow k x)), add_sub_cancel]
  · have hZ := hZ1 k
    have hZpos : 0 < ∫ x, Real.exp (-W k x) ∂m := lt_of_lt_of_le one_pos hZ
    have hbound2 : Integrable (fun x : V => Real.exp 2 * B * ((1 + ‖x‖) ^ 2 *
        Real.exp (-a * ‖x‖))) m :=
      (integrable_one_add_norm_pow_mul_exp_neg m ha 2).const_mul _
    have hpt : ∀ x : V, Real.exp (-W k x) * ‖x‖ ^ 2 ≤
        Real.exp 2 * B * ((1 + ‖x‖) ^ 2 * Real.exp (-a * ‖x‖)) := by
      intro x
      have hsq : ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
      calc Real.exp (-W k x) * ‖x‖ ^ 2
          ≤ (Real.exp 2 * B * Real.exp (-a * ‖x‖)) * (1 + ‖x‖) ^ 2 :=
            mul_le_mul (hdom k x) hsq (sq_nonneg _) (by positivity)
        _ = _ := by ring
    have hmeas2 : AEStronglyMeasurable (fun x : V => Real.exp (-W k x) * ‖x‖ ^ 2) m :=
      ((Real.continuous_exp.comp (hcontW k).neg).mul (continuous_norm.pow 2)).aestronglyMeasurable
    have hi2 : Integrable (fun x : V => Real.exp (-W k x) * ‖x‖ ^ 2) m :=
      hbound2.mono' hmeas2 (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpt x)
    refine ⟨(integrable_tilted_iff (hint k) _).mpr ?_, ?_⟩
    · simpa only [Pi.neg_apply, smul_eq_mul] using hi2
    · rw [integral_tilted]
      refine integral_mono ?_ hbound2 fun x => ?_
      · refine (hi2.div_const (∫ x, Real.exp (-W k x) ∂m)).congr
          (Eventually.of_forall fun x => ?_)
        simp only [Pi.neg_apply, smul_eq_mul]
        ring
      · simp only [Pi.neg_apply, smul_eq_mul]
        have h1 : Real.exp (-W k x) / (∫ x, Real.exp (-W k x) ∂m) ≤ Real.exp (-W k x) :=
          div_le_self (Real.exp_pos _).le hZ
        calc Real.exp (-W k x) / (∫ x, Real.exp (-W k x) ∂m) * ‖x‖ ^ 2
            ≤ Real.exp (-W k x) * ‖x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
          _ ≤ _ := hpt x

end Approximation

end FunctionalInequalities.KLS

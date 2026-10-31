module

public import FunctionalInequalities.KLS.Klartag.LinearGrowth
public import FunctionalInequalities.Probability.Line.Haar
public import FunctionalInequalities.Probability.ExponentialMoments.Norm
public import FunctionalInequalities.Probability.Line.ExpIntegral
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Two-sided linear bounds for centered convex potentials

Klartag, *Logarithmically-concave moment measures I*, arXiv:1309.2767v1, Lemma 2.3. Let `L, ε > 0`
and let `ψ : E → ℝ` be convex, `L`-Lipschitz and centered (Klartag (7): `∫ e^{-ψ} = 1` and
`∫ x e^{-ψ(x)} dx = 0` for an additive Haar measure) with the nondegeneracy condition (13)
`∫ |⟪∇ψ, θ⟫| e^{-ψ} ≥ ε` for every unit `θ`. Then `α‖x‖ - β ≤ ψ(x) ≤ L‖x‖ + γ` with
`α, β, γ > 0` depending only on `L`, `ε`, the dimension and the Haar measure
(`MomentMeasure.exists_two_sided_linear_bounds`).

The intermediate statements of Klartag's proof are stated separately:
* (15): Fubini along the lines parallel to `θ` and the one-dimensional identity
  `∫ |g'| e^{-g} = 2 e^{-inf g}` give
  `c ∫ |⟪∇ψ, θ⟫| e^{-ψ} = ∫_{θ^⊥} 2 e^{-inf_s ψ(z + sθ)} dz`, with the Fubini constant `c` of
  `Probability.exists_lintegral_line` (`Probability.Line.lintegral_abs_deriv_mul_exp_neg_eq`,
  `MomentMeasure.exists_lintegral_line_abs_inner_gradient`);
* (17)–(18): if `ψ(tθ) ≤ 2n + inf ψ`, convexity gives
  `∫ e^{-ψ(z/2 + sθ)} ds ≥ ½ e^{-2n} |t| e^{-inf_s ψ(z + sθ)}` on every line
  (`MomentMeasure.lintegral_line_half_ge`);
* (19)–(20): hence `|t| ≤ 2^{n+1} e^{2n} / ε`, so `K(ψ) = {ψ ≤ 2n + inf ψ}` lies in a ball of
  radius `2^{n+1} e^{2n} / ε` (`MomentMeasure.abs_le_of_mem_levelSet_of_centered`).
The lower bound then follows from Lemma 2.2 in the convexity form of
`KLS/Klartag/LinearGrowth.lean`, and integrability bounds `ψ(0)` above and below.

Scope: `ψ` is assumed `C¹` (the paper allows any Lipschitz convex `ψ`, with `∇ψ` defined almost
everywhere); this is an added restriction. The constants are explicit in the proof but only their
existence is stated.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section LineConvexity

/-! Convex functions along the lines `s ↦ z + s θ`; no measure on `E`. -/

private theorem line_tendsto_pair_of_compact_sublevel {ψ : E → ℝ}
    (hcompact : ∀ b : ℝ, IsCompact {x : E | ψ x ≤ b}) {θ : E} (hθ : ‖θ‖ = 1) (z : E) :
    Tendsto (fun s : ℝ => ψ (z + s • θ)) atTop atTop ∧
      Tendsto (fun s : ℝ => ψ (z + s • θ)) atBot atTop := by
  have hθ0 : θ ≠ 0 := fun h => by simp [h] at hθ
  have hψ : Tendsto ψ (cocompact E) atTop :=
    tendsto_atTop.2 fun b =>
      mem_cocompact.2 ⟨_, hcompact b, fun x (hx : ¬ψ x ≤ b) => (not_le.1 hx).le⟩
  have hline : Tendsto (fun s : ℝ => z + s • θ) (cocompact ℝ) (cocompact E) :=
    ((Homeomorph.addLeft z).isClosedEmbedding.comp
        (isClosedEmbedding_smul_left hθ0)).tendsto_cocompact
  exact
    ⟨(hψ.comp hline).mono_left atTop_le_cocompact, (hψ.comp hline).mono_left atBot_le_cocompact⟩

private theorem line_segment_bound {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ)
    {θ : E} {t c : ℝ} (hzero : ψ 0 ≤ c) (ht : ψ (t • θ) ≤ c)
    {r : ℝ} (hr : r ∈ Icc (min 0 t) (max 0 t)) :
    ψ (r • θ) ≤ c := by
  by_cases ht0 : t = 0
  · have hr0 : r = 0 := by simpa [ht0] using hr
    simpa [hr0] using hzero
  have hlam : 0 ≤ r / t ∧ r / t ≤ 1 := by
    rcases lt_or_gt_of_ne ht0 with htneg | htpos
    · have hh : t ≤ r ∧ r ≤ 0 := by
        simpa [min_eq_right htneg.le, max_eq_left htneg.le] using hr
      constructor
      · apply (le_div_iff_of_neg htneg).2
        linarith [hh.2]
      · apply (div_le_iff_of_neg htneg).2
        linarith [hh.1]
    · have hh : 0 ≤ r ∧ r ≤ t := by
        simpa [min_eq_left htpos.le, max_eq_right htpos.le] using hr
      constructor
      · exact div_nonneg hh.1 htpos.le
      · apply (div_le_iff₀ htpos).2
        simpa using hh.2
  have hid :
      (1 - r / t) • (0 : E) + (r / t) • (t • θ) = r • θ := by
    simp only [smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ ht0]
  have hc := hψ.2 (mem_univ (0 : E)) (mem_univ (t • θ))
    (show 0 ≤ 1 - r / t by linarith) hlam.1
    (show (1 - r / t) + r / t = 1 by ring)
  rw [hid] at hc
  simp only [smul_eq_mul] at hc
  calc
    ψ (r • θ) ≤ (1 - r / t) * ψ 0 + (r / t) * ψ (t • θ) := hc
    _ ≤ (1 - r / t) * c + (r / t) * c :=
      add_le_add
        (mul_le_mul_of_nonneg_left hzero (by linarith [hlam.2]))
        (mul_le_mul_of_nonneg_left ht hlam.1)
    _ = c := by ring

private theorem lintegral_line_half_ge_at_point {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hbdd : BddBelow (range ψ)) {n : ℝ} (hn : 0 ≤ n) (hzero : ψ 0 ≤ 2 * n + ⨅ y, ψ y) {θ : E}
    {t : ℝ} (ht : ψ (t • θ) ≤ 2 * n + ⨅ y, ψ y) (z : E) (s₀ : ℝ) :
    ENNReal.ofReal (|t| * Real.exp (-2 * n) / 2 * Real.exp (-ψ (z + s₀ • θ))) ≤
      ∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-ψ ((1 / 2 : ℝ) • z + s • θ))) := by
  let a : ℝ := (min 0 t + s₀) / 2
  let b : ℝ := (max 0 t + s₀) / 2
  have hlen : b - a = |t| / 2 := by
    dsimp [a, b]
    rcases le_total 0 t with htpos | htneg
    · rw [min_eq_left htpos, max_eq_right htpos, abs_of_nonneg htpos]
      ring
    · rw [min_eq_right htneg, max_eq_left htneg, abs_of_nonpos htneg]
      ring
  have hmeasure : volume (Icc a b) = ENNReal.ofReal (|t| / 2) := by rw [Real.volume_Icc, hlen]
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) :
    ENNReal.ofReal (Real.exp (-2 * n) * Real.exp (-ψ (z + s₀ • θ))) ≤
      ENNReal.ofReal (Real.exp (-ψ ((1 / 2 : ℝ) • z + s • θ))) := by
    have hr : 2 * s - s₀ ∈ Icc (min 0 t) (max 0 t) := by
      change a ≤ s ∧ s ≤ b at hs
      dsimp [a, b] at hs
      constructor <;> linarith [hs.1, hs.2]
    have hseg := line_segment_bound hψ hzero ht hr
    have hid :
      (1 / 2 : ℝ) • (z + s₀ • θ) + (1 / 2 : ℝ) • ((2 * s - s₀) • θ) = (1 / 2 : ℝ) • z + s • θ := by
      have hcoef : (1 / 2 : ℝ) * s₀ + (1 / 2 : ℝ) * (2 * s - s₀) = s := by ring
      simp only [smul_add, smul_smul]
      rw [add_assoc, ← add_smul, hcoef]
    have hc :=
      hψ.2 (mem_univ (z + s₀ • θ)) (mem_univ ((2 * s - s₀) • θ))
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    rw [hid] at hc
    simp only [smul_eq_mul] at hc
    have hm : (⨅ y, ψ y) ≤ ψ (z + s₀ • θ) := ciInf_le hbdd _
    have hp : ψ ((1 / 2 : ℝ) • z + s • θ) ≤ 2 * n + ψ (z + s₀ • θ) := by linarith
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  calc
    ENNReal.ofReal (|t| * Real.exp (-2 * n) / 2 * Real.exp (-ψ (z + s₀ • θ))) =
        ∫⁻ _s in Icc a b, ENNReal.ofReal (Real.exp (-2 * n) * Real.exp (-ψ (z + s₀ • θ))) := by
      rw [lintegral_const, Measure.restrict_apply_univ, hmeasure]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ∫⁻ s in Icc a b, ENNReal.ofReal (Real.exp (-ψ ((1 / 2 : ℝ) • z + s • θ))) :=
      setLIntegral_mono' measurableSet_Icc hpoint
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-ψ ((1 / 2 : ℝ) • z + s • θ))) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_mono
      intro s
      by_cases hs : s ∈ Icc a b
      · rw [indicator_of_mem hs]
      · rw [indicator_of_notMem hs]
        exact bot_le

/-- **Klartag arXiv:1309.2767v1, (17)–(18)** on one line: if `ψ(tθ) ≤ 2n + inf ψ` and
`ψ(0) ≤ n + inf ψ`, then for every `z` (in particular `z ⊥ θ`),
`∫ e^{-ψ(z/2 + sθ)} ds ≥ ½ e^{-2n} |t| e^{-inf_s ψ(z + sθ)}`. -/
theorem lintegral_line_half_ge {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ) (hbdd : BddBelow (range ψ))
    (hfrad : ψ 0 ≤ (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y) {θ : E}
    {t : ℝ} (ht : ψ (t • θ) ≤ 2 * (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y) (z : E) :
    ENNReal.ofReal (|t| * Real.exp (-2 * (Module.finrank ℝ E : ℝ)) / 2 *
        Real.exp (-⨅ s : ℝ, ψ (z + s • θ))) ≤
      ∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-ψ ((1 / 2 : ℝ) • z + s • θ))) := by
  let n : ℝ := Module.finrank ℝ E
  let m : ℝ := ⨅ s : ℝ, ψ (z + s • θ)
  let F : ℝ → ENNReal := fun b =>
    ENNReal.ofReal (|t| * Real.exp (-2 * n) / 2 * Real.exp (-b))
  have hn : 0 ≤ n := by
    dsimp [n]
    positivity
  have hzero : ψ 0 ≤ 2 * n + ⨅ y, ψ y := by
    change ψ 0 ≤ n + ⨅ y, ψ y at hfrad
    linarith
  have hbase (s₀ : ℝ) :
      F (ψ (z + s₀ • θ)) ≤
        ∫⁻ s : ℝ, ENNReal.ofReal
          (Real.exp (-ψ ((1 / 2 : ℝ) • z + s • θ))) := by
    exact lintegral_line_half_ge_at_point hψ hbdd hn hzero ht z s₀
  have hbound (b : ℝ) (hb : m < b) :
      F b ≤ ∫⁻ s : ℝ, ENNReal.ofReal
        (Real.exp (-ψ ((1 / 2 : ℝ) • z + s • θ))) := by
    obtain ⟨s₀, hs₀⟩ := exists_lt_of_ciInf_lt hb
    have hmon : F b ≤ F (ψ (z + s₀ • θ)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hs₀.le)) (by positivity)
    exact hmon.trans (hbase s₀)
  have hF : Continuous F := by
    dsimp [F]
    exact ENNReal.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_exp.comp continuous_neg))
  have hlim : Tendsto F (𝓝[>] m) (𝓝 (F m)) :=
    hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  change F m ≤ _
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact hbound b hb

end LineConvexity

section Haar

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Klartag arXiv:1309.2767v1, (15)**, with the Fubini constant `c` of
`Probability.exists_lintegral_line`: for a convex `C¹` `ψ` with integrable `e^{-ψ}` and a unit
vector `θ`, `c ∫ |⟪∇ψ, θ⟫| e^{-ψ} = ∫_{θ^⊥} 2 e^{-inf_s ψ(z + sθ)} dz`. -/
theorem exists_lintegral_line_abs_inner_gradient (m : Measure E) [m.IsAddHaarMeasure]
    {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ) (hψ1 : ContDiff ℝ 1 ψ)
    (hint : Integrable (fun x => Real.exp (-ψ x)) m) {θ : E} (hθ : ‖θ‖ = 1) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ G : E → ENNReal, Measurable G →
        c * ∫⁻ x, G x ∂m =
          ∫⁻ z : (ℝ ∙ θ)ᗮ, ∫⁻ s : ℝ, G ((z : E) + s • θ) ∂(volume : Measure ℝ)
            ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ)) ∧
      c * ∫⁻ x, ENNReal.ofReal (|⟪gradient ψ x, θ⟫| * Real.exp (-ψ x)) ∂m =
        ∫⁻ z : (ℝ ∙ θ)ᗮ, ENNReal.ofReal (2 * Real.exp (-⨅ s : ℝ, ψ ((z : E) + s • θ)))
          ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) := by
  obtain ⟨c, hc0, hct, hfub⟩ := Probability.exists_lintegral_line m hθ
  refine ⟨c, hc0, hct, hfub, ?_⟩
  have hgrad : Continuous (gradient ψ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hψ1.continuous_fderiv one_ne_zero)
  have hG : Measurable
      (fun x => ENNReal.ofReal (|⟪gradient ψ x, θ⟫| * Real.exp (-ψ x))) := by
    exact (ENNReal.continuous_ofReal.comp
      ((hgrad.inner continuous_const).abs.mul
        (Real.continuous_exp.comp hψ1.continuous.neg))).measurable
  have hinner (x v : E) :
      ⟪gradient ψ x, v⟫ = fderiv ℝ ψ x v :=
    InnerProductSpace.toDual_symm_apply
  have hcompact : ∀ b : ℝ, IsCompact {x : E | ψ x ≤ b} :=
    (Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
      m hψ hint).2
  rw [hfub _ hG]
  apply lintegral_congr
  intro z
  have hconv : ConvexOn ℝ univ
      (fun s : ℝ => ψ ((z : E) + s • θ)) := by
    refine ⟨convex_univ, ?_⟩
    intro s hs t ht a b ha hb hab
    have heq :
        a • ((z : E) + s • θ) + b • ((z : E) + t • θ) =
          (z : E) + (a * s + b * t) • θ := by
      calc
        a • ((z : E) + s • θ) + b • ((z : E) + t • θ) =
            (a + b) • (z : E) + (a * s + b * t) • θ := by
          simp only [smul_add, smul_smul, add_smul]
          abel
        _ = (z : E) + (a * s + b * t) • θ := by
          rw [hab, one_smul]
    have hh := hψ.2 (mem_univ ((z : E) + s • θ))
      (mem_univ ((z : E) + t • θ)) ha hb hab
    rw [heq] at hh
    exact hh
  have hline (s : ℝ) :
      HasDerivAt (fun t : ℝ => ψ ((z : E) + t • θ))
        ⟪gradient ψ ((z : E) + s • θ), θ⟫ s := by
    have hs : HasDerivAt (fun t : ℝ => t • θ) θ s := by
      change HasFDerivAt (fun t : ℝ => t • θ)
        (ContinuousLinearMap.toSpanSingleton ℝ θ) s
      exact (ContinuousLinearMap.toSpanSingleton ℝ θ).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => (z : E) + t • θ) θ s :=
      hs.const_add (z : E)
    have hdψ : HasFDerivAt ψ
        (fderiv ℝ ψ ((z : E) + s • θ)) ((z : E) + s • θ) :=
      (hψ1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    rw [hinner]
    exact hdψ.comp_hasDerivAt s hl
  have hderiv (s : ℝ) :
      deriv (fun t : ℝ => ψ ((z : E) + t • θ)) s =
        ⟪gradient ψ ((z : E) + s • θ), θ⟫ :=
    (hline s).deriv
  have hline1 : ContDiff ℝ 1 (fun s : ℝ => ψ ((z : E) + s • θ)) :=
    hψ1.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  obtain ⟨htop, hbot⟩ :=
    line_tendsto_pair_of_compact_sublevel hcompact hθ (z : E)
  simpa only [hderiv] using
    Line.lintegral_abs_deriv_mul_exp_neg_eq hconv hline1 htop hbot

private theorem lintegral_half_smul_addHaar
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (f : F → ENNReal) (hf : Measurable f) :
    (∫⁻ y, f ((1 / 2 : ℝ) • y) ∂(Measure.addHaar : Measure F)) =
      (2 : ENNReal) ^ Module.finrank ℝ F *
        ∫⁻ y, f y ∂(Measure.addHaar : Measure F) := by
  have hinv : (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ = 2 := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hm :
      Measure.map (fun y : F => (1 / 2 : ℝ) • y) Measure.addHaar =
        (2 : ENNReal) ^ Module.finrank ℝ F •
          (Measure.addHaar : Measure F) := by
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs, Measure.smul_apply]
    norm_num [Measure.addHaar_preimage_smul, abs_pow,
      ENNReal.ofReal_pow, ENNReal.inv_pow, hinv]
  rw [← lintegral_map hf (by fun_prop), hm, lintegral_smul_measure]
  rfl

/-- **Klartag arXiv:1309.2767v1, (19)–(20)**: a centered convex `C¹` `ψ` satisfying (13) in
direction `θ` has `|t| ≤ 2^{n+1} e^{2n} / ε` whenever `ψ(tθ) ≤ 2n + inf ψ`. -/
theorem abs_le_of_mem_levelSet_of_centered (m : Measure E) [m.IsAddHaarMeasure]
    {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ) (hψ1 : ContDiff ℝ 1 ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂m = 1) (hbar : ∫ x, Real.exp (-ψ x) • x ∂m = 0)
    {ε : ℝ} (hε : 0 < ε) {θ : E} (hθ : ‖θ‖ = 1)
    (h13 : ε ≤ ∫ x, |⟪gradient ψ x, θ⟫| * Real.exp (-ψ x) ∂m)
    {t : ℝ} (ht : ψ (t • θ) ≤ 2 * (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y) :
    |t| ≤ 2 ^ (Module.finrank ℝ E + 1) * Real.exp (2 * (Module.finrank ℝ E : ℝ)) / ε := by
  obtain ⟨hbdd, hfrad⟩ := le_finrank_add_iInf_of_centered m hψ hnorm hbar
  have hcont : Continuous ψ := hψ1.continuous
  have hint : Integrable (fun x => Real.exp (-ψ x)) m :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  have hgradint :
      Integrable (fun x => |⟪gradient ψ x, θ⟫| * Real.exp (-ψ x)) m :=
    Integrable.of_integral_ne_zero (hε.trans_le h13).ne'
  have hθ0 : θ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hθ
    norm_num at hθ
  let H := (ℝ ∙ θ)ᗮ
  let n := Module.finrank ℝ E
  let d := Module.finrank ℝ H
  have : Nontrivial E := ⟨⟨θ, 0, hθ0⟩⟩
  have hn : 0 < n := (Module.finrank_pos_iff_of_free ℝ E).mpr inferInstance
  have : Fact (Module.finrank ℝ E = Module.finrank ℝ E - 1 + 1) :=
    ⟨by change n = n - 1 + 1; omega⟩
  have hd : d = n - 1 := by
    dsimp [d, n, H]
    exact Submodule.finrank_orthogonal_span_singleton hθ0
  have hdim : d + 1 = n := by omega
  let G : E → ENNReal := fun x => ENNReal.ofReal (Real.exp (-ψ x))
  let J : ENNReal :=
    ∫⁻ x, ENNReal.ofReal (|⟪gradient ψ x, θ⟫| * Real.exp (-ψ x)) ∂m
  let M : ENNReal :=
    ∫⁻ z : H, ENNReal.ofReal (Real.exp (-⨅ s : ℝ, ψ ((z : E) + s • θ)))
      ∂(Measure.addHaar : Measure H)
  let F : H → ENNReal := fun z => ∫⁻ s : ℝ, G ((z : E) + s • θ)
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  have hF : Measurable F := by
    have hh : Measurable (fun p : H × ℝ => G ((p.1 : E) + p.2 • θ)) := by
      fun_prop
    exact hh.lintegral_prod_right
  have hsplit :
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        (∀ Q : E → ENNReal, Measurable Q →
          c * ∫⁻ x, Q x ∂m =
            ∫⁻ z : H, ∫⁻ s : ℝ, Q ((z : E) + s • θ)
              ∂(volume : Measure ℝ) ∂(Measure.addHaar : Measure H)) ∧
        c * J =
          ∫⁻ z : H,
            ENNReal.ofReal (2 * Real.exp (-⨅ s : ℝ, ψ ((z : E) + s • θ)))
              ∂(Measure.addHaar : Measure H) := by
    exact exists_lintegral_line_abs_inner_gradient m hψ hψ1 hint hθ
  obtain ⟨c, hc0, hct, hfub, hg⟩ := hsplit
  have hnorm' : (∫⁻ x, G x ∂m) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
    rw [hnorm]
    norm_num
  have hFint :
      (∫⁻ z : H, F z ∂(Measure.addHaar : Measure H)) = c := by
    have hh := hfub G hG
    rw [hnorm', mul_one] at hh
    exact hh.symm
  have hg' : c * J = 2 * M := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hg
    norm_num only [ENNReal.ofReal_ofNat] at hg
    rw [hg]
    dsimp [M]
    exact lintegral_const_mul' _ _ (by norm_num)
  have hεJ : ENNReal.ofReal ε ≤ J := by
    calc
      ENNReal.ofReal ε ≤
          ENNReal.ofReal
            (∫ x, |⟪gradient ψ x, θ⟫| * Real.exp (-ψ x) ∂m) :=
        ENNReal.ofReal_le_ofReal h13
      _ = J := ofReal_integral_eq_lintegral_ofReal hgradint
        (Filter.Eventually.of_forall (fun x => by positivity))
  let A : ℝ := |t| * Real.exp (-2 * (n : ℝ)) / 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hline :
      ENNReal.ofReal A * M ≤ (2 : ENNReal) ^ d * c := by
    calc
      ENNReal.ofReal A * M =
          ∫⁻ z : H,
            ENNReal.ofReal
              (A * Real.exp (-⨅ s : ℝ, ψ ((z : E) + s • θ)))
              ∂(Measure.addHaar : Measure H) := by
        simp_rw [ENNReal.ofReal_mul hA]
        dsimp [M]
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ z : H, F ((1 / 2 : ℝ) • z)
            ∂(Measure.addHaar : Measure H) := by
        apply lintegral_mono
        intro z
        simpa only [A, n, F, G, Submodule.coe_smul] using
          lintegral_line_half_ge hψ hbdd hfrad ht (z : E)
      _ = (2 : ENNReal) ^ d *
          ∫⁻ z : H, F z ∂(Measure.addHaar : Measure H) :=
        lintegral_half_smul_addHaar F hF
      _ = (2 : ENNReal) ^ d * c := by rw [hFint]
  have hcombine :
      (ENNReal.ofReal A * ENNReal.ofReal ε) * c ≤
        (2 * (2 : ENNReal) ^ d) * c := by
    calc
      (ENNReal.ofReal A * ENNReal.ofReal ε) * c =
          ENNReal.ofReal A * (c * ENNReal.ofReal ε) := by ac_rfl
      _ ≤ ENNReal.ofReal A * (c * J) := by
        gcongr
      _ = ENNReal.ofReal A * (2 * M) := by rw [hg']
      _ = 2 * (ENNReal.ofReal A * M) := by ac_rfl
      _ ≤ 2 * ((2 : ENNReal) ^ d * c) := by
        gcongr
      _ = (2 * (2 : ENNReal) ^ d) * c := by ac_rfl
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  have hfinite : (2 * (2 : ENNReal) ^ d) * c ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · norm_num
      · finiteness
    · exact hct
  have hreal := ENNReal.toReal_mono hfinite hcombine
  have hbound : A * ε ≤ 2 * (2 : ℝ) ^ d := by
    have hh : (A * ε) * c.toReal ≤
        (2 * (2 : ℝ) ^ d) * c.toReal := by
      simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, hA, hε.le] using hreal
    nlinarith
  have hexp :
      Real.exp (-2 * (n : ℝ)) * Real.exp (2 * (n : ℝ)) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  have hpow : (2 : ℝ) ^ (n + 1) = 4 * (2 : ℝ) ^ d := by
    rw [← hdim]
    simp only [pow_succ]
    ring
  apply (le_div_iff₀ hε).2
  change |t| * ε ≤ (2 : ℝ) ^ (n + 1) * Real.exp (2 * (n : ℝ))
  calc
    |t| * ε =
        (A * ε) * (2 * Real.exp (2 * (n : ℝ))) := by
      dsimp [A]
      calc
        |t| * ε =
            |t| * ε *
              (Real.exp (-2 * (n : ℝ)) * Real.exp (2 * (n : ℝ))) := by
          rw [hexp, mul_one]
        _ = _ := by ring
    _ ≤ (2 * (2 : ℝ) ^ d) * (2 * Real.exp (2 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (2 : ℝ) ^ (n + 1) * Real.exp (2 * (n : ℝ)) := by
      rw [hpow]
      ring

private theorem centered_level_norm_bound (m : Measure E) [m.IsAddHaarMeasure]
    {ψ : E → ℝ}
    (hψ : ConvexOn ℝ univ ψ) (hψ1 : ContDiff ℝ 1 ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂m = 1)
    (hbar : ∫ x, Real.exp (-ψ x) • x ∂m = 0)
    {ε : ℝ} (hε : 0 < ε)
    (h13 : ∀ θ : E, ‖θ‖ = 1 →
      ε ≤ ∫ x, |⟪gradient ψ x, θ⟫| * Real.exp (-ψ x) ∂m)
    {x : E}
    (hx : ψ x ≤ 2 * (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y) :
    ‖x‖ ≤ 2 ^ (Module.finrank ℝ E + 1) *
      Real.exp (2 * (Module.finrank ℝ E : ℝ)) / ε := by
  by_cases hx0 : x = 0
  · subst x
    simp only [norm_zero]
    positivity
  have hn0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  let θ : E := ‖x‖⁻¹ • x
  have hθ : ‖θ‖ = 1 := by
    dsimp [θ]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hn0]
  have hid : ‖x‖ • θ = x := by
    dsimp [θ]
    rw [smul_smul, mul_inv_cancel₀ hn0, one_smul]
  have ht : ψ (‖x‖ • θ) ≤
      2 * (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y := by
    rw [hid]
    exact hx
  have hh := abs_le_of_mem_levelSet_of_centered m hψ hψ1 hnorm hbar
    hε hθ (h13 θ hθ) ht
  simpa only [abs_of_nonneg (norm_nonneg x)] using hh

private theorem centered_uniform_growth (m : Measure E) [m.IsAddHaarMeasure]
    {ψ : E → ℝ}
    (hψ : ConvexOn ℝ univ ψ) (hψ1 : ContDiff ℝ 1 ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂m = 1)
    (hbar : ∫ x, Real.exp (-ψ x) • x ∂m = 0)
    {ε : ℝ} (hε : 0 < ε)
    (h13 : ∀ θ : E, ‖θ‖ = 1 →
      ε ≤ ∫ x, |⟪gradient ψ x, θ⟫| * Real.exp (-ψ x) ∂m)
    {R : ℝ} (hR : 0 < R)
    (hr : 2 ^ (Module.finrank ℝ E + 1) *
      Real.exp (2 * (Module.finrank ℝ E : ℝ)) / ε < R)
    (x : E) :
    (Module.finrank ℝ E : ℝ) / R * ‖x‖ + ψ 0 -
      2 * (Module.finrank ℝ E : ℝ) ≤ ψ x := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := by dsimp [n]; positivity
  obtain ⟨hbdd, hfrad⟩ := le_finrank_add_iInf_of_centered m hψ hnorm hbar
  have hmin : ψ 0 - n ≤ ψ x := by
    have hh := ciInf_le hbdd x
    change ψ 0 ≤ n + ⨅ y, ψ y at hfrad
    linarith
  by_cases hx : ‖x‖ ≤ R
  · have hh : n / R * ‖x‖ ≤ n := by
      calc
        n / R * ‖x‖ ≤ n / R * R :=
          mul_le_mul_of_nonneg_left hx (div_nonneg hn hR.le)
        _ = n := div_mul_cancel₀ _ hR.ne'
    change n / R * ‖x‖ + ψ 0 - 2 * n ≤ ψ x
    linarith
  have hxR : R < ‖x‖ := lt_of_not_ge hx
  have hxpos : 0 < ‖x‖ := hR.trans hxR
  let c : ℝ := R / ‖x‖
  have hc0 : 0 ≤ c := (div_pos hR hxpos).le
  have hc1 : c ≤ 1 := (div_le_one hxpos).mpr hxR.le
  have hy : ‖c • x‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    exact div_mul_cancel₀ _ hxpos.ne'
  have hlevel : 2 * n + (⨅ y, ψ y) < ψ (c • x) := by
    by_contra hh
    have hh' : ψ (c • x) ≤
        2 * (Module.finrank ℝ E : ℝ) + ⨅ y, ψ y := not_lt.mp hh
    have hb := centered_level_norm_bound m hψ hψ1 hnorm hbar hε h13 hh'
    rw [hy] at hb
    exact (not_le_of_gt hr) hb
  have hc := hψ.2 (mem_univ (0 : E)) (mem_univ x)
    (show 0 ≤ 1 - c by linarith) hc0
    (show (1 - c) + c = 1 by ring)
  simp only [smul_zero, zero_add, smul_eq_mul] at hc
  change ψ 0 ≤ n + ⨅ y, ψ y at hfrad
  have hh : n ≤ c * (ψ x - ψ 0) := by linarith
  have hh' : n * ‖x‖ ≤ R * (ψ x - ψ 0) := by
    apply (le_div_iff₀ hxpos).mp
    calc
      n ≤ c * (ψ x - ψ 0) := hh
      _ = R * (ψ x - ψ 0) / ‖x‖ := by dsimp [c]; ring
  have hstrong : n / R * ‖x‖ ≤ ψ x - ψ 0 := by
    calc
      n / R * ‖x‖ = (n * ‖x‖) / R := by ring
      _ ≤ ψ x - ψ 0 := (div_le_iff₀ hR).mpr (by nlinarith [hh'])
  change n / R * ‖x‖ + ψ 0 - 2 * n ≤ ψ x
  linarith

/-- **Klartag arXiv:1309.2767v1, Lemma 2.3**, for `C¹` potentials: for `L, ε > 0` there are
`α, β, γ > 0` such that every convex, `C¹`, `L`-Lipschitz, centered `ψ` satisfying (13) with `ε`
obeys `α‖x‖ - β ≤ ψ(x) ≤ L‖x‖ + γ`. -/
theorem exists_two_sided_linear_bounds (m : Measure E) [m.IsAddHaarMeasure] {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) :
    ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧
      ∀ ψ : E → ℝ, ConvexOn ℝ univ ψ → ContDiff ℝ 1 ψ → LipschitzWith (Real.toNNReal L) ψ →
        ∫ x, Real.exp (-ψ x) ∂m = 1 → ∫ x, Real.exp (-ψ x) • x ∂m = 0 →
        (∀ θ : E, ‖θ‖ = 1 → ε ≤ ∫ x, |⟪gradient ψ x, θ⟫| * Real.exp (-ψ x) ∂m) →
        ∀ x, α * ‖x‖ - β ≤ ψ x ∧ ψ x ≤ L * ‖x‖ + γ := by
  classical
  let n : ℝ := Module.finrank ℝ E
  let r : ℝ := 2 ^ (Module.finrank ℝ E + 1) * Real.exp (2 * n) / ε
  let R : ℝ := r + 1
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [R]; linarith
  let α : ℝ := if Subsingleton E then 1 else n / R
  have hα : 0 < α := by
    dsimp [α]
    split_ifs with h
    · norm_num
    · have : Nontrivial E := not_subsingleton_iff_nontrivial.mp h
      have hn : 0 < n := by
        dsimp [n]
        exact_mod_cast (Module.finrank_pos_iff_of_free ℝ E).mpr inferInstance
      exact div_pos hn hR
  let A : ℝ := ∫ x : E, Real.exp (-(L * ‖x‖)) ∂m
  let B : ℝ := ∫ x : E, Real.exp (-(α * ‖x‖)) ∂m
  have hAi : Integrable (fun x : E => Real.exp (-(L * ‖x‖))) m := by
    simpa only [pow_zero, one_mul] using integrable_norm_pow_mul_exp_neg_mul_norm m hL 0
  have hBi : Integrable (fun x : E => Real.exp (-(α * ‖x‖))) m := by
    simpa only [pow_zero, one_mul] using integrable_norm_pow_mul_exp_neg_mul_norm m hα 0
  have hA : 0 < A := integral_exp_pos hAi
  have hB : 0 < B := integral_exp_pos hBi
  refine ⟨α, max 1 (2 * n - Real.log A), max 1 (2 * n + Real.log B),
    hα, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ψ hψ hψ1 hLip hnorm hbar h13
  have hi : Integrable (fun x => Real.exp (-ψ x)) m :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  have hu (x : E) : ψ x ≤ ψ 0 + L * ‖x‖ := by
    have hh : |ψ x - ψ 0| ≤ L * ‖x‖ := by
      simpa [Real.dist_eq, Real.coe_toNNReal, hL.le] using hLip.dist_le_mul x 0
    linarith [le_abs_self (ψ x - ψ 0)]
  have hl (x : E) : α * ‖x‖ + ψ 0 - 2 * n ≤ ψ x := by
    by_cases hE : Subsingleton E
    · have hx : x = 0 := Subsingleton.elim _ _
      have hn : 0 ≤ n := by dsimp [n]; positivity
      rw [hx, norm_zero, mul_zero]
      linarith
    · have ha : α = n / R := ite_eq_right hE
      rw [ha]
      apply centered_uniform_growth m hψ hψ1 hnorm hbar hε h13 hR
      change r < R
      dsimp [R]
      linarith
  have hlo : Real.exp (-ψ 0) * A ≤ 1 := by
    calc
      Real.exp (-ψ 0) * A =
          ∫ x : E, Real.exp (-ψ 0) * Real.exp (-(L * ‖x‖)) ∂m := by
        rw [integral_const_mul]
      _ ≤ ∫ x : E, Real.exp (-ψ x) ∂m := by
        apply integral_mono (hAi.const_mul _) hi
        intro x
        dsimp only
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith [hu x]
      _ = 1 := hnorm
  have hhi : 1 ≤ Real.exp (2 * n - ψ 0) * B := by
    calc
      1 = ∫ x : E, Real.exp (-ψ x) ∂m := hnorm.symm
      _ ≤ ∫ x : E, Real.exp (2 * n - ψ 0) *
          Real.exp (-(α * ‖x‖)) ∂m := by
        apply integral_mono hi (hBi.const_mul _)
        intro x
        dsimp only
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith [hl x]
      _ = Real.exp (2 * n - ψ 0) * B := integral_const_mul _ _
  have hp0lo : Real.log A ≤ ψ 0 := by
    have hh : Real.exp (-ψ 0 + Real.log A) ≤ Real.exp 0 := by
      rw [Real.exp_add, Real.exp_log hA, Real.exp_zero]
      exact hlo
    have hh' := Real.exp_le_exp.mp hh
    linarith
  have hp0hi : ψ 0 ≤ 2 * n + Real.log B := by
    have hh : Real.exp 0 ≤ Real.exp (2 * n - ψ 0 + Real.log B) := by
      rw [Real.exp_add, Real.exp_log hB, Real.exp_zero]
      exact hhi
    have hh' := Real.exp_le_exp.mp hh
    linarith
  intro x
  constructor
  · have hb := le_max_right (1 : ℝ) (2 * n - Real.log A)
    linarith [hl x]
  · have hg := le_max_right (1 : ℝ) (2 * n + Real.log B)
    linarith [hu x]

end Haar

end FunctionalInequalities.Probability.MomentMeasure

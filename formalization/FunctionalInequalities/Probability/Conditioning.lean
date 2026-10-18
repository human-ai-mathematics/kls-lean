import FunctionalInequalities.Probability.Moments
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Conditioning on a ball

`conditionOnBall ν R hp` is the probability law `ν` conditioned on the open ball `B(0, R)` (Mathlib
`ProbabilityTheory.cond`), defined when the ball has positive mass. `abs_integral_conditionOnBall_sub_le` bounds the
change of the integral of a measurable observable of at most degree-four growth under this conditioning by the
eighth-moment tail, with all integrabilities derived (Letwin's conditioning step, as used for BKL arXiv:2610.05474v1;
the moment tails are `Probability/Moments.lean`, section `MomentTails`).
-/

noncomputable section
open MeasureTheory

namespace FunctionalInequalities.Probability

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The law `ν` conditioned on the open ball of radius `R` (Mathlib `cond`; positive mass required). -/
def conditionOnBall (ν : ProbabilityMeasure E) (R : ℝ) (hp : 0 < (ν : Measure E) (Metric.ball (0 : E) R)) :
    ProbabilityMeasure E :=
  ⟨ProbabilityTheory.cond (ν : Measure E) (Metric.ball (0 : E) R),
    ProbabilityTheory.cond_isProbabilityMeasure (ne_of_gt hp)⟩

omit [BorelSpace E] in
theorem coe_conditionOnBall (ν : ProbabilityMeasure E) (R : ℝ) (hp : 0 < (ν : Measure E) (Metric.ball (0 : E) R)) :
    (conditionOnBall ν R hp : Measure E) = ProbabilityTheory.cond (ν : Measure E) (Metric.ball (0 : E) R) :=
  rfl

/-- **Conditioning error for degree-four observables**: exact and quantitative bounds, with all integrabilities derived. -/
theorem abs_integral_conditionOnBall_sub_le (ν : ProbabilityMeasure E) {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (h8 : Integrable (fun x : E => ‖x‖ ^ 8) (ν : Measure E))
    (hp : 0 < (ν : Measure E) (Metric.ball (0 : E) R)) {f : E → ℝ} (hf : Measurable f)
    (hgrow : ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 4)) :
    Integrable f (ν : Measure E) ∧
    Integrable f (conditionOnBall ν R hp : Measure E) ∧
    Integrable (fun x : E => ‖x‖ ^ 4) (ν : Measure E) ∧
    |(∫ x, f x ∂(conditionOnBall ν R hp : Measure E)) - ∫ x, f x ∂(ν : Measure E)| ≤
      ((1 - ((ν : Measure E) (Metric.ball (0 : E) R)).toReal) * |∫ x, f x ∂(ν : Measure E)| +
        ∫ x, (Metric.ball (0 : E) R)ᶜ.indicator (fun y => |f y|) x ∂(ν : Measure E)) /
        ((ν : Measure E) (Metric.ball (0 : E) R)).toReal ∧
    |(∫ x, f x ∂(conditionOnBall ν R hp : Measure E)) - ∫ x, f x ∂(ν : Measure E)| ≤
      (C / ((ν : Measure E) (Metric.ball (0 : E) R)).toReal) *
        ((1 - ((ν : Measure E) (Metric.ball (0 : E) R)).toReal) * (2 + ∫ x, ‖x‖ ^ 4 ∂(ν : Measure E)) +
          (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 4) := by
    let B : Set E := Metric.ball (0 : E) R
    let μ : Measure E := (ν : Measure E)
    let p : ℝ := (μ B).toReal
    have hB : MeasurableSet B := measurableSet_ball
    have hpμ : μ B ≠ 0 := ne_of_gt hp
    have hp0 : 0 < p := by
      dsimp [p]
      exact ENNReal.toReal_pos hpμ (measure_ne_top μ B)
    have hpone : p ≤ 1 := by
      have hle : μ B ≤ μ Set.univ := measure_mono (Set.subset_univ B)
      dsimp [p]
      simpa using ENNReal.toReal_mono (by simp) hle
    have h4 :=
      integrable_norm_pow_four_and_tail_le_of_integrable_pow_eight ν hR h8
    have hf4 : Integrable (fun x : E => ‖x‖ ^ 4) μ := by
      simpa [μ] using h4.1
    have htail :
        Integrable (Bᶜ.indicator (fun x : E => ‖x‖ ^ 4)) μ := by
      simpa [μ, B] using h4.2.1
    have hbase : Integrable (fun x : E => (1 : ℝ) + ‖x‖ ^ 4) μ :=
      (integrable_const (μ := μ) (1 : ℝ)).add hf4
    have hbound : Integrable (fun x : E => C * (1 + ‖x‖ ^ 4)) μ :=
      hbase.const_mul C
    have hfν : Integrable f μ := by
      apply hbound.mono'
      · exact hf.aestronglyMeasurable
      · filter_upwards [] with x
        simpa [abs_of_nonneg (show 0 ≤ C * (1 + ‖x‖ ^ 4) by positivity)] using
          hgrow x
    have hfcond : Integrable f (conditionOnBall ν R hp : Measure E) := by
      rw [coe_conditionOnBall]
      unfold ProbabilityTheory.cond
      exact hfν.restrict.smul_measure
        (ENNReal.inv_ne_top.mpr hpμ)
    have h4' : Integrable (fun x : E => ‖x‖ ^ 4) μ := hf4
    let I : ℝ := ∫ x, f x ∂μ
    let J : ℝ := ∫ x, Bᶜ.indicator f x ∂μ
    let K : ℝ := ∫ x, Bᶜ.indicator (fun y => |f y|) x ∂μ
    let A : ℝ := ∫ x, ‖x‖ ^ 4 ∂μ
    let T : ℝ := ∫ x, Bᶜ.indicator (fun y => ‖y‖ ^ 4) x ∂μ
    have hsplit : I = (∫ x in B, f x ∂μ) + J := by
      have h := integral_add_compl hB hfν
      rw [← integral_indicator hB.compl] at h
      dsimp [I, J]
      exact h.symm
    have hcond :
        (∫ x, f x ∂(conditionOnBall ν R hp : Measure E)) =
          (∫ x in B, f x ∂μ) / p := by
      rw [coe_conditionOnBall]
      unfold ProbabilityTheory.cond
      rw [integral_smul_measure, ← integral_indicator hB]
      simp only [smul_eq_mul, ENNReal.toReal_inv]
      dsimp [p]
      ring
    have hJabs : |J| ≤ K := by
      dsimp [J, K]
      calc
        |∫ x, Bᶜ.indicator f x ∂μ| ≤
            ∫ x, |Bᶜ.indicator f x| ∂μ :=
          abs_integral_le_integral_abs
        _ = ∫ x, Bᶜ.indicator (fun y => |f y|) x ∂μ := by
          congr 1
          funext x
          by_cases hx : x ∈ Bᶜ <;> simp [Set.indicator, hx]
    have hE : |I| ≤ C * (1 + A) := by
      dsimp [I, A]
      calc
        |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ :=
          abs_integral_le_integral_abs
        _ ≤ ∫ x, C * (1 + ‖x‖ ^ 4) ∂μ :=
          integral_mono hfν.abs hbound (fun x => hgrow x)
        _ = C * (1 + ∫ x, ‖x‖ ^ 4 ∂μ) := by
          rw [integral_const_mul]
          rw [integral_add (integrable_const (μ := μ) (1 : ℝ)) hf4]
          simp
    have hK :
        K ≤ C * ((1 - p) + T) := by
      have hi :
          Integrable
            (Bᶜ.indicator (fun y => C * (1 + ‖y‖ ^ 4))) μ :=
        hbound.indicator hB.compl
      have hpoint :
          ∀ x, Bᶜ.indicator (fun y => |f y|) x ≤
            Bᶜ.indicator (fun y => C * (1 + ‖y‖ ^ 4)) x := by
        intro x
        by_cases hx : x ∈ Bᶜ <;> simp [Set.indicator, hx, hgrow]
      have hind :
          Bᶜ.indicator (fun y : E => 1 + ‖y‖ ^ 4) =
            Bᶜ.indicator (fun _ => 1) +
              Bᶜ.indicator (fun y : E => ‖y‖ ^ 4) := by
        funext x
        by_cases hx : x ∈ Bᶜ <;> simp [Set.indicator, hx]
      have hc : Integrable (Bᶜ.indicator (fun _ : E => (1 : ℝ))) μ :=
        (integrable_const (μ := μ) (1 : ℝ)).indicator hB.compl
      have hle :
          K ≤ ∫ x, Bᶜ.indicator (fun y => C * (1 + ‖y‖ ^ 4)) x ∂μ :=
        integral_mono
          ((hfν.abs).indicator hB.compl) hi hpoint
      have heq :
          (∫ x, Bᶜ.indicator (fun y => C * (1 + ‖y‖ ^ 4)) x ∂μ) =
            C * ((1 - p) + T) := by
        have hscalar :
            Bᶜ.indicator (fun y : E => C * (1 + ‖y‖ ^ 4)) =
              (fun y => C * Bᶜ.indicator (fun z : E => 1 + ‖z‖ ^ 4) y) := by
          funext x
          by_cases hx : x ∈ Bᶜ <;> simp [Set.indicator, hx]
        rw [hscalar, integral_const_mul]
        calc
          C * (∫ x, Bᶜ.indicator (fun y : E => 1 + ‖y‖ ^ 4) x ∂μ) =
              C * ((∫ x, Bᶜ.indicator (fun _ : E => (1 : ℝ)) x ∂μ) +
                ∫ x, Bᶜ.indicator (fun y : E => ‖y‖ ^ 4) x ∂μ) := by
                  congr 1
                  rw [hind]
                  exact integral_add hc htail
          _ = C * ((1 - p) + T) := by
            rw [integral_indicator hB.compl]
            have hμreal : μ.real B = p := rfl
            simp [T, p, measureReal_compl hB, hμreal]
      exact hle.trans_eq heq
    have hmain :
        |(∫ x, f x ∂(conditionOnBall ν R hp : Measure E)) - I| ≤
          ((1 - p) * |I| + K) / p := by
      have hid :
          (∫ x, f x ∂(conditionOnBall ν R hp : Measure E)) - I =
            ((1 - p) * I - J) / p := by
        rw [hcond]
        have hs := hsplit
        field_simp [ne_of_gt hp0]
        linarith
      rw [hid]
      calc
        |((1 - p) * I - J) / p| =
            |(1 - p) * I - J| / p := by
              rw [abs_div, abs_of_pos hp0]
        _ ≤ ((1 - p) * |I| + |J|) / p := by
          apply div_le_div_of_nonneg_right
          · calc
              |(1 - p) * I - J| ≤
                  |(1 - p) * I| + |J| := by
                simpa [sub_eq_add_neg] using
                  (norm_add_le ((1 - p) * I) (-J))
              _ = (1 - p) * |I| + |J| := by
                rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hpone)]
          · exact le_of_lt hp0
        _ ≤ ((1 - p) * |I| + K) / p := by
          gcongr
    have hquant :
        ((1 - p) * |I| + K) / p ≤
          (C / p) * ((1 - p) * (2 + A) +
            (∫ x, ‖x‖ ^ 8 ∂μ) / R ^ 4) := by
      have ht : T ≤ (∫ x, ‖x‖ ^ 8 ∂μ) / R ^ 4 := by
        simpa [T, μ, B] using h4.2.2
      have hscaled :
          (1 - p) * |I| + K ≤
            C * ((1 - p) * (2 + A) +
              (∫ x, ‖x‖ ^ 8 ∂μ) / R ^ 4) := by
        have h₁ :=
          mul_le_mul_of_nonneg_left hE (sub_nonneg.mpr hpone)
        have h₂ :
            C * ((1 - p) + T) ≤
              C * ((1 - p) + (∫ x, ‖x‖ ^ 8 ∂μ) / R ^ 4) := by
          gcongr
        calc
          (1 - p) * |I| + K ≤
              (1 - p) * (C * (1 + A)) + C * ((1 - p) + T) :=
            add_le_add h₁ hK
          _ ≤ (1 - p) * (C * (1 + A)) +
              C * ((1 - p) +
                (∫ x, ‖x‖ ^ 8 ∂μ) / R ^ 4) := by
            linarith
          _ = C * ((1 - p) * (2 + A) +
              (∫ x, ‖x‖ ^ 8 ∂μ) / R ^ 4) := by
            ring
      calc
        ((1 - p) * |I| + K) / p ≤
            (C * ((1 - p) * (2 + A) +
              (∫ x, ‖x‖ ^ 8 ∂μ) / R ^ 4)) / p :=
          div_le_div_of_nonneg_right hscaled (le_of_lt hp0)
        _ = (C / p) * ((1 - p) * (2 + A) +
            (∫ x, ‖x‖ ^ 8 ∂μ) / R ^ 4) := by
          ring
    refine ⟨hfν, hfcond, h4', ?_, ?_⟩
    · simpa [μ, B, p, I, K] using hmain
    · simpa [μ, B, p, I, A] using le_trans hmain hquant

end FunctionalInequalities.Probability

section LT10ABallConditioningMoments

open MeasureTheory Set Metric Filter
open scoped Topology

/-! Conditioning weakly convergent laws on a ball containing the support of the limit: integrals of continuous functions converge (Letwin Lemma A.1 approximation). -/

namespace FunctionalInequalities.KLS

/-- **Conditioning on a large ball preserves weak convergence** (Letwin Lemma A.1 approximation):
if `ν k → μ` weakly and `μ` is carried by `closedBall 0 r` with `r < R`, then for every continuous `f` the
integrals against the conditioned laws `ν k [| closedBall 0 R]` converge to `∫ f dμ`. -/
theorem tendsto_integral_cond_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hν : Tendsto ν atTop (𝓝 μ)) {r R : ℝ} (hrR : r < R)
    (hsupp : (μ : Measure E) (closedBall (0 : E) r)ᶜ = 0) {f : E → ℝ} (hf : Continuous f) :
    Tendsto (fun k => ∫ x, f x ∂(ProbabilityTheory.cond (ν k : Measure E) (closedBall (0 : E) R)))
      atTop (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  let B : Set E := closedBall (0 : E) R
  have hB : MeasurableSet B := isClosed_closedBall.measurableSet
  have hsub : closedBall (0 : E) r ⊆ B :=
    closedBall_subset_closedBall hrR.le
  have hBc : (μ : Measure E) Bᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hsub) hsupp
  have hBmass : (μ : Measure E) B = 1 := by
    simpa only [measure_univ] using measure_of_measure_compl_eq_zero hBc
  have hfront : (μ : Measure E) (frontier B) = 0 := by
    apply measure_mono_null (t := (closedBall (0 : E) r)ᶜ) _ hsupp
    intro x hx hxr
    have hxR : dist x 0 = R :=
      mem_sphere.mp (frontier_closedBall_subset_sphere hx)
    have hxr' : dist x 0 ≤ r := mem_closedBall.mp hxr
    linarith
  have hmass :
      Tendsto (fun k => (ν k : Measure E) B) atTop (𝓝 (1 : ENNReal)) := by
    rw [← hBmass]
    exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν hfront
  have hcompl :
      Tendsto (fun k => (ν k : Measure E) Bᶜ) atTop (𝓝 (0 : ENNReal)) := by
    rw [← hBc]
    apply ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν
    rw [frontier_compl]
    exact hfront
  have hmassReal :
      Tendsto (fun k => ((ν k : Measure E) B).toReal) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_one] using
      (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp hmass
  have hcomplReal :
      Tendsto (fun k => ((ν k : Measure E) Bᶜ).toReal) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hcompl

  -- Clip the values of f to obtain a bounded continuous function equal to f on B.
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf.continuousOn
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hfC : ∀ x ∈ B, ‖f x‖ ≤ C := by
    intro x hx
    exact (hC₀ x hx).trans (le_max_left _ _)
  have hclip : ∀ x : E, ‖max (-C) (min C (f x))‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let g : BoundedContinuousFunction E ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => max (-C) (min C (f x)))
      (continuous_const.max (continuous_const.min hf)) C hclip
  have hg_eq : EqOn (fun x => g x) f B := by
    intro x hx
    change max (-C) (min C (f x)) = f x
    have hx' := abs_le.mp (show |f x| ≤ C from hfC x hx)
    rw [min_eq_right hx'.2, max_eq_right hx'.1]
  have hgμ : (∫ x, g x ∂(μ : Measure E)) = ∫ x, f x ∂(μ : Measure E) := by
    apply integral_congr_ae
    have hae : ∀ᵐ x ∂(μ : Measure E), x ∈ B := ae_iff.mpr hBc
    exact hae.mono fun x hx => hg_eq hx
  have hg :
      Tendsto (fun k => ∫ x, g x ∂(ν k : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
    rw [← hgμ]
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν g

  have htail :
      Tendsto (fun k => ∫ x in Bᶜ, g x ∂(ν k : Measure E)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm
      (a := fun k => ‖g‖ * ((ν k : Measure E) Bᶜ).toReal)
    · intro k
      have hbound :
          ‖∫ x in Bᶜ, g x ∂(ν k : Measure E)‖ ≤
            ‖g‖ * ((ν k : Measure E).restrict Bᶜ).real univ :=
        norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
      simpa only [Measure.real_def, Measure.restrict_apply_univ] using hbound
    · simpa only [mul_zero] using
        (tendsto_const_nhds.mul hcomplReal :
          Tendsto (fun k => ‖g‖ * ((ν k : Measure E) Bᶜ).toReal)
            atTop (𝓝 (‖g‖ * 0)))
  have hrestricted :
      Tendsto (fun k => ∫ x in B, f x ∂(ν k : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
    have hlim := hg.sub htail
    rw [sub_zero] at hlim
    apply hlim.congr'
    apply Filter.Eventually.of_forall
    intro k
    have hsplit := integral_add_compl hB (g.integrable (ν k : Measure E))
    have heq :
        (∫ x in B, g x ∂(ν k : Measure E)) =
          ∫ x in B, f x ∂(ν k : Measure E) :=
      setIntegral_congr_fun hB hg_eq
    linarith
  have hinv :
      Tendsto (fun k => ((ν k : Measure E) B).toReal⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [inv_one] using hmassReal.inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
  have hlim := hinv.mul hrestricted
  rw [one_mul] at hlim
  change Tendsto
    (fun k => ∫ x, f x ∂(((ν k : Measure E) B)⁻¹ • (ν k : Measure E).restrict B))
    atTop (𝓝 (∫ x, f x ∂(μ : Measure E)))
  simpa only [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul] using hlim

end FunctionalInequalities.KLS

end LT10ABallConditioningMoments

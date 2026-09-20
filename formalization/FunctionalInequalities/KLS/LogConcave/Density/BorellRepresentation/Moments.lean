import Mathlib.Probability.Moments.IntegrableExpMul
import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic

/-!
# BorellRepresentation: Moments

Responsibility split of the existing implementation. Public namespaces, mathematical scope
and proof bodies are preserved; later layers import their prerequisites.
-/

noncomputable section
open MeasureTheory Set Topology Filter

namespace FunctionalInequalities

section Moments

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

namespace KLS.BorelLogConcave

omit [FiniteDimensional ℝ V] in
/-- Borell's tail lemma in the form needed here: once a ball of radius `R` carries mass at
least `3/4`, the mass outside radius `k R` decays geometrically in `k`. The bound is stated
for every `k`, the cases `k = 0, 1` being trivial. -/
theorem measure_norm_ge_le {ν : ProbabilityMeasure V} (hν : BorelLogConcave ν)
    {R : ℝ} (hball : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R)) (k : ℕ) :
    (ν : Measure V) {v | (k : ℝ) * R ≤ ‖v‖} ≤ ENNReal.ofReal ((3 : ℝ) ^ ((1 - (k : ℝ)) / 2)) := by
  by_cases hk : k < 2
  · have hk' : (k : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hk
    calc (ν : Measure V) {v | (k : ℝ) * R ≤ ‖v‖} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ ((1 - (k : ℝ)) / 2)) :=
        ENNReal.one_le_ofReal.mpr (Real.one_le_rpow (by norm_num) (by linarith))
  push Not at hk
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set t : ℝ := 2 / ((k : ℝ) + 1) with ht_def
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have ht : 0 < t := by positivity
  have ht1 : t < 1 := by
    rw [ht_def, div_lt_one hk1]; linarith
  have ht_eq : t * ((k : ℝ) + 1) = 2 := by
    rw [ht_def]; field_simp
  set B₀ : Set V := {v | (k : ℝ) * R ≤ ‖v‖} with hB₀_def
  have hB₀ : MeasurableSet B₀ := (isClosed_le continuous_const continuous_norm).measurableSet
  have hB₁ : MeasurableSet (Metric.ball (0 : V) R) := measurableSet_ball
  have key := hν B₀ (Metric.ball 0 R) hB₀ hB₁ t ht ht1
  have hsub : {z | ∃ x ∈ B₀, ∃ y ∈ Metric.ball (0 : V) R, z = t • x + (1 - t) • y} ⊆
      (Metric.closedBall (0 : V) R)ᶜ := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hx' : (k : ℝ) * R ≤ ‖x‖ := hx
    have hy' : ‖y‖ < R := mem_ball_zero_iff.mp hy
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
    have h1 := norm_le_add_norm_add (t • x) ((1 - t) • y)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht,
      abs_of_pos (sub_pos.mpr ht1)] at h1
    have h2 : t * ((k : ℝ) * R) ≤ t * ‖x‖ := mul_le_mul_of_nonneg_left hx' ht.le
    have h3 : (1 - t) * ‖y‖ < (1 - t) * R := mul_lt_mul_of_pos_left hy' (sub_pos.mpr ht1)
    have h4 : t * ((k : ℝ) * R) - (1 - t) * R = R := by linear_combination R * ht_eq
    linarith
  have hinner : innerMeasure (ν : Measure V)
      {z | ∃ x ∈ B₀, ∃ y ∈ Metric.ball (0 : V) R, z = t • x + (1 - t) • y} ≤
        (ν : Measure V) (Metric.closedBall (0 : V) R)ᶜ :=
    (innerMeasure_mono _ hsub).trans (innerMeasure_le _ _)
  have hcompl : (ν : Measure V) (Metric.closedBall (0 : V) R)ᶜ ≤ ENNReal.ofReal (1 / 4) := by
    calc (ν : Measure V) (Metric.closedBall (0 : V) R)ᶜ
        ≤ (ν : Measure V) (Metric.ball (0 : V) R)ᶜ :=
          measure_mono (Set.compl_subset_compl.mpr Metric.ball_subset_closedBall)
      _ = 1 - (ν : Measure V) (Metric.ball (0 : V) R) := prob_compl_eq_one_sub hB₁
      _ ≤ 1 - ENNReal.ofReal (3 / 4) := tsub_le_tsub_left hball 1
      _ = ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
  have h34 : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R) ^ (1 - t) := by
    calc ENNReal.ofReal (3 / 4) = ENNReal.ofReal (3 / 4) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ ≤ ENNReal.ofReal (3 / 4) ^ (1 - t) :=
          ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.mpr (by norm_num))
            (by linarith)
      _ ≤ (ν : Measure V) (Metric.ball (0 : V) R) ^ (1 - t) :=
          ENNReal.rpow_le_rpow hball (by linarith)
  have hmain : (ν : Measure V) B₀ ^ t * ENNReal.ofReal (3 / 4) ≤ ENNReal.ofReal (1 / 4) :=
    calc (ν : Measure V) B₀ ^ t * ENNReal.ofReal (3 / 4)
        ≤ (ν : Measure V) B₀ ^ t * (ν : Measure V) (Metric.ball (0 : V) R) ^ (1 - t) :=
          mul_le_mul' le_rfl h34
      _ ≤ _ := key
      _ ≤ _ := hinner
      _ ≤ _ := hcompl
  have hpow : (ν : Measure V) B₀ ^ t ≤ ENNReal.ofReal (1 / 3) := by
    have h34ne : ENNReal.ofReal (3 / 4) ≠ 0 := by simp
    have h34top : ENNReal.ofReal (3 / 4) ≠ ⊤ := ENNReal.ofReal_ne_top
    have := (ENNReal.le_div_iff_mul_le (Or.inl h34ne) (Or.inl h34top)).mpr hmain
    rwa [← ENNReal.ofReal_div_of_pos (by norm_num), show (1 / 4 : ℝ) / (3 / 4) = 1 / 3 by norm_num]
      at this
  have hroot : (ν : Measure V) B₀ ≤ ENNReal.ofReal (1 / 3) ^ (((k : ℝ) + 1) / 2) := by
    have h1t : 1 / t = ((k : ℝ) + 1) / 2 := by rw [ht_def, one_div_div]
    calc (ν : Measure V) B₀ = ((ν : Measure V) B₀ ^ t) ^ (1 / t) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel ht.ne', ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal (1 / 3) ^ (1 / t) := ENNReal.rpow_le_rpow hpow (by positivity)
      _ = _ := by rw [h1t]
  refine hroot.trans ?_
  rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : ((1 : ℝ) / 3) ^ (((k : ℝ) + 1) / 2) = (3 : ℝ) ^ (-(((k : ℝ) + 1) / 2)) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  rw [hexp]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

omit [FiniteDimensional ℝ V] in
/-- A Borel log-concave probability law on a finite-dimensional space has an exponential
moment. The radius is chosen from the exhaustion by balls, the tail from Borell's lemma, and
the integral is dominated by a geometric series. -/
theorem exists_integrable_exp_norm {ν : ProbabilityMeasure V}
    (hν : BorelLogConcave ν) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun v ↦ Real.exp (t * ‖v‖)) (ν : Measure V) := by
  -- a ball of integer radius carrying mass at least 3/4
  have hmono : Monotone fun n : ℕ ↦ Metric.ball (0 : V) n := fun i j hij ↦
    Metric.ball_subset_ball (by exact_mod_cast hij)
  have htend := tendsto_measure_iUnion_atTop (μ := (ν : Measure V)) hmono
  rw [Metric.iUnion_ball_nat, measure_univ] at htend
  obtain ⟨n, hn1, hball⟩ :=
    ((eventually_ge_atTop 1).and
      (htend.eventually_const_le (ENNReal.ofReal_lt_one.mpr (by norm_num : (3 / 4 : ℝ) < 1)))).exists
  set R : ℝ := (n : ℝ) with hR_def
  have hR : 0 < R := by rw [hR_def]; exact Nat.cast_pos.mpr hn1
  have hball' : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R) := hball
  have tail := hν.measure_norm_ge_le hball'
  -- the rate and the dominating series
  set t₀ : ℝ := Real.log 3 / (4 * R) with ht₀_def
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ht₀ : 0 < t₀ := by positivity
  set c : ℕ → ℝ := fun k ↦ Real.exp (t₀ * ((k : ℝ) + 1) * R) with hc_def
  set b : ℕ → ℝ := fun k ↦ (3 : ℝ) ^ ((1 - (k : ℝ)) / 2) with hb_def
  set A : ℕ → Set V := fun k ↦ {v | (k : ℝ) * R ≤ ‖v‖} with hA_def
  have hA : ∀ k, MeasurableSet (A k) := fun k ↦
    (isClosed_le continuous_const continuous_norm).measurableSet
  set f : ℕ → V → ENNReal := fun k ↦ (A k).indicator fun _ ↦ ENNReal.ofReal (c k) with hf_def
  have hc_pos : ∀ k, 0 < c k := fun k ↦ Real.exp_pos _
  have hb_pos : ∀ k, 0 < b k := fun k ↦ Real.rpow_pos_of_pos (by norm_num) _
  -- pointwise domination
  have hpt : ∀ v : V, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ≤ ∑' k, f k v := by
    intro v
    set n := ⌊‖v‖ / R⌋₊ with hn_def
    have hn1 : (n : ℝ) ≤ ‖v‖ / R := Nat.floor_le (div_nonneg (norm_nonneg _) hR.le)
    have hn2 : ‖v‖ / R < n + 1 := Nat.lt_floor_add_one _
    have hmem : v ∈ A n := by
      show (n : ℝ) * R ≤ ‖v‖
      exact (le_div_iff₀ hR).mp hn1
    have hlt : ‖v‖ < ((n : ℝ) + 1) * R := (div_lt_iff₀ hR).mp hn2
    calc ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ≤ ENNReal.ofReal (c n) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hlt.le ht₀.le
      _ = f n v := by simp [hf_def, Set.indicator_of_mem hmem]
      _ ≤ ∑' k, f k v := ENNReal.le_tsum n
  -- the series
  have hcb : ∀ k, c k * b k = (3 : ℝ) ^ ((3 : ℝ) / 4) * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
    intro k
    have hc : c k = (3 : ℝ) ^ (((k : ℝ) + 1) / 4) := by
      rw [hc_def, Real.rpow_def_of_pos (by norm_num)]
      rw [ht₀_def]
      field_simp
    rw [hc, hb_def]
    simp only
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hq1 : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hq0 : 0 ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hsum : Summable fun k ↦ c k * b k :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _).congr fun k ↦ (hcb k).symm
  -- the integral bound
  have hbound : ∫⁻ v, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ∂(ν : Measure V) < ⊤ := by
    calc ∫⁻ v, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ∂(ν : Measure V)
        ≤ ∫⁻ v, ∑' k, f k v ∂(ν : Measure V) := lintegral_mono hpt
      _ = ∑' k, ∫⁻ v, f k v ∂(ν : Measure V) :=
          lintegral_tsum fun k ↦ (measurable_const.indicator (hA k)).aemeasurable
      _ = ∑' k, ENNReal.ofReal (c k) * (ν : Measure V) (A k) := by
          congr 1; ext k; exact lintegral_indicator_const (hA k) _
      _ ≤ ∑' k, ENNReal.ofReal (c k) * ENNReal.ofReal (b k) :=
          ENNReal.tsum_le_tsum fun k ↦ mul_le_mul' le_rfl (tail k)
      _ = ∑' k, ENNReal.ofReal (c k * b k) := by
          congr 1; ext k; rw [ENNReal.ofReal_mul (hc_pos k).le]
      _ = ENNReal.ofReal (∑' k, c k * b k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (mul_pos (hc_pos k) (hb_pos k)).le) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨t₀, ht₀, ?_, ?_⟩
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
      |>.aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun v ↦ (Real.exp_pos _).le)]
    exact hbound

end KLS.BorelLogConcave

namespace Probability

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- An exponential moment gives finite moments of every order. -/
theorem integrable_norm_pow_of_integrable_exp_norm {ν : Measure V} [IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 < t) (hint : Integrable (fun v ↦ Real.exp (t * ‖v‖)) ν) (p : ℕ) :
    Integrable (fun v ↦ ‖v‖ ^ p) ν := by
  have hneg : Integrable (fun v ↦ Real.exp (-t * ‖v‖)) ν := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun v ↦ ?_)
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg v])
  have := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul ht.ne' hint hneg p
  simpa [abs_norm] using this

end Probability

end Moments


end FunctionalInequalities

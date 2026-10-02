import FunctionalInequalities.KLS.LogConcave.Borel

/-!
# Borell's lemma for log-concave laws

S. G. Bobkov, *Isoperimetric and analytic inequalities for log-concave probability measures*
(Ann. Probab. 27 (1999)), Lemma 3.1, attributed to Borell: for a log-concave probability law
μ, every `t ≥ 1` and every convex set `B` symmetric about the origin with `θ = μ(B) > 1/2`,
`1 - μ(tB) ≤ (1 - θ) ((1 - θ)/θ)^((t-1)/2)`.

The Lean statement adds measurability of `B`: a convex set need not be Borel, while the paper's
`μ(B)` presupposes it. Log-concavity is the compact-set predicate `KLS.LogConcave`, equivalent
to Bobkov's Borel formulation (`LogConcave.borel_iff`).
-/

open MeasureTheory
open scoped Pointwise

namespace FunctionalInequalities.KLS.LogConcave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The convex-combination inclusion behind Borell's lemma:
`(2/(t+1)) (tB)ᶜ + (1 - 2/(t+1)) B ⊆ Bᶜ` for a convex symmetric `B` and `t > 1`. -/
theorem combination_compl_smul_subset_compl {B : Set E} (hconv : Convex ℝ B)
    (hsymm : ∀ x ∈ B, -x ∈ B) {t : ℝ} (ht : 1 < t) :
    {z | ∃ x ∈ (t • B)ᶜ, ∃ y ∈ B, z = (2 / (t + 1)) • x + (1 - 2 / (t + 1)) • y} ⊆ Bᶜ := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, hz⟩
  intro hzb
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have ht1 : t + 1 ≠ 0 := by linarith
  have hden : 0 < 2 * t := mul_pos (by norm_num) htpos

  let a : ℝ := (t + 1) / (2 * t)
  let b : ℝ := (t - 1) / (2 * t)

  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (by linarith) (le_of_lt hden)

  have hb : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg (by linarith) (le_of_lt hden)

  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [ht0]
    ring

  have hw : a • z + b • (-y) ∈ B := by
    exact hconv hzb (hsymm y hy) ha hb hab

  have hid : t • (a • z + b • (-y)) = x := by
    rw [hz]
    simp [a, b, smul_add, smul_smul]
    field_simp [ht0, ht1]
    module

  have hxt : x ∈ t • B := by
    exact Set.mem_smul_set.mpr ⟨a • z + b • (-y), hw, hid⟩

  exact hx hxt

/-- The log-concavity step of Borell's lemma in real form:
`(1 - μ(tB))^(2/(t+1)) · μ(B)^(1 - 2/(t+1)) ≤ 1 - μ(B)` for `t > 1`. -/
theorem one_sub_measure_smul_rpow_mul_le {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ)
    {B : Set E} (hB : MeasurableSet B) (hconv : Convex ℝ B) (hsymm : ∀ x ∈ B, -x ∈ B)
    {t : ℝ} (ht : 1 < t) :
    (1 - ((μ : Measure E) (t • B)).toReal) ^ (2 / (t + 1)) *
        ((μ : Measure E) B).toReal ^ (1 - 2 / (t + 1)) ≤
      1 - ((μ : Measure E) B).toReal := by
  have htpos : 0 < t := lt_trans zero_lt_one ht
  have ht0 : t ≠ 0 := ne_of_gt htpos

  have hts : MeasurableSet (t • B) := by
    exact hB.const_smul_of_ne_zero ht0

  have htsc : MeasurableSet (t • B)ᶜ := hts.compl

  have hpow0 : 0 < (2 / (t + 1) : ℝ) := by
    positivity

  have hpow1 : (2 / (t + 1) : ℝ) < 1 := by
    have hden : 0 < t + 1 := by linarith
    apply (div_lt_one hden).2
    linarith

  let C : Set E :=
    {z | ∃ x ∈ (t • B)ᶜ, ∃ y ∈ B,
      z = (2 / (t + 1)) • x + (1 - 2 / (t + 1)) • y}

  have hsub : C ⊆ Bᶜ := by
    exact combination_compl_smul_subset_compl hconv hsymm ht

  have hlog :
      ((μ : Measure E) (t • B)ᶜ) ^ (2 / (t + 1)) *
          ((μ : Measure E) B) ^ (1 - 2 / (t + 1))
        ≤ KLS.innerMeasure (μ : Measure E) C := by
    simpa [C] using
      ((KLS.LogConcave.borel_iff μ).1 hμ
        (t • B)ᶜ B htsc hB (2 / (t + 1)) hpow0 hpow1)

  have hinner :
      KLS.innerMeasure (μ : Measure E) C ≤ (μ : Measure E) Bᶜ :=
    le_trans (KLS.innerMeasure_le (μ : Measure E) C) (measure_mono hsub)

  have henne :
      ((μ : Measure E) (t • B)ᶜ) ^ (2 / (t + 1)) *
          ((μ : Measure E) B) ^ (1 - 2 / (t + 1))
        ≤ (μ : Measure E) Bᶜ :=
    hlog.trans hinner

  have hreal := ENNReal.toReal_mono (by finiteness) henne
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hreal

  have hcomp_t :
      (μ : Measure E) (t • B)ᶜ = 1 - (μ : Measure E) (t • B) :=
    prob_compl_eq_one_sub hts

  have hcomp_B :
      (μ : Measure E) Bᶜ = 1 - (μ : Measure E) B :=
    prob_compl_eq_one_sub hB

  rw [hcomp_t, hcomp_B] at hreal

  have hle_t : (μ : Measure E) (t • B) ≤ 1 := prob_le_one
  have hle_B : (μ : Measure E) B ≤ 1 := prob_le_one

  have htr_t :
      (1 - (μ : Measure E) (t • B)).toReal =
        1 - ((μ : Measure E) (t • B)).toReal := by
    rw [ENNReal.toReal_sub_of_le hle_t] <;> simp

  have htr_B :
      (1 - (μ : Measure E) B).toReal =
        1 - ((μ : Measure E) B).toReal := by
    rw [ENNReal.toReal_sub_of_le hle_B] <;> simp

  rw [htr_t, htr_B] at hreal
  exact hreal

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A convex set symmetric about the origin is contained in its dilates `t • B`, `t ≥ 1`. -/
theorem subset_smul_of_one_le {B : Set E} (hconv : Convex ℝ B) (hsymm : ∀ x ∈ B, -x ∈ B)
    {t : ℝ} (ht : 1 ≤ t) : B ⊆ t • B := by
  intro x hx
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht0 : t ≠ 0 := ne_of_gt htpos

  have hzero : (0 : E) ∈ B := by
    have h :=
      hconv hx (hsymm x hx)
        (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have heq :
        (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) = (0 : E) := by
      module
    rwa [heq] at h

  have hnonneg₁ : 0 ≤ (1 / t : ℝ) := by
    positivity
  have hfrac : (1 / t : ℝ) ≤ 1 := by
    apply (div_le_one htpos).2
    exact ht
  have hnonneg₂ : 0 ≤ (1 - 1 / t : ℝ) := sub_nonneg.mpr hfrac
  have hsum : (1 / t : ℝ) + (1 - 1 / t) = 1 := by
    ring

  have hscaled : (1 / t : ℝ) • x ∈ B := by
    have h :=
      hconv hx hzero hnonneg₁ hnonneg₂ hsum
    simpa using h

  apply Set.mem_smul_set.mpr
  refine ⟨(1 / t : ℝ) • x, hscaled, ?_⟩
  rw [smul_smul]
  have hmul : t * (1 / t : ℝ) = 1 := by
    field_simp [ht0]
  rw [hmul, one_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- The real algebra of Borell's lemma: from `u^(2/(t+1)) θ^(1 - 2/(t+1)) ≤ 1 - θ` with
`0 ≤ u`, `0 < θ < 1` and `t > 1`, deduce `u ≤ (1 - θ) ((1 - θ)/θ)^((t-1)/2)`. -/
theorem le_mul_rpow_of_rpow_mul_rpow_le {u θ t : ℝ} (hu : 0 ≤ u) (hθ : 0 < θ) (hθ1 : θ < 1)
    (ht : 1 < t) (h : u ^ (2 / (t + 1)) * θ ^ (1 - 2 / (t + 1)) ≤ 1 - θ) :
    u ≤ (1 - θ) * ((1 - θ) / θ) ^ ((t - 1) / 2) := by
  have hden : t + 1 ≠ 0 := by
    linarith

  have hp : 0 < (t + 1) / 2 := by
    positivity

  have hθpow : 0 < θ ^ (1 - 2 / (t + 1)) := by
    exact Real.rpow_pos_of_pos hθ _

  have hdiv :
      u ^ (2 / (t + 1)) ≤ (1 - θ) / θ ^ (1 - 2 / (t + 1)) := by
    exact (le_div_iff₀ hθpow).2 h

  have hraised :
      (u ^ (2 / (t + 1))) ^ ((t + 1) / 2) ≤
        ((1 - θ) / θ ^ (1 - 2 / (t + 1))) ^ ((t + 1) / 2) := by
    exact Real.rpow_le_rpow (by positivity) hdiv (le_of_lt hp)

  have hexp :
      (2 / (t + 1)) * ((t + 1) / 2) = 1 := by
    field_simp [hden]

  have hqexp :
      (1 - 2 / (t + 1)) * ((t + 1) / 2) = (t - 1) / 2 := by
    field_simp [hden]
    ring

  have hpq :
      (t + 1) / 2 = 1 + (t - 1) / 2 := by
    ring

  have hone : 0 < 1 - θ := by
    linarith

  have hθq : 0 ≤ θ ^ (1 - 2 / (t + 1)) := by
    positivity

  calc
    u = (u ^ (2 / (t + 1))) ^ ((t + 1) / 2) := by
      rw [← Real.rpow_mul hu, hexp, Real.rpow_one]
    _ ≤ ((1 - θ) / θ ^ (1 - 2 / (t + 1))) ^ ((t + 1) / 2) := hraised
    _ = (1 - θ) ^ ((t + 1) / 2) /
          θ ^ ((1 - 2 / (t + 1)) * ((t + 1) / 2)) := by
      rw [Real.div_rpow (le_of_lt hone) hθq]
      rw [← Real.rpow_mul hθ.le]
    _ = (1 - θ) ^ ((t + 1) / 2) / θ ^ ((t - 1) / 2) := by
      rw [hqexp]
    _ = (1 - θ) * ((1 - θ) ^ ((t - 1) / 2) / θ ^ ((t - 1) / 2)) := by
      rw [hpq, Real.rpow_add hone, Real.rpow_one]
      ring
    _ = (1 - θ) * ((1 - θ) / θ) ^ ((t - 1) / 2) := by
      rw [Real.div_rpow (le_of_lt hone) hθ.le]

theorem one_sub_measure_smul_le {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ)
    {B : Set E} (hB : MeasurableSet B) (hconv : Convex ℝ B) (hsymm : ∀ x ∈ B, -x ∈ B)
    (hθ : 1 / 2 < ((μ : Measure E) B).toReal) {t : ℝ} (ht : 1 ≤ t) :
    1 - ((μ : Measure E) (t • B)).toReal ≤
      (1 - ((μ : Measure E) B).toReal) *
        ((1 - ((μ : Measure E) B).toReal) / ((μ : Measure E) B).toReal) ^ ((t - 1) / 2) := by
  have hθle : ((μ : Measure E) B).toReal ≤ 1 := by
    have hprob : (μ : Measure E) B ≤ 1 := prob_le_one
    have hreal := ENNReal.toReal_mono (by finiteness) hprob
    simpa using hreal

  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  · by_cases hθeq : ((μ : Measure E) B).toReal = 1
    · have hsub : B ⊆ t • B :=
        subset_smul_of_one_le hconv hsymm (le_of_lt ht)
      have hmono : (μ : Measure E) B ≤ (μ : Measure E) (t • B) :=
        measure_mono hsub
      have hreal := ENNReal.toReal_mono (by finiteness) hmono
      have hle : 1 ≤ ((μ : Measure E) (t • B)).toReal := by
        simpa [hθeq] using hreal
      have hlhs : 1 - ((μ : Measure E) (t • B)).toReal ≤ 0 := by
        linarith
      simpa [hθeq] using hlhs
    · have hθlt : ((μ : Measure E) B).toReal < 1 :=
        lt_of_le_of_ne hθle hθeq
      have hθpos : 0 < ((μ : Measure E) B).toReal := by
        linarith
      have hprob_t : (μ : Measure E) (t • B) ≤ 1 := prob_le_one
      have hreal_t := ENNReal.toReal_mono (by finiteness) hprob_t
      have hmt : ((μ : Measure E) (t • B)).toReal ≤ 1 := by
        simpa using hreal_t
      have hu : 0 ≤ 1 - ((μ : Measure E) (t • B)).toReal := by
        linarith
      have hbase :=
        one_sub_measure_smul_rpow_mul_le hμ hB hconv hsymm ht
      exact
        le_mul_rpow_of_rpow_mul_rpow_le hu hθpos hθlt ht hbase

end FunctionalInequalities.KLS.LogConcave

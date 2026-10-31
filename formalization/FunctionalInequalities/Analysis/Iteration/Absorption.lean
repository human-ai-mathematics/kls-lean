module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Radius absorption iteration

The radius-absorption lemma used to close interior Schauder estimates (cf. Giaquinta–Martinazzi,
Lemma 6.1, and Han–Lin, Lemma 4.3; Gilbarg–Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Classics 2001 (ISBN 3-540-41160-7), reach the same absorption in the interior
estimates of Theorems 4.6 and 6.2 through weighted interior norms instead):

* `absorption_le_chain`: iterating `A r ≤ θ A r' + B / (r' - r) ^ k + C` along an increasing
  chain of radii `t 0 < t 1 < ⋯ ≤ R₀`;
* `exists_absorption_constant`: if `0 ≤ θ < 1`, `0 < k`, and a function `A`, nonnegative and
  bounded above on `(0, R₀]`, satisfies the recursion for all `0 < r < r' ≤ R₀`, then
  `A r ≤ c (B / (R₀ - r) ^ k + C)` on `(0, R₀)`, with `c > 0` depending only on `θ` and `k`.

Powers `(r' - r) ^ k` are real powers (`Real.rpow`). The proof uses the chain
`t i = r + (R₀ - r) (1 - τ ^ i)` with `τ ^ k = (1 + θ) / 2` and yields
`c = (1 - τ) ^ (-k) / (1 - θ τ ^ (-k))`, but only the existence of `c` and its dependence on
`(θ, k)` alone are stated. The nonnegativity hypothesis on `A` is part of the stated interface but
is not needed by the proof. No Schauder estimate is proved here.
-/

@[expose] public section

open Filter Topology Finset

namespace FunctionalInequalities.Analysis

/-- Iterating the absorption recursion along an increasing chain of radii in `(0, R₀]`. -/
theorem absorption_le_chain {θ k R₀ B C : ℝ} {A : ℝ → ℝ} (hθ0 : 0 ≤ θ)
    (hrec : ∀ r r' : ℝ, 0 < r → r < r' → r' ≤ R₀ → A r ≤ θ * A r' + B / (r' - r) ^ k + C)
    (t : ℕ → ℝ) (ht0 : ∀ i, 0 < t i) (hmono : ∀ i, t i < t (i + 1)) (hle : ∀ i, t i ≤ R₀)
    (N : ℕ) :
    A (t 0) ≤ θ ^ N * A (t N) +
      ∑ i ∈ range N, θ ^ i * (B / (t (i + 1) - t i) ^ k + C) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h := hrec (t N) (t (N + 1)) (ht0 N) (hmono N) (hle (N + 1))
    have hθN : 0 ≤ θ ^ N := pow_nonneg hθ0 N
    calc A (t 0)
        ≤ θ ^ N * A (t N) + ∑ i ∈ range N, θ ^ i * (B / (t (i + 1) - t i) ^ k + C) := ih
      _ ≤ θ ^ N * (θ * A (t (N + 1)) + B / (t (N + 1) - t N) ^ k + C) +
          ∑ i ∈ range N, θ ^ i * (B / (t (i + 1) - t i) ^ k + C) := by gcongr
      _ = θ ^ (N + 1) * A (t (N + 1)) +
          ∑ i ∈ range (N + 1), θ ^ i * (B / (t (i + 1) - t i) ^ k + C) := by
        rw [sum_range_succ, pow_succ]; ring

/--
**Radius absorption lemma.** Let `0 ≤ θ < 1` and `0 < k`. There is `c > 0`, depending only on
`θ` and `k`, such that for every `R₀ > 0`, `B, C ≥ 0` and every function `A`, nonnegative and
bounded
above on `(0, R₀]`, satisfying `A r ≤ θ A r' + B / (r' - r) ^ k + C` for all `0 < r < r' ≤ R₀`, one
has
`A r ≤ c (B / (R₀ - r) ^ k + C)` for all `0 < r < R₀`. -/
theorem exists_absorption_constant {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {k : ℝ} (hk : 0 < k) :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (R₀ : ℝ),
          0 < R₀ →
            ∀ (A : ℝ → ℝ) (B C : ℝ),
              0 ≤ B →
                0 ≤ C →
                  (∀ r ∈ Set.Ioc (0 : ℝ) R₀, 0 ≤ A r) →
                    (∃ Bd : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) R₀, A r ≤ Bd) →
                      (∀ r r' : ℝ,
                          0 < r → r < r' → r' ≤ R₀ → A r ≤ θ * A r' + B / (r' - r) ^ k + C) →
                        ∀ r ∈ Set.Ioo (0 : ℝ) R₀, A r ≤ c * (B / (R₀ - r) ^ k + C) := by
  -- the ratio `τ` with `τ ^ k = σ := (1 + θ) / 2 ∈ (θ, 1)`

  set σ : ℝ := (1 + θ) / 2 with hσ_def
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ < 1 := by linarith
  have hθσ : θ < σ := by linarith
  set τ : ℝ := σ ^ k⁻¹ with hτ_def
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hσ0 _
  have hτ1 : τ < 1 := Real.rpow_lt_one hσ0.le hσ1 (inv_pos.2 hk)
  have hτk : τ ^ k = σ := Real.rpow_inv_rpow hσ0.le hk.ne'
  set q : ℝ := θ / σ with hq_def
  have hq0 : 0 ≤ q := div_nonneg hθ0 hσ0.le
  have hq1 : q < 1 := (div_lt_one hσ0).2 hθσ
  have hθq : θ ≤ q := le_div_self hθ0 hσ0 hσ1.le
  set D : ℝ := (1 - τ) ^ k with hD_def
  have hD0 : 0 < D := Real.rpow_pos_of_pos (by linarith) _
  have hD1 : D ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hk.le
  have h1q : 0 < 1 - q := by linarith
  clear_value D q τ σ
  refine ⟨1 / (D * (1 - q)), by positivity, ?_⟩
  intro R₀ _hR₀ A B C hB hC _hA ⟨Bd, hBd⟩ hrec r hr
  obtain ⟨hr0, hrR⟩ := hr
  set P : ℝ := (R₀ - r) ^ k with hP_def
  have hP0 : 0 < P :=
    Real.rpow_pos_of_pos (by linarith)
      _
  -- the chain `t i = r + (R₀ - r) (1 - τ ^ i)`

  set t : ℕ → ℝ := fun i => r + (R₀ - r) * (1 - τ ^ i) with ht_def
  have hτi (i : ℕ) : 0 < τ ^ i := pow_pos hτ0 i
  have hτi1 (i : ℕ) : τ ^ i ≤ 1 := pow_le_one₀ hτ0.le hτ1.le
  have hstep (i : ℕ) : t (i + 1) - t i = (R₀ - r) * τ ^ i * (1 - τ) := by
    simp only [ht_def, pow_succ]; ring
  have ht0 (i : ℕ) : 0 < t i := by
    have : 0 ≤ (R₀ - r) * (1 - τ ^ i) := mul_nonneg (by linarith) (by linarith [hτi1 i])
    simp only [ht_def]; linarith
  have hmono (i : ℕ) : t i < t (i + 1) := by
    have : 0 < (R₀ - r) * τ ^ i * (1 - τ) :=
      mul_pos (mul_pos (by linarith) (hτi i)) (by linarith)
    linarith [hstep i]
  have hle (i : ℕ) : t i ≤ R₀ := by
    have : 0 ≤ (R₀ - r) * τ ^ i := mul_nonneg (by linarith) (hτi i).le
    simp only [ht_def]; nlinarith
  have hpow (i : ℕ) : (t (i + 1) - t i) ^ k = P * σ ^ i * D := by
    rw [hstep i, Real.mul_rpow (mul_nonneg (by linarith) (hτi i).le) (by linarith),
      Real.mul_rpow (by linarith) (hτi i).le, ← hτk, Real.rpow_pow_comm hτ0.le, hD_def]
  -- each term of the iterated sum is dominated by a geometric term

  have hterm (i : ℕ) : θ ^ i * (B / (t (i + 1) - t i) ^ k + C) ≤ (B / (P * D) + C) * q ^ i := by
    rw [hpow i]
    have hσi : 0 < σ ^ i := pow_pos hσ0 i
    have h1 : θ ^ i * (B / (P * σ ^ i * D)) = B / (P * D) * q ^ i := by
      rw [hq_def, div_pow];
      field_simp
    have h2 : θ ^ i * C ≤ C * q ^ i := by
      rw [mul_comm];
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ0 hθq i) hC
    calc
      θ ^ i * (B / (P * σ ^ i * D) + C) = θ ^ i * (B / (P * σ ^ i * D)) + θ ^ i * C := by ring
      _ ≤ B / (P * D) * q ^ i + C * q ^ i := by rw [h1]; linarith
      _ = (B / (P * D) + C) * q ^ i := by ring
  set M : ℝ := (B / (P * D) + C) / (1 - q) with hM_def
  have hM0 : 0 ≤ B / (P * D) + C := by positivity
  have hbound (N : ℕ) : A r ≤ θ ^ N * Bd + M := by
    have hchain := absorption_le_chain hθ0 hrec t ht0 hmono hle N
    have ht00 : t 0 = r := by simp [ht_def]
    rw [ht00] at hchain
    have hAN : θ ^ N * A (t N) ≤ θ ^ N * Bd :=
      mul_le_mul_of_nonneg_left (hBd _ ⟨ht0 N, hle N⟩) (pow_nonneg hθ0 N)
    have hsum : ∑ i ∈ range N, θ ^ i * (B / (t (i + 1) - t i) ^ k + C) ≤ M := by
      calc
        ∑ i ∈ range N, θ ^ i * (B / (t (i + 1) - t i) ^ k + C) ≤
            ∑ i ∈ range N, (B / (P * D) + C) * q ^ i :=
          sum_le_sum fun i _ => hterm i
        _ = (B / (P * D) + C) * ∑ i ∈ range N, q ^ i := by rw [mul_sum]
        _ ≤ (B / (P * D) + C) * (1 / (1 - q)) := by
          gcongr
          have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hq0 hq1
          rwa [← range_eq_Ico, pow_zero] at h
        _ = M := by rw [hM_def]; ring
    linarith
  have hlim : Tendsto (fun N : ℕ => θ ^ N * Bd + M) atTop (𝓝 (0 * Bd + M)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const Bd).add_const M
  have hAM : A r ≤ M := by simpa using ge_of_tendsto' hlim hbound
  calc
    A r ≤ M := hAM
    _ = B / P / (D * (1 - q)) + C / (1 - q) := by rw [hM_def]; field_simp
    _ ≤ B / P / (D * (1 - q)) + C / (D * (1 - q)) := by
      gcongr
      calc
        D * (1 - q) ≤ 1 * (1 - q) := by gcongr
        _ = 1 - q := one_mul _
    _ = 1 / (D * (1 - q)) * (B / P + C) := by ring

end FunctionalInequalities.Analysis

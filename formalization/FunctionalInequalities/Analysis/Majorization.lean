import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A majorization Gronwall comparison

Klartag–Lehec, *Thin-shell bounds via parallel coupling* (arXiv:2507.15495v2), Lemma 4.7: let
`μ₁, …, μₙ` and `λ₁ ≥ … ≥ λₙ` be nonnegative continuous functions on `[0, ∞)` such that for all
`t ≥ 0` and `k ≤ n`, `∑_{i ≤ k} μᵢ(t) ≤ ∑_{i ≤ k} [1 + 2 ∫₀ᵗ μᵢ λᵢ]`. Then
`∑_{i ≤ k} μᵢ(t) ≤ ∑_{i ≤ k} exp(2 ∫₀ᵗ λᵢ)` for all `t ≥ 0` and `k ≤ n`.

In Lean the functions `λᵢ` are written `ℓ i` (`λ` is a keyword), indices are `0, …, n - 1` and
the partial sums run over `Finset.range k`. The nonnegativity of the `μᵢ` is not needed and is
not assumed. The proof is the paper's induction on `k`: Abel summation turns the induction
hypothesis into a bound on `∑_{i < k} μᵢ (λᵢ - λₖ)`, and the function
`exp(-2 Λₖ) ∑_{i ≤ k} νᵢ - ∑_{i < k} exp(2 (Λᵢ - Λₖ))`, with `Λᵢ = ∫₀ᵗ λᵢ` and
`νᵢ = 1 + 2 ∫₀ᵗ μᵢ λᵢ`, is nonincreasing and equals `1` at `t = 0`.
-/

open Finset Set intervalIntegral
open MeasureTheory
open scoped Topology

namespace FunctionalInequalities.Analysis

/-- Abel summation for majorization: if the partial sums of `a` are dominated by those of `b` up
to `k` and the weights `w₀ ≥ w₁ ≥ … ≥ w_{k-1} ≥ 0` are nonincreasing, then
`∑_{i < k} aᵢ wᵢ ≤ ∑_{i < k} bᵢ wᵢ`. -/
theorem sum_mul_le_sum_mul_of_sum_le {k : ℕ} {a b w : ℕ → ℝ}
    (hab : ∀ j ≤ k, ∑ i ∈ range j, a i ≤ ∑ i ∈ range j, b i)
    (hw : ∀ i j, i ≤ j → j < k → w j ≤ w i) (hw0 : ∀ i < k, 0 ≤ w i) :
    ∑ i ∈ range k, a i * w i ≤ ∑ i ∈ range k, b i * w i := by
  induction k generalizing a b w with
  | zero =>
      simp
  | succ k ih =>
      have hdecomp : ∀ c : ℕ → ℝ,
          (∑ i ∈ range (k + 1), c i * w i) =
            (∑ i ∈ range k, c i * (w i - w k)) +
              w k * (∑ i ∈ range (k + 1), c i) := by
        intro c
        have hp :
            (∑ i ∈ range k, c i * (w i - w k)) =
              (∑ i ∈ range k, c i * w i) -
                (∑ i ∈ range k, c i) * w k := by
          calc
            (∑ i ∈ range k, c i * (w i - w k)) =
                ∑ i ∈ range k, (c i * w i - c i * w k) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = (∑ i ∈ range k, c i * w i) -
                ∑ i ∈ range k, c i * w k := by
                  rw [Finset.sum_sub_distrib]
            _ = (∑ i ∈ range k, c i * w i) -
                (∑ i ∈ range k, c i) * w k := by
                  rw [Finset.sum_mul]
        calc
          (∑ i ∈ range (k + 1), c i * w i) =
              (∑ i ∈ range k, c i * w i) + c k * w k := by
                rw [Finset.sum_range_succ]
          _ = (∑ i ∈ range k, c i * (w i - w k)) +
                w k * (∑ i ∈ range (k + 1), c i) := by
                rw [hp, Finset.sum_range_succ]
                ring

      have hab' : ∀ j ≤ k, ∑ i ∈ range j, a i ≤ ∑ i ∈ range j, b i := by
        intro j hj
        exact hab j (le_trans hj (Nat.le_succ k))

      have hw' : ∀ i j, i ≤ j → j < k → (w j - w k) ≤ (w i - w k) := by
        intro i j hij hj
        exact sub_le_sub_right (hw i j hij (lt_trans hj (Nat.lt_succ_self k))) _

      have hw0' : ∀ i < k, 0 ≤ w i - w k := by
        intro i hi
        exact sub_nonneg.mpr (hw i k (Nat.le_of_lt hi) (Nat.lt_succ_self k))

      have hIH :
          (∑ i ∈ range k, a i * (w i - w k)) ≤
            ∑ i ∈ range k, b i * (w i - w k) :=
        ih (a := a) (b := b) (w := fun i => w i - w k) hab' hw' hw0'

      have hlast :
          w k * (∑ i ∈ range (k + 1), a i) ≤
            w k * (∑ i ∈ range (k + 1), b i) := by
        exact mul_le_mul_of_nonneg_left (hab (k + 1) (le_rfl))
          (hw0 k (Nat.lt_succ_self k))

      rw [hdecomp a, hdecomp b]
      exact add_le_add hIH hlast

/-- The primitive `u ↦ ∫₀ᵘ f` of a function continuous on `[0, ∞)` is continuous on `[0, T]`. -/
theorem continuousOn_primitive_Icc {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun u => ∫ s in (0 : ℝ)..u, f s) (Icc 0 T) := by
  have h_int : IntegrableOn f (uIcc (0 : ℝ) T) volume := by
    rw [Set.uIcc_of_le hT]
    exact (hf.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
  simpa [Set.uIcc_of_le hT] using
    (intervalIntegral.continuousOn_primitive_interval
      (f := f) (a := (0 : ℝ)) (b := T) (μ := volume) h_int)

/-- The primitive `u ↦ ∫₀ᵘ f` has derivative `f t` at every `t > 0`. -/
theorem hasDerivAt_primitive_Ici {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, f s) (f t) t := by
  have hsub : uIcc (0 : ℝ) t ⊆ Ici 0 := by
    rw [uIcc_of_le (le_of_lt ht)]
    exact Icc_subset_Ici_self
  have h_int : IntervalIntegrable f volume (0 : ℝ) t :=
    (hf.mono hsub).intervalIntegrable
  have h_meas : StronglyMeasurableAtFilter f (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter (μ := volume)
      isOpen_Ioi (hf.mono Ioi_subset_Ici_self) t ht
  have h_cont : ContinuousAt f t :=
    hf.continuousAt (Ici_mem_nhds ht)
  exact intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont

/-- The derivative of the comparison quantity `exp(-2 L) S - ∑_{i < k} exp(2 (Λᵢ - L))`. -/
theorem hasDerivAt_exp_mul_sub_sum {k : ℕ} {S L : ℝ → ℝ} {Λ : ℕ → ℝ → ℝ} {u s l : ℝ}
    {dΛ : ℕ → ℝ} (hS : HasDerivAt S s u) (hL : HasDerivAt L l u)
    (hΛ : ∀ i < k, HasDerivAt (Λ i) (dΛ i) u) :
    HasDerivAt (fun v => Real.exp (-2 * L v) * S v - ∑ i ∈ range k, Real.exp (2 * (Λ i v - L v)))
      (Real.exp (-2 * L u) * (s - 2 * l * S u -
        ∑ i ∈ range k, 2 * Real.exp (2 * Λ i u) * (dΛ i - l))) u := by
  have hsum :
      HasDerivAt
        (fun v => ∑ i ∈ range k, Real.exp (2 * (Λ i v - L v)))
        (∑ i ∈ range k, Real.exp (2 * (Λ i u - L u)) * (2 * (dΛ i - l))) u := by
    apply HasDerivAt.fun_sum
    intro i hi
    simpa using
      (((hΛ i (Finset.mem_range.mp hi)).sub hL).const_mul 2).exp

  have hmain :=
    (((hL.const_mul (-2)).exp).mul hS).sub hsum

  have hexp (i : ℕ) :
      Real.exp (2 * (Λ i u - L u)) =
        Real.exp (-2 * L u) * Real.exp (2 * Λ i u) := by
    rw [← Real.exp_add]
    congr 1
    ring

  have hrew :
      (∑ i ∈ range k, Real.exp (2 * (Λ i u - L u)) * (2 * (dΛ i - l))) =
        ∑ i ∈ range k,
          (Real.exp (-2 * L u) * Real.exp (2 * Λ i u)) *
            (2 * (dΛ i - l)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hexp i]

  have hsum' :
      (∑ i ∈ range k,
          (Real.exp (-2 * L u) * Real.exp (2 * Λ i u)) *
            (2 * (dΛ i - l))) =
        Real.exp (-2 * L u) *
          (∑ i ∈ range k, 2 * Real.exp (2 * Λ i u) * (dΛ i - l)) := by
    calc
      (∑ i ∈ range k,
          (Real.exp (-2 * L u) * Real.exp (2 * Λ i u)) *
            (2 * (dΛ i - l))) =
          ∑ i ∈ range k,
            Real.exp (-2 * L u) *
              (2 * Real.exp (2 * Λ i u) * (dΛ i - l)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = Real.exp (-2 * L u) *
          (∑ i ∈ range k, 2 * Real.exp (2 * Λ i u) * (dΛ i - l)) := by
            rw [Finset.mul_sum]

  apply hmain.congr_deriv
  rw [hrew, hsum']
  ring

/-- A function continuous on `[0, t]` with nonpositive derivative on `(0, t)` satisfies
`Φ t ≤ Φ 0`. -/
theorem le_of_hasDerivAt_nonpos {Φ Φ' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hc : ContinuousOn Φ (Icc 0 t))
    (hd : ∀ u ∈ Ioo 0 t, HasDerivAt Φ (Φ' u) u) (hn : ∀ u ∈ Ioo 0 t, Φ' u ≤ 0) :
    Φ t ≤ Φ 0 := by
  have h :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) t) hc
      (fun u hu => by
        rw [interior_Icc] at hu
        exact (hd u hu).hasDerivWithinAt)
      (fun u hu => by
        rw [interior_Icc] at hu
        exact hn u hu)
  exact h (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht

/-- Continuity of the comparison quantity on `[0, t]`. -/
theorem continuousOn_exp_mul_sub_sum {k : ℕ} {S L : ℝ → ℝ} {Λ : ℕ → ℝ → ℝ} {t : ℝ}
    (hS : ContinuousOn S (Icc 0 t)) (hL : ContinuousOn L (Icc 0 t))
    (hΛ : ∀ i < k, ContinuousOn (Λ i) (Icc 0 t)) :
    ContinuousOn (fun v => Real.exp (-2 * L v) * S v -
      ∑ i ∈ range k, Real.exp (2 * (Λ i v - L v))) (Icc 0 t) := by
  have hmulL : ContinuousOn (fun v : ℝ => (-2 : ℝ) * L v) (Icc 0 t) := by
    exact continuousOn_const.mul hL

  have hexpL' :
      ContinuousOn (Real.exp ∘ (fun v : ℝ => (-2 : ℝ) * L v)) (Icc 0 t) := by
    exact Real.continuous_exp.comp_continuousOn hmulL

  have hexpL : ContinuousOn (fun v : ℝ => Real.exp (-2 * L v)) (Icc 0 t) := by
    exact hexpL'.congr (fun v hv => rfl)

  have hsum :
      ContinuousOn
        (fun v => ∑ i ∈ range k, Real.exp (2 * (Λ i v - L v)))
        (Icc 0 t) := by
    apply continuousOn_finsetSum
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hdiff : ContinuousOn (fun v : ℝ => Λ i v - L v) (Icc 0 t) :=
      (hΛ i hi').sub hL
    have hmul :
        ContinuousOn (fun v : ℝ => (2 : ℝ) * (Λ i v - L v)) (Icc 0 t) := by
      exact continuousOn_const.mul hdiff
    have hexp' :
        ContinuousOn
          (Real.exp ∘ (fun v : ℝ => (2 : ℝ) * (Λ i v - L v)))
          (Icc 0 t) := by
      exact Real.continuous_exp.comp_continuousOn hmul
    exact hexp'.congr (fun v hv => rfl)

  exact (hexpL.mul hS).sub hsum

/-- Comparison through a monotone quantity: if `S, L, Λ₀, …, Λ_{k-1}` are continuous on `[0, t]`
with derivatives `s, l, l₀, …` on `(0, t)` and
`s ≤ 2 l S + ∑_{i < k} 2 exp(2 Λᵢ) (lᵢ - l)` there, then
`exp(-2 L) S - ∑_{i < k} exp(2 (Λᵢ - L))` at `t` is at most its value at `0`. -/
theorem exp_mul_sub_sum_le {k : ℕ} {S L s l : ℝ → ℝ} {Λ dΛ : ℕ → ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hS : ContinuousOn S (Icc 0 t)) (hL : ContinuousOn L (Icc 0 t))
    (hΛ : ∀ i < k, ContinuousOn (Λ i) (Icc 0 t))
    (hS' : ∀ u ∈ Ioo 0 t, HasDerivAt S (s u) u) (hL' : ∀ u ∈ Ioo 0 t, HasDerivAt L (l u) u)
    (hΛ' : ∀ i < k, ∀ u ∈ Ioo 0 t, HasDerivAt (Λ i) (dΛ i u) u)
    (hle : ∀ u ∈ Ioo 0 t, s u ≤ 2 * l u * S u +
      ∑ i ∈ range k, 2 * Real.exp (2 * Λ i u) * (dΛ i u - l u)) :
    Real.exp (-2 * L t) * S t - ∑ i ∈ range k, Real.exp (2 * (Λ i t - L t)) ≤
      Real.exp (-2 * L 0) * S 0 - ∑ i ∈ range k, Real.exp (2 * (Λ i 0 - L 0)) := by
  apply le_of_hasDerivAt_nonpos ht
    (continuousOn_exp_mul_sub_sum hS hL hΛ)
    (fun u hu =>
      hasDerivAt_exp_mul_sub_sum (hS' u hu) (hL' u hu)
        (fun i hi => hΛ' i hi u hu))
  intro u hu
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by
    linarith [hle u hu])

/-- The pointwise inequality behind the induction step: at a fixed time, with
`Eᵢ = exp(2 ∫₀ᵗ λᵢ)` and `νᵢ = 1 + 2 ∫₀ᵗ μᵢ λᵢ`,
`∑_{i ≤ k} μᵢ λᵢ ≤ λₖ ∑_{i ≤ k} νᵢ + ∑_{i < k} Eᵢ (λᵢ - λₖ)`. -/
theorem sum_mul_le_of_majorization {k : ℕ} {m l e v : ℕ → ℝ}
    (hl : ∀ i j, i ≤ j → j ≤ k → l j ≤ l i) (hl0 : 0 ≤ l k)
    (hmv : ∑ i ∈ range (k + 1), m i ≤ ∑ i ∈ range (k + 1), v i)
    (hme : ∀ j ≤ k, ∑ i ∈ range j, m i ≤ ∑ i ∈ range j, e i) :
    ∑ i ∈ range (k + 1), m i * l i ≤
      l k * ∑ i ∈ range (k + 1), v i + ∑ i ∈ range k, e i * (l i - l k) := by
  have hdecomp : ∀ c : ℕ → ℝ,
      (∑ i ∈ range (k + 1), c i * l i) =
        (∑ i ∈ range k, c i * (l i - l k)) +
          l k * (∑ i ∈ range (k + 1), c i) := by
    intro c
    have hp :
        (∑ i ∈ range k, c i * (l i - l k)) =
          (∑ i ∈ range k, c i * l i) -
            (∑ i ∈ range k, c i) * l k := by
      calc
        (∑ i ∈ range k, c i * (l i - l k)) =
            ∑ i ∈ range k, (c i * l i - c i * l k) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (∑ i ∈ range k, c i * l i) -
            ∑ i ∈ range k, c i * l k := by
              rw [Finset.sum_sub_distrib]
        _ = (∑ i ∈ range k, c i * l i) -
            (∑ i ∈ range k, c i) * l k := by
              rw [Finset.sum_mul]
    calc
      (∑ i ∈ range (k + 1), c i * l i) =
          (∑ i ∈ range k, c i * l i) + c k * l k := by
            rw [Finset.sum_range_succ]
      _ = (∑ i ∈ range k, c i * (l i - l k)) +
          l k * (∑ i ∈ range (k + 1), c i) := by
            rw [hp, Finset.sum_range_succ]
            ring

  have hw : ∀ i j, i ≤ j → j < k → (l j - l k) ≤ (l i - l k) := by
    intro i j hij hj
    exact sub_le_sub_right (hl i j hij (Nat.le_of_lt hj)) _

  have hw0 : ∀ i < k, 0 ≤ l i - l k := by
    intro i hi
    exact sub_nonneg.mpr (hl i k (Nat.le_of_lt hi) le_rfl)

  have hIH :
      (∑ i ∈ range k, m i * (l i - l k)) ≤
        ∑ i ∈ range k, e i * (l i - l k) :=
    sum_mul_le_sum_mul_of_sum_le
      (k := k) (a := m) (b := e) (w := fun i => l i - l k)
      hme hw hw0

  have hlast :
      l k * (∑ i ∈ range (k + 1), m i) ≤
        l k * (∑ i ∈ range (k + 1), v i) :=
    mul_le_mul_of_nonneg_left hmv hl0

  calc
    ∑ i ∈ range (k + 1), m i * l i =
        (∑ i ∈ range k, m i * (l i - l k)) +
          l k * (∑ i ∈ range (k + 1), m i) := hdecomp m
    _ ≤ (∑ i ∈ range k, e i * (l i - l k)) +
          l k * (∑ i ∈ range (k + 1), v i) :=
      add_le_add hIH hlast
    _ = l k * ∑ i ∈ range (k + 1), v i +
          ∑ i ∈ range k, e i * (l i - l k) := by
      ring

/-- The induction step of Lemma 4.7 in integrated form: if the conclusion holds for every
`j ≤ k` and the hypothesis holds at `k + 1`, then
`∑_{i ≤ k} νᵢ(t) ≤ ∑_{i ≤ k} exp(2 ∫₀ᵗ λᵢ)` with `νᵢ(t) = 1 + 2 ∫₀ᵗ μᵢ λᵢ`. -/
theorem sum_le_sum_exp_step {n k : ℕ} (hk : k + 1 ≤ n) {μ ℓ : ℕ → ℝ → ℝ}
    (hμc : ∀ i < n, ContinuousOn (μ i) (Ici 0)) (hℓc : ∀ i < n, ContinuousOn (ℓ i) (Ici 0))
    (hℓ0 : ∀ i < n, ∀ t, 0 ≤ t → 0 ≤ ℓ i t)
    (hℓ : ∀ t, 0 ≤ t → ∀ i j, i ≤ j → j < n → ℓ j t ≤ ℓ i t)
    (hyp : ∀ t, 0 ≤ t → ∑ i ∈ range (k + 1), μ i t ≤
      ∑ i ∈ range (k + 1), (1 + 2 * ∫ s in (0 : ℝ)..t, μ i s * ℓ i s))
    (ih : ∀ j ≤ k, ∀ t, 0 ≤ t → ∑ i ∈ range j, μ i t ≤
      ∑ i ∈ range j, Real.exp (2 * ∫ s in (0 : ℝ)..t, ℓ i s))
    {t : ℝ} (ht : 0 ≤ t) :
    ∑ i ∈ range (k + 1), (1 + 2 * ∫ s in (0 : ℝ)..t, μ i s * ℓ i s) ≤
      ∑ i ∈ range (k + 1), Real.exp (2 * ∫ s in (0 : ℝ)..t, ℓ i s) := by
  let Λ : ℕ → ℝ → ℝ := fun i u => ∫ s in (0 : ℝ)..u, ℓ i s
  let I : ℕ → ℝ → ℝ := fun i u => ∫ s in (0 : ℝ)..u, μ i s * ℓ i s
  let S : ℝ → ℝ := fun u => ∑ i ∈ range (k + 1), (1 + 2 * I i u)

  have hidx : ∀ i < k + 1, i < n := by
    intro i hi
    exact lt_of_lt_of_le hi hk

  have hI_cont : ∀ i < k + 1, ContinuousOn (I i) (Icc 0 t) := by
    intro i hi
    apply continuousOn_primitive_Icc
    · exact (hμc i (hidx i hi)).mul (hℓc i (hidx i hi))
    · exact ht

  have hΛ_cont : ∀ i < k, ContinuousOn (Λ i) (Icc 0 t) := by
    intro i hi
    apply continuousOn_primitive_Icc
    · exact hℓc i (hidx i (lt_trans hi (Nat.lt_succ_self k)))
    · exact ht

  have hS_cont : ContinuousOn S (Icc 0 t) := by
    dsimp [S]
    apply continuousOn_finsetSum
    intro i hi
    have hi' : i < k + 1 := Finset.mem_range.mp hi
    exact continuousOn_const.add (continuousOn_const.mul (hI_cont i hi'))

  have hL_cont : ContinuousOn (Λ k) (Icc 0 t) := by
    apply continuousOn_primitive_Icc
    · exact hℓc k (hidx k (Nat.lt_succ_self k))
    · exact ht

  have hS_deriv :
      ∀ u ∈ Ioo 0 t,
        HasDerivAt S
          (∑ i ∈ range (k + 1), 2 * (μ i u * ℓ i u)) u := by
    intro u hu
    dsimp [S]
    apply HasDerivAt.fun_sum
    intro i hi
    have hi' : i < k + 1 := Finset.mem_range.mp hi
    have hprim :
        HasDerivAt (I i) (μ i u * ℓ i u) u := by
      dsimp [I]
      apply hasDerivAt_primitive_Ici
      · exact (hμc i (hidx i hi')).mul (hℓc i (hidx i hi'))
      · exact hu.1
    simpa using (hprim.const_mul 2).const_add 1

  have hL_deriv :
      ∀ u ∈ Ioo 0 t, HasDerivAt (Λ k) (ℓ k u) u := by
    intro u hu
    dsimp [Λ]
    apply hasDerivAt_primitive_Ici
    · exact hℓc k (hidx k (Nat.lt_succ_self k))
    · exact hu.1

  have hΛ_deriv :
      ∀ i < k, ∀ u ∈ Ioo 0 t, HasDerivAt (Λ i) (ℓ i u) u := by
    intro i hi u hu
    dsimp [Λ]
    apply hasDerivAt_primitive_Ici
    · exact hℓc i (hidx i (lt_trans hi (Nat.lt_succ_self k)))
    · exact hu.1

  have hle :
      ∀ u ∈ Ioo 0 t,
        (∑ i ∈ range (k + 1), 2 * (μ i u * ℓ i u)) ≤
          2 * ℓ k u * S u +
            ∑ i ∈ range k, 2 * Real.exp (2 * Λ i u) *
              (ℓ i u - ℓ k u) := by
    intro u hu
    have hu0 : 0 ≤ u := le_of_lt hu.1
    have hmaj :
        ∑ i ∈ range (k + 1), μ i u * ℓ i u ≤
          ℓ k u * ∑ i ∈ range (k + 1), (1 + 2 * I i u) +
            ∑ i ∈ range k, Real.exp (2 * Λ i u) * (ℓ i u - ℓ k u) := by
      apply sum_mul_le_of_majorization
      · intro i j hij hj
        exact hℓ u hu0 i j hij (lt_of_le_of_lt hj hk)
      · exact hℓ0 k (hidx k (Nat.lt_succ_self k)) u hu0
      · simpa [I] using hyp u hu0
      · intro j hj
        simpa [Λ] using ih j hj u hu0
    have hsum :
        2 * ∑ i ∈ range k,
            Real.exp (2 * Λ i u) * (ℓ i u - ℓ k u) =
          ∑ i ∈ range k,
            2 * Real.exp (2 * Λ i u) * (ℓ i u - ℓ k u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    calc
      ∑ i ∈ range (k + 1), 2 * (μ i u * ℓ i u)
          = 2 * (∑ i ∈ range (k + 1), μ i u * ℓ i u) := by
              rw [Finset.mul_sum]
      _ ≤ 2 * (ℓ k u * ∑ i ∈ range (k + 1), (1 + 2 * I i u) +
            ∑ i ∈ range k, Real.exp (2 * Λ i u) * (ℓ i u - ℓ k u)) :=
        mul_le_mul_of_nonneg_left hmaj (by norm_num)
      _ = 2 * ℓ k u * S u +
            ∑ i ∈ range k, 2 * Real.exp (2 * Λ i u) *
              (ℓ i u - ℓ k u) := by
        dsimp [S]
        rw [mul_add, hsum]
        ring

  have hcomp :
      Real.exp (-2 * Λ k t) * S t -
          ∑ i ∈ range k, Real.exp (2 * (Λ i t - Λ k t)) ≤
        Real.exp (-2 * Λ k 0) * S 0 -
          ∑ i ∈ range k, Real.exp (2 * (Λ i 0 - Λ k 0)) := by
    apply exp_mul_sub_sum_le ht hS_cont hL_cont hΛ_cont
    · exact hS_deriv
    · exact hL_deriv
    · exact hΛ_deriv
    · simpa [S, Λ, I] using hle

  have hcomp' :
      Real.exp (-2 * Λ k t) * S t -
          ∑ i ∈ range k, Real.exp (2 * (Λ i t - Λ k t)) ≤ 1 := by
    simpa [S, Λ, I] using hcomp

  have hmul :=
    mul_le_mul_of_nonneg_left hcomp' (Real.exp_pos (2 * Λ k t)).le

  have hcancel :
      Real.exp (2 * Λ k t) * Real.exp (-2 * Λ k t) = 1 := by
    rw [← Real.exp_add]
    have hz : 2 * Λ k t + -2 * Λ k t = 0 := by ring
    rw [hz, Real.exp_zero]

  have hright :
      Real.exp (2 * Λ k t) *
          ∑ i ∈ range k, Real.exp (2 * (Λ i t - Λ k t)) =
        ∑ i ∈ range k, Real.exp (2 * Λ i t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.exp_add]
    congr 1
    ring

  have hmul' :
      S t - ∑ i ∈ range k, Real.exp (2 * Λ i t) ≤
        Real.exp (2 * Λ k t) := by
    calc
      S t - ∑ i ∈ range k, Real.exp (2 * Λ i t) =
          Real.exp (2 * Λ k t) *
              (Real.exp (-2 * Λ k t) * S t) -
            Real.exp (2 * Λ k t) *
              ∑ i ∈ range k, Real.exp (2 * (Λ i t - Λ k t)) := by
        rw [hright]
        rw [← mul_assoc, hcancel, one_mul]
      _ = Real.exp (2 * Λ k t) *
          (Real.exp (-2 * Λ k t) * S t -
            ∑ i ∈ range k, Real.exp (2 * (Λ i t - Λ k t))) := by
        rw [mul_sub]
      _ ≤ Real.exp (2 * Λ k t) * 1 := hmul
      _ = Real.exp (2 * Λ k t) := by ring

  have hfinal :
      S t ≤ ∑ i ∈ range (k + 1), Real.exp (2 * Λ i t) := by
    rw [Finset.sum_range_succ]
    linarith

  simpa [S, I, Λ] using hfinal

/-- Klartag–Lehec (2025), Lemma 4.7: the majorization Gronwall comparison. -/
theorem sum_le_sum_exp {n : ℕ} {μ ℓ : ℕ → ℝ → ℝ}
    (hμc : ∀ i < n, ContinuousOn (μ i) (Ici 0)) (hℓc : ∀ i < n, ContinuousOn (ℓ i) (Ici 0))
    (hℓ0 : ∀ i < n, ∀ t, 0 ≤ t → 0 ≤ ℓ i t)
    (hℓ : ∀ t, 0 ≤ t → ∀ i j, i ≤ j → j < n → ℓ j t ≤ ℓ i t)
    (hyp : ∀ t, 0 ≤ t → ∀ k ≤ n, ∑ i ∈ range k, μ i t ≤
      ∑ i ∈ range k, (1 + 2 * ∫ s in (0 : ℝ)..t, μ i s * ℓ i s))
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : k ≤ n) :
    ∑ i ∈ range k, μ i t ≤ ∑ i ∈ range k, Real.exp (2 * ∫ s in (0 : ℝ)..t, ℓ i s) := by
  have H :
      ∀ q : ℕ, ∀ t : ℝ, 0 ≤ t → q ≤ n →
        ∑ i ∈ range q, μ i t ≤
          ∑ i ∈ range q, Real.exp (2 * ∫ s in (0 : ℝ)..t, ℓ i s) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro t ht hq
        by_cases hq0 : q = 0
        · subst q
          simp
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
          have hstep :
              ∑ i ∈ range (m + 1),
                  (1 + 2 * ∫ s in (0 : ℝ)..t, μ i s * ℓ i s) ≤
                ∑ i ∈ range (m + 1),
                  Real.exp (2 * ∫ s in (0 : ℝ)..t, ℓ i s) := by
            apply sum_le_sum_exp_step (n := n) (k := m) hq hμc hℓc hℓ0 hℓ
            · intro t' ht'
              exact hyp t' ht' (m + 1) hq
            · intro j hj t' ht'
              have hjn : j ≤ n := by
                exact le_trans hj (le_trans (Nat.le_succ m) hq)
              exact ih j (Nat.lt_succ_of_le hj) t' ht' hjn
            · exact ht
          exact le_trans (hyp t ht (m + 1) hq) hstep
  exact H k t ht hk

end FunctionalInequalities.Analysis

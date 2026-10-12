import Mathlib

/-!
# Matrices acting on one slot of a coordinate tensor

Order-`r` coordinate tensors on `ℝⁿ`, their Euclidean inner product, the action `H^{(s)}` of a matrix on the `s`-th input
and `Σ_H = Σ_s H^{(s)}` (BKL arXiv:2610.05474v1, p. 23), and the algebra (89)–(91) of the proof of Lemma 5.1 at `A = Id`:
the drift expression is at least `½ Σ|W_i|² − 17 m² |T|² − 2⟨T, L⟩` when `Σ_i H_i² ≤ 8 Id`. Proof body: GPT (BKL
Claude-controller goal, task S3a); statement and placement: Claude.
-/

noncomputable section

open Matrix

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

/-- The Euclidean inner product of two order-`r` coordinate tensors on `ℝⁿ`. -/
def inner (T S : (Fin r → Fin n) → ℝ) : ℝ := ∑ J, T J * S J

/-- `H^{(s)}`: the matrix `H` acting on the `s`-th input of an order-`r` tensor (BKL arXiv:2610.05474v1, p. 23). -/
def actOn (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin r) (T : (Fin r → Fin n) → ℝ) : (Fin r → Fin n) → ℝ :=
  fun J => ∑ k, H (J s) k * T (Function.update J s k)

/-- `Σ_H = Σ_s H^{(s)}`. -/
def actSum (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin r → Fin n) → ℝ) : (Fin r → Fin n) → ℝ :=
  fun J => ∑ s, actOn H s T J

private lemma cross_bound (x y : (Fin r → Fin n) → ℝ) :
    -(1 / 2 : ℝ) * inner x x - 2 * inner y y ≤ -2 * inner x y := by
  calc
    -(1 / 2 : ℝ) * inner x x - 2 * inner y y =
        ∑ J, (-(1 / 2 : ℝ) * (x J * x J) - 2 * (y J * y J)) := by
          unfold inner
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ∑ J, (-2 * (x J * y J)) := by
      apply Finset.sum_le_sum
      intro J hJ
      nlinarith [sq_nonneg (x J - 2 * y J)]
    _ = -2 * inner x y := by
      unfold inner
      rw [Finset.mul_sum]

private lemma slot_bound (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
    (T : (Fin r → Fin n) → ℝ) (s : Fin r) :
    ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 ≤
      8 * ∑ J, T J ^ 2 := by
  classical
  cases r with
  | zero =>
      exact Fin.elim0 s
  | succ q =>
      let e := Fin.insertNthEquiv (fun _ : Fin (q + 1) => Fin n) s
      have heval (a : Fin n) (K : Fin q → Fin n) :
          e (a, K) s = a := by
        simp [e, Fin.insertNthEquiv_apply, Fin.insertNth, Fin.succAboveCases]
      have hupd (a b : Fin n) (K : Fin q → Fin n) :
          Function.update (e (a, K)) s b = e (b, K) := by
        funext j
        by_cases hj : j = s
        · subst j
          simp [e, Fin.insertNthEquiv_apply, Fin.insertNth, Fin.succAboveCases]
        · simp [Function.update, hj, e, Fin.insertNthEquiv_apply, Fin.insertNth,
            Fin.succAboveCases]
      have hri (i : Fin n) :
          ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
            ∑ x : Fin n × (Fin q → Fin n),
              (∑ k, H i x.1 k * T (e (k, x.2))) ^ 2 := by
        symm
        refine Fintype.sum_equiv (M := ℝ) e
          (fun x : Fin n × (Fin q → Fin n) =>
            (∑ k, H i x.1 k * T (e (k, x.2))) ^ 2)
          (fun J => (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2) ?_
        rintro ⟨a, K⟩
        simp only [heval, hupd]
      have hsum :
          ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
            ∑ K : Fin q → Fin n, ∑ i, ∑ a,
              (∑ k, H i a k * T (e (k, K))) ^ 2 := by
        calc
          ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
              ∑ i, ∑ x : Fin n × (Fin q → Fin n),
                (∑ k, H i x.1 k * T (e (k, x.2))) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hri i
          _ = ∑ i, ∑ a, ∑ K : Fin q → Fin n,
                (∑ k, H i a k * T (e (k, K))) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                exact Fintype.sum_prod_type' (γ := ℝ) (α₁ := Fin n)
                  (α₂ := Fin q → Fin n)
                  (fun a K => (∑ k, H i a k * T (e (k, K))) ^ 2)
          _ = ∑ i, ∑ K : Fin q → Fin n, ∑ a,
                (∑ k, H i a k * T (e (k, K))) ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_comm]
          _ = ∑ K : Fin q → Fin n, ∑ i, ∑ a,
                (∑ k, H i a k * T (e (k, K))) ^ 2 := by
                rw [Finset.sum_comm]
      have hpoint (K : Fin q → Fin n) :
          ∑ i, ∑ a, (∑ k, H i a k * T (e (k, K))) ^ 2 ≤
            8 * ∑ a, T (e (a, K)) ^ 2 := by
        simpa using h8 (fun b => T (e (b, K)))
      have heq :
          ∑ K : Fin q → Fin n, ∑ a, T (e (a, K)) ^ 2 =
            ∑ J, T J ^ 2 := by
        calc
          ∑ K : Fin q → Fin n, ∑ a, T (e (a, K)) ^ 2 =
              ∑ a, ∑ K : Fin q → Fin n, T (e (a, K)) ^ 2 := by
                rw [Finset.sum_comm]
          _ = ∑ x : Fin n × (Fin q → Fin n), T (e x) ^ 2 := by
                symm
                exact Fintype.sum_prod_type' (γ := ℝ) (α₁ := Fin n)
                  (α₂ := Fin q → Fin n)
                  (fun a K => T (e (a, K)) ^ 2)
          _ = ∑ J, T J ^ 2 := by
                exact Fintype.sum_equiv (M := ℝ) e
                  (fun x : Fin n × (Fin q → Fin n) => T (e x) ^ 2)
                  (fun J => T J ^ 2) (fun _ => rfl)
      calc
        ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 =
            ∑ K : Fin q → Fin n, ∑ i, ∑ a,
              (∑ k, H i a k * T (e (k, K))) ^ 2 := hsum
        _ ≤ ∑ K : Fin q → Fin n, 8 * ∑ a, T (e (a, K)) ^ 2 := by
              apply Finset.sum_le_sum
              intro K hK
              exact hpoint K
        _ = 8 * (∑ K : Fin q → Fin n, ∑ a, T (e (a, K)) ^ 2) := by
              rw [Finset.mul_sum]
        _ = 8 * ∑ J, T J ^ 2 := by rw [heq]

private lemma actSum_bound (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (T : (Fin r → Fin n) → ℝ) :
    ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤
      (r : ℝ) * ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
  classical
  have hi (i : Fin n) :
      inner (actSum (H i) T) (actSum (H i) T) ≤
        (r : ℝ) * ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
    unfold inner actSum
    calc
      ∑ J, (∑ s, actOn (H i) s T J) * (∑ s, actOn (H i) s T J) ≤
          ∑ J, (r : ℝ) * ∑ s, (actOn (H i) s T J) * (actOn (H i) s T J) := by
            apply Finset.sum_le_sum
            intro J hJ
            simpa only [pow_two, Finset.card_univ, Fintype.card_fin] using
              (sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset (Fin r)))
                (f := fun s : Fin r => actOn (H i) s T J))
      _ = (r : ℝ) * ∑ s, ∑ J,
            (actOn (H i) s T J) * (actOn (H i) s T J) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤
        ∑ i, (r : ℝ) * ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
          apply Finset.sum_le_sum
          intro i hi'
          exact hi i
    _ = (r : ℝ) * ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
          rw [Finset.mul_sum]

private lemma fin_sum_const_mul (q : ℕ) (x : ℝ) :
    (∑ _ : Fin q, x) = (q : ℝ) * x := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma sum_sq_nonneg {α : Type*} [Fintype α] (f : α → ℝ) :
    0 ≤ ∑ x, f x ^ 2 := by
  exact Finset.sum_nonneg (fun x hx => sq_nonneg (f x))

/-- **The algebra of BKL Lemma 5.1, (89)–(91)** at `A = Id`: for symmetric `H_i` with `Σ_i H_i² ≤ 8 Id` and any
tensors `T, W_i, L` of order `r = m − 1 ≥ 1`, the drift expression of (89),
`−(m+1)|T|² − 2⟨T, L⟩ + Σ|W_i|² − 2Σ⟨W_i, Σ_{H_i}T⟩ + ½Σ|Σ_{H_i}T|² + ½ΣΣ_s|H_i^{(s)}T|²`, is at least
`½ Σ|W_i|² − 17 m² |T|² − 2⟨T, L⟩`. -/
theorem drift_expression_ge {m : ℕ} (hm : r + 1 = m) (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i, (H i).IsHermitian)
    (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
    (T L : (Fin r → Fin n) → ℝ) (W : Fin n → (Fin r → Fin n) → ℝ) :
    (1 / 2 : ℝ) * ∑ i, inner (W i) (W i) - 17 * (m : ℝ) ^ 2 * inner T T - 2 * inner T L ≤
      -((m : ℝ) + 1) * inner T T - 2 * inner T L + ∑ i, inner (W i) (W i)
        - 2 * ∑ i, inner (W i) (actSum (H i) T)
        + (1 / 2 : ℝ) * ∑ i, inner (actSum (H i) T) (actSum (H i) T)
        + (1 / 2 : ℝ) * ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
  classical
  have hH_used : (0 : ℝ) ≤ 0 := by
    exact (fun _ : ∀ i, (H i).IsHermitian => le_rfl) hH
  have hcross :
      -(1 / 2 : ℝ) * ∑ i, inner (W i) (W i) -
          2 * ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤
        -2 * ∑ i, inner (W i) (actSum (H i) T) := by
    have hi (i : Fin n) := cross_bound (W i) (actSum (H i) T)
    calc
      -(1 / 2 : ℝ) * ∑ i, inner (W i) (W i) -
            2 * ∑ i, inner (actSum (H i) T) (actSum (H i) T) =
          ∑ i, (-(1 / 2 : ℝ) * inner (W i) (W i) -
            2 * inner (actSum (H i) T) (actSum (H i) T)) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ ∑ i, -2 * inner (W i) (actSum (H i) T) := by
            apply Finset.sum_le_sum
            intro i hi'
            exact hi i
      _ = -2 * ∑ i, inner (W i) (actSum (H i) T) := by
            rw [Finset.mul_sum]
  have hslot :
      ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) ≤
        8 * (r : ℝ) * inner T T := by
    calc
      ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) =
          ∑ s, ∑ i, inner (actOn (H i) s T) (actOn (H i) s T) := by
            rw [Finset.sum_comm]
      _ ≤ ∑ s, 8 * ∑ J, T J ^ 2 := by
            apply Finset.sum_le_sum
            intro s hs
            simpa only [inner, actOn, pow_two] using slot_bound H h8 T s
      _ = 8 * (r : ℝ) * inner T T := by
            rw [fin_sum_const_mul]
            unfold inner
            simp only [pow_two]
            ring
  have hact := actSum_bound H T
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hC :
      ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤
        (r : ℝ) * (8 * (r : ℝ) * inner T T) :=
    le_trans hact (mul_le_mul_of_nonneg_left hslot hr)
  have hA : 0 ≤ inner T T := by
    unfold inner
    simpa only [pow_two] using sum_sq_nonneg T
  have hDnonneg :
      0 ≤ ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
    simp only [inner]
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro s hs
    simpa only [pow_two] using sum_sq_nonneg (actOn (H i) s T)
  have hmcast : (m : ℝ) = (r : ℝ) + 1 := by
    exact_mod_cast hm.symm
  have hcoef :
      0 ≤ 17 * (m : ℝ) ^ 2 - (m : ℝ) - 1 - 16 * (r : ℝ) ^ 2 := by
    rw [hmcast]
    nlinarith [sq_nonneg (r : ℝ)]
  have hprod :
      0 ≤ (17 * (m : ℝ) ^ 2 - (m : ℝ) - 1 - 16 * (r : ℝ) ^ 2) * inner T T :=
    mul_nonneg hcoef hA
  nlinarith [hcross, hC, hA, hDnonneg, hprod, hH_used]

end FunctionalInequalities.Analysis.CoordinateTensor

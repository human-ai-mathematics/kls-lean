import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The dyadic summation in the proof of BKL Theorem 3.1

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Theorem 3.1, p. 17: the recursion (63)
between the degree-`d` and degree-`2d` quantities is summed along the dyadic degrees
`d = 1, 2, 4, …`. This file isolates that step as a statement about real sequences.

## What is proved

* `le_of_dyadic_recursion`: let `S : ℕ → ℝ` vanish from some index `N` on, let `x` be any real
  number and `0 ≤ A`, `0 ≤ y ≤ 1/100`. If for every `d ≥ 1`
  `x^(d-1) S(d) ≤ x^(2d-1) S(2d) + A d y^d`, then `S(1) ≤ A / 90`.

The intended instance is `x = cλ`, `y = c²λR²`, with the source's (63) multiplied by
`(cλ)^(d-1)`.

## The argument

Put `T(d) = x^(d-1) S(d)`; the recursion reads `T(d) ≤ T(2d) + A d y^d`. Applying it at
`d = 2^j` for `j < m` and chaining gives
`S(1) = T(1) ≤ T(2^m) + A Σ_{j<m} 2^j y^(2^j)` (`le_dyadic_chain`). With `m = N` we have
`2^m ≥ N`, so `S(2^m) = 0`. Since `y ≤ 1/100` and the dyadic indices are a subfamily of
`ℕ`, `Σ_{j<m} 2^j y^(2^j) ≤ Σ_{d} d (1/100)^d = (1/100)/(1 - 1/100)² = 100/9801 < 1/90`
(`sum_dyadic_le`).

## What this is not

This is only the elementary summation. It does not prove the recursion (63), the bounds on the
iterates feeding it, or Theorem 3.1 itself. The hypotheses `0 ≤ S d` and `x ≤ 1` of the main
theorem are not used by the argument; they are kept to match the source's setting.
-/

namespace FunctionalInequalities.Analysis

open Finset

/-- Chaining the dyadic recursion `m` times: with `T(d) = x^(d-1) S(d)`,
`S(1) ≤ T(2^m) + A Σ_{j<m} 2^j y^(2^j)`. -/
private theorem le_dyadic_chain {S : ℕ → ℝ} {x y A : ℝ}
    (hrec : ∀ d, 1 ≤ d → x ^ (d - 1) * S d ≤ x ^ (2 * d - 1) * S (2 * d) + A * d * y ^ d)
    (m : ℕ) :
    S 1 ≤ x ^ (2 ^ m - 1) * S (2 ^ m) +
      A * ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := hrec (2 ^ m) (Nat.one_le_two_pow)
    rw [sum_range_succ, pow_succ' 2 m, mul_add]
    linarith [ih, h]

/-- The dyadic partial sums are bounded by `Σ_d d (1/100)^d = 100/9801 ≤ 1/90`. -/
private theorem sum_dyadic_le {y : ℝ} (hy : 0 ≤ y) (hy1 : 100 * y ≤ 1) (m : ℕ) :
    ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j) ≤ 1 / 90 := by
  set r : ℝ := 1 / 100 with hr
  have hyr : y ≤ r := by rw [hr]; linarith
  have hnorm : ‖r‖ < 1 := by rw [hr, Real.norm_eq_abs]; norm_num
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j) (range m : Set ℕ) :=
    fun a _ b _ hab => Nat.pow_right_injective le_rfl hab
  calc ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j)
      ≤ ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * r ^ (2 ^ j) := by
        gcongr
    _ = ∑ d ∈ (range m).image (fun j : ℕ => 2 ^ j), ((d : ℕ) : ℝ) * r ^ d :=
        (sum_image (f := fun d : ℕ => (d : ℝ) * r ^ d) hinj).symm
    _ ≤ ∑' d : ℕ, (d : ℝ) * r ^ d :=
        hsum.summable.sum_le_tsum _ (fun d _ => by positivity)
    _ = r / (1 - r) ^ 2 := hsum.tsum_eq
    _ ≤ 1 / 90 := by rw [hr]; norm_num

/-- **The dyadic summation of BKL Theorem 3.1** (arXiv:2610.05474v1, p. 17). If `S` vanishes
from `N` on, `0 ≤ x ≤ 1`, `0 ≤ A`, `0 ≤ y ≤ 1/100`, and
`x^(d-1) S(d) ≤ x^(2d-1) S(2d) + A d y^d` for all `d ≥ 1`, then `S(1) ≤ A / 90`. -/
theorem le_of_dyadic_recursion {S : ℕ → ℝ} {x y A : ℝ} {N : ℕ}
    (hN : ∀ d, N ≤ d → S d = 0) (hA : 0 ≤ A) (hy : 0 ≤ y) (hy1 : 100 * y ≤ 1)
    (hrec : ∀ d, 1 ≤ d → x ^ (d - 1) * S d ≤ x ^ (2 * d - 1) * S (2 * d) + A * d * y ^ d) :
    S 1 ≤ A / 90 := by
  have hchain := le_dyadic_chain hrec N
  rw [hN (2 ^ N) (Nat.lt_two_pow_self).le, mul_zero, zero_add] at hchain
  have hsum := sum_dyadic_le hy hy1 N
  calc S 1 ≤ A * ∑ j ∈ range N, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j) := hchain
    _ ≤ A * (1 / 90) := mul_le_mul_of_nonneg_left hsum hA
    _ = A / 90 := by ring

end FunctionalInequalities.Analysis

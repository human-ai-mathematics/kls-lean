import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hölder bounds from Lipschitz bounds and Lipschitz cutoffs

Generic Hölder tools for the local-source form of Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), pp. 57–59, in a
pseudometric space:

* `le_rpow_one_sub_mul_rpow`: `t ≤ d^(1-α) t^α` for `0 ≤ t ≤ d` and `α ≤ 1`;
* `holderOnWith_of_dist_le_mul_of_diam`: a Lipschitz-type bound `L` on a set of diameter at most `d`
  gives `HolderOnWith` with cap `L d^(1-α)` (`α ≤ 1`);
* `abs_mul_sub_mul_le_of_cutoff`: if `|η| ≤ 1`, `η` is `L`-Lipschitz and vanishes off `K`, and `f` is
  `α`-Hölder with cap `H` and bounded by `M` on `K`, then `η f` is `α`-Hölder with cap
  `H + M L d^(1-α)` on every set of diameter at most `d`. No bound or Hölder cap of `f` outside `K` is used.
-/

noncomputable section

open scoped NNReal

namespace FunctionalInequalities.Analysis

/-- A pointwise distance bound gives `HolderOnWith` with the corresponding nonnegative cap. -/
theorem holderOnWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {g : X → Y} {s : Set X}
    {C : ℝ} {r : ℝ≥0} (hC : 0 ≤ C) (h : ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) ≤ C * dist x y ^ (r:ℝ)) :
    HolderOnWith (Real.toNNReal C) r g s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg, ← ENNReal.ofReal_coe_nnreal,
    Real.coe_toNNReal C hC, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

section Holder

variable {X : Type*} [PseudoMetricSpace X]

/-- `t ≤ d^{1−α} t^α` for `0 ≤ t ≤ d`, `α ≤ 1`. -/
theorem le_rpow_one_sub_mul_rpow {t d α : ℝ} (ht : 0 ≤ t) (htd : t ≤ d) (hα1 : α ≤ 1) :
    t ≤ d ^ (1 - α) * t ^ α := by
  rcases ht.eq_or_lt with h0 | h0
  · subst h0; have hd : 0 ≤ d := htd; positivity
  calc t = t ^ (1 - α) * t ^ α := by rw [← Real.rpow_add h0, sub_add_cancel, Real.rpow_one]
    _ ≤ d ^ (1 - α) * t ^ α :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht htd (by linarith)) (Real.rpow_nonneg ht α)

/-- A Lipschitz-type bound on a set of diameter `≤ d` gives an `α`-Hölder bound with cap `L d^{1−α}`. -/
theorem holderOnWith_of_dist_le_mul_of_diam {Y : Type*} [PseudoMetricSpace Y] {g : X → Y} {s : Set X} {L d : ℝ} {α : ℝ≥0}
    (hL : 0 ≤ L) (hd : 0 ≤ d) (hα1 : α ≤ 1) (hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ d)
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) ≤ L * dist x y) :
    HolderOnWith (Real.toNNReal (L * d ^ (1 - (α:ℝ)))) α g s := by
  refine holderOnWith_of_dist_le (by positivity) fun x hx y hy => (h x hx y hy).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (le_rpow_one_sub_mul_rpow dist_nonneg (hdiam x hx y hy) (by exact_mod_cast hα1)) hL

/-- Product with a Lipschitz cutoff: if `|η| ≤ 1`, `η` is `L`-Lipschitz and vanishes off `K`, and `f` is `α`-Hölder with cap `H` and
bounded by `M` on `K`, then `η f` satisfies `|η x f x − η y f y| ≤ (H + M L d^{1−α}) dist(x,y)^α` on any set of diameter `≤ d`. -/
theorem abs_mul_sub_mul_le_of_cutoff {η f : X → ℝ} {K D : Set X} {L H M d α : ℝ} (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hηL : ∀ x y, |η x - η y| ≤ L * dist x y) (hη1 : ∀ x, |η x| ≤ 1) (hη0 : ∀ x, x ∉ K → η x = 0)
    (hfH : ∀ x ∈ K, ∀ y ∈ K, |f x - f y| ≤ H * dist x y ^ α) (hfM : ∀ x ∈ K, |f x| ≤ M)
    (hdiam : ∀ x ∈ D, ∀ y ∈ D, dist x y ≤ d) :
    ∀ x ∈ D, ∀ y ∈ D, |η x * f x - η y * f y| ≤ (H + M * L * d ^ (1 - α)) * dist x y ^ α := by
  intro x hx y hy
  have hP : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg α
  have hlip : L * dist x y ≤ L * (d ^ (1 - α) * dist x y ^ α) :=
    mul_le_mul_of_nonneg_left (le_rpow_one_sub_mul_rpow dist_nonneg (hdiam x hx y hy) hα1) hL
  have hcut : ∀ u v, u ∈ K → v ∉ K → |η u * f u - η v * f v| ≤ M * (L * dist u v) := by
    intro u v hu hv
    rw [hη0 v hv, zero_mul, sub_zero, abs_mul, mul_comm]
    have : |η u| = |η u - η v| := by rw [hη0 v hv, sub_zero]
    rw [this]
    exact mul_le_mul (hfM u hu) (hηL u v) (abs_nonneg _) hM
  by_cases hxK : x ∈ K <;> by_cases hyK : y ∈ K
  · have e : η x * f x - η y * f y = η x * (f x - f y) + f y * (η x - η y) := by ring
    rw [e]
    calc _ ≤ |η x * (f x - f y)| + |f y * (η x - η y)| := abs_add_le _ _
      _ ≤ 1 * (H * dist x y ^ α) + M * (L * dist x y) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (hη1 x) (hfH x hxK y hyK) (abs_nonneg _) zero_le_one)
            (mul_le_mul (hfM y hyK) (hηL x y) (abs_nonneg _) hM)
      _ ≤ (H + M * L * d ^ (1 - α)) * dist x y ^ α := by nlinarith [mul_le_mul_of_nonneg_left hlip hM]
  · calc _ ≤ M * (L * dist x y) := hcut x y hxK hyK
      _ ≤ (H + M * L * d ^ (1 - α)) * dist x y ^ α := by nlinarith [mul_le_mul_of_nonneg_left hlip hM, mul_nonneg hH hP]
  · calc _ = |η y * f y - η x * f x| := abs_sub_comm _ _
      _ ≤ M * (L * dist y x) := hcut y x hyK hxK
      _ ≤ (H + M * L * d ^ (1 - α)) * dist x y ^ α := by
          rw [dist_comm]; nlinarith [mul_le_mul_of_nonneg_left hlip hM, mul_nonneg hH hP]
  · rw [hη0 x hxK, hη0 y hyK, zero_mul, zero_mul, sub_zero, abs_zero]; positivity

end Holder

end FunctionalInequalities.Analysis

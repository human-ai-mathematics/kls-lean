module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Continuity and normal slope of the CNS logarithmic barrier piece (CNS1984 Lemma 5.1, p. 386)

The barrier of CNS contains the singular piece `-q · log((p - β)² + q²)`. On its singular set
`{p = β, q = 0}` (codimension two in the ambient setting) the logarithm blows up, but the piece is
still
continuous: with `r = √((p - β)² + q²)` one has `|q| ≤ r` and `|q · log r²| ≤ 2 |r log r| → 0`.
Along the positive
normal ray the difference quotient `-(ε t) log(t²) / t = -2ε log t` tends to `+∞`, so the barrier is
not
differentiable there.

* `continuous_log_radial_barrier`: global continuity, for arbitrary real normed `G` and arbitrary
  continuous linear
  functionals `p`, `q` (no finite dimension, completeness, nontriviality or independence).
* `tendsto_log_radial_positive_normal_slope`: the positive normal-ray slope tends to `+∞` for `ε >
  0`.
-/

@[expose] public section

section
open Filter
open scoped Topology

namespace FunctionalInequalities.Analysis

theorem continuous_log_radial_barrier {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) (β : ℝ) :
    Continuous (fun y : G => -(q y) * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) := by
  have hS : Continuous (fun y : G => (p y - β) ^ 2 + (q y) ^ 2) :=
    ((p.continuous.sub continuous_const).pow 2).add (q.continuous.pow 2)
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : (p y - β) ^ 2 + (q y) ^ 2 = 0
  · -- the singular set: squeeze by `2 |r log r|`, `r = √S`

    have hq0 : q y = 0 := by nlinarith [sq_nonneg (p y - β), sq_nonneg (q y)]
    have hFy : -(q y) * Real.log ((p y - β) ^ 2 + (q y) ^ 2) = 0 := by rw [hq0]; ring
    set r : G → ℝ := fun z => Real.sqrt ((p z - β) ^ 2 + (q z) ^ 2) with hr
    have hrc : Continuous r := hS.sqrt
    have hry : r y = 0 := by simp [hr, hy]
    have hbound :
      ∀ z, ‖-(q z) * Real.log ((p z - β) ^ 2 + (q z) ^ 2)‖ ≤ 2 * |r z * Real.log (r z)| := by
      intro z
      have hS0 : 0 ≤ (p z - β) ^ 2 + (q z) ^ 2 := by positivity
      have hr0 : 0 ≤ r z := Real.sqrt_nonneg _
      have hsq : (p z - β) ^ 2 + (q z) ^ 2 = r z ^ 2 := (Real.sq_sqrt hS0).symm
      have hqr : |q z| ≤ r z := Real.abs_le_sqrt (by nlinarith [sq_nonneg (p z - β)])
      rw [Real.norm_eq_abs, hsq, Real.log_pow, abs_mul, abs_neg, abs_mul, abs_mul,
        abs_of_nonneg hr0]
      push_cast
      rw [abs_two]
      nlinarith [abs_nonneg (Real.log (r z))]
    have hlim : Tendsto (fun z => 2 * |r z * Real.log (r z)|) (𝓝 y) (𝓝 0) := by
      have h := ((Real.continuous_mul_log.comp hrc).abs.const_mul 2).tendsto y
      simpa [hry] using h
    have h0 := squeeze_zero_norm hbound hlim
    rw [← hFy] at h0
    exact h0
  · exact (q.continuous.neg.continuousAt).mul (hS.continuousAt.log hy)

theorem tendsto_log_radial_positive_normal_slope {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t : ℝ => (-(ε * t) * Real.log (t ^ 2)) / t) (𝓝[>] (0 : ℝ)) atTop := by
  have hlog : Tendsto (fun t : ℝ => -(2 * ε) * Real.log t) (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg (by linarith)
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  rw [Real.log_pow]
  field_simp
  push_cast
  ring

end FunctionalInequalities.Analysis

end

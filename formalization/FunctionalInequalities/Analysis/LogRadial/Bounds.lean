module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Scalar values of the logarithmic radial barrier

Caffarelli–Nirenberg–Spruck, CPAM37(1984), Lemma5.1 p386:
nonnegativity and value bounds for the actual radial/log profile. Constants here
are derived support bounds; no coefficient, PDE or regularity assumption occurs.
-/

@[expose] public section
namespace FunctionalInequalities.Analysis

/-- The nonnegative profile is bounded by its radius times a logarithmic factor. -/
theorem log_radial_profile_value_bounds {ε s y r : ℝ} (hε : 0 ≤ ε) (hy : 0 < y) (hr0 : 0 < r)
    (hr2 : r ^ 2 = s ^ 2 + y ^ 2) (hr1 : r < 1) :
    0 ≤ (r + s - ε * y * Real.log (r ^ 2)) / 2 ∧
      (r + s - ε * y * Real.log (r ^ 2)) / 2 ≤ r * (1 + ε / 2 * |Real.log (r ^ 2)|) := by
  have hsr : |s| ≤ r := by
    rw [← Real.sqrt_sq hr0.le, hr2]
    exact Real.abs_le_sqrt (by nlinarith)
  have hyr : y ≤ r := by nlinarith
  have hlog : Real.log (r ^ 2) < 0 := Real.log_neg (by positivity) (by nlinarith)
  have habs : |Real.log (r ^ 2)| = -Real.log (r ^ 2) := abs_of_neg hlog
  set L := -Real.log (r ^ 2) with hL
  have hL0 : 0 ≤ L := by linarith
  have hv : (r + s - ε * y * Real.log (r ^ 2)) / 2 = (r + s + ε * y * L) / 2 := by rw [hL]; ring
  rw [hv, habs]
  have hsle : s ≤ r := (le_abs_self s).trans hsr
  have hsge : -r ≤ s := (neg_abs_le s).trans' (neg_le_neg hsr)
  have hεy : 0 ≤ ε * y * L := mul_nonneg (mul_nonneg hε hy.le) hL0
  have hεyr : ε * y * L ≤ ε * r * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyr hε) hL0
  constructor <;> dsimp only [L] at * <;> nlinarith

/-- The logarithmic term gives the uniform radius-plus-epsilon value bound. -/
theorem log_radial_profile_value_le_radius_add {ε s y r : ℝ} (hε : 0 ≤ ε)
    (hy : 0 < y) (hr0 : 0 < r) (hr2 : r ^ 2 = s ^ 2 + y ^ 2) (hr1 : r < 1) :
    (r + s - ε * y * Real.log (r ^ 2)) / 2 ≤ r + ε := by
  have hv := (log_radial_profile_value_bounds hε hy hr0 hr2 hr1).2
  have hl : Real.log r < 0 := Real.log_neg hr0 hr1
  have hrl := Real.self_sub_one_le_mul_log hr0.le
  have hpow : |Real.log (r ^ 2)| = 2 * (-Real.log r) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [abs_of_nonpos (by nlinarith : (2 : ℝ) * Real.log r ≤ 0)]
    ring
  rw [hpow] at hv
  nlinarith [mul_nonneg hε (show 0 ≤ 1 + r * Real.log r by linarith)]

end FunctionalInequalities.Analysis

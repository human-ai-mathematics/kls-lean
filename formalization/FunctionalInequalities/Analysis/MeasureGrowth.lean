import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Ball growth of measures

Pure metric-measure geometry for measures with power ball growth `ν(B(x,r)) ≤ K r^d`:
* a measure supported in `closedBall x D` has total mass at most `K D^d` (no finiteness premise);
* local growth for centers within `2R` of `x0` and radii at most `R` gives growth of the measure restricted to `B(x0,R)`
  for EVERY center and EVERY positive radius, including balls meeting the boundary and large balls.
* small-ball growth for centers within `A + r0` of `x0` and radii at most `r0`, together with a separate bound on
  `ν(B(x0, A))`, gives the same all-ball growth of `ν.restrict (B(x0, A))`, with `A` and `r0` independent.
Consumers: the Riesz potentials of `RieszPotential/` and the Morrey bounds of `MorreyGrowth`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

section MeasurableSpace

variable {E : Type*}
  [PseudoMetricSpace E] [MeasurableSpace E]

/-- **Mass from support and growth.** If `ν` is a.e. supported in `closedBall x D`, `D > 0`, and
`ν(B(x,r)) ≤ K r^d` for every `r > 0`, then `ν(univ) ≤ K D^d`. -/
theorem measure_univ_le_of_ae_closedBall_ball_growth
    (ν : Measure E) (x : E) {K D d : ℝ} (hD : 0 < D)
    (hsupport : ∀ᵐ y ∂ν, y ∈ closedBall x D)
    (hgrowth : ∀ r : ℝ, 0 < r → ν (ball x r) ≤ ENNReal.ofReal (K * r ^ d)) :
    ν univ ≤ ENNReal.ofReal (K * D ^ d) := by
  have hr : ∀ r : ℝ, D < r → ν univ ≤ ENNReal.ofReal (K * r ^ d) := by
    intro r hdr
    have hball : ∀ᵐ y ∂ν, y ∈ univ → y ∈ ball x r := by
      filter_upwards [hsupport] with y hy
      intro _
      exact lt_of_le_of_lt hy hdr
    exact (measure_mono_ae hball).trans (hgrowth r (hD.trans hdr))
  have hc : ContinuousAt (fun r : ℝ => ENNReal.ofReal (K * r ^ d)) D := by
    exact ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul (Real.continuousAt_rpow_const D d (Or.inl hD.ne')))
  exact ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi D)))
    (eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun r hr' => hr r hr'))

section MeasurableSpace

variable [OpensMeasurableSpace E]

/-- **All-ball growth of a restriction.** Growth `ν(B(x,r)) ≤ K r^d` for centers with `dist x x0 < 2R` and `0 < r ≤ R`
(`R > 0`, `K, d ≥ 0`) gives `(ν.restrict (B(x0,R)))(B(x,r)) ≤ K r^d` for every center and every `r > 0`. -/
theorem restrict_ball_growth_of_local_ball_growth
    (ν : Measure E) (x0 : E) {R K d : ℝ} (hR : 0 < R) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hgrowth : ∀ x : E, dist x x0 < 2 * R → ∀ r : ℝ, 0 < r → r ≤ R →
      ν (ball x r) ≤ ENNReal.ofReal (K * r ^ d)) :
    ∀ x : E, ∀ r : ℝ, 0 < r →
      (ν.restrict (ball x0 R)) (ball x r) ≤ ENNReal.ofReal (K * r ^ d) := by
  intro x r hr
  rw [Measure.restrict_apply measurableSet_ball]
  by_cases hsmall : r ≤ R
  · by_cases hcenter : dist x x0 < 2 * R
    · exact (measure_mono inter_subset_left).trans (hgrowth x hcenter r hr hsmall)
    · have he : ball x r ∩ ball x0 R = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro y hy
        have ht := dist_triangle x y x0
        have hy1 : dist x y < r := by rw [dist_comm]; exact hy.1
        have hy2 : dist y x0 < R := hy.2
        exact hcenter (by linarith)
      rw [he, measure_empty]
      exact zero_le
  · have hmass := hgrowth x0 (by simpa using (by linarith : (0 : ℝ) < 2 * R)) R hR le_rfl
    refine (measure_mono inter_subset_right).trans (hmass.trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le (le_of_lt (lt_of_not_ge hsmall)) hd) hK

/-- **All-ball growth from small balls and a total mass.** Growth `ν(B(x,r)) ≤ K r^d` for centers with
`dist x x0 < A + r0` and `0 < r ≤ r0`, together with `ν(B(x0, A)) ≤ K r0^d` (`r0 > 0`, `K, d ≥ 0`; `A` and `r0`
independent), gives `(ν.restrict (B(x0, A)))(B(x,r)) ≤ K r^d` for every center and every `r > 0`. -/
theorem restrict_ball_growth_of_small_ball_growth_and_mass
    (ν : Measure E) (x0 : E) {A r0 K d : ℝ}
    (hr0 : 0 < r0) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hmass : ν (ball x0 A) ≤ ENNReal.ofReal (K * r0 ^ d))
    (hgrowth : ∀ x : E, dist x x0 < A + r0 → ∀ r : ℝ, 0 < r → r ≤ r0 →
      ν (ball x r) ≤ ENNReal.ofReal (K * r ^ d)) :
    ∀ x : E, ∀ r : ℝ, 0 < r →
      (ν.restrict (ball x0 A)) (ball x r) ≤ ENNReal.ofReal (K * r ^ d) := by
  intro x r hr
  rw [Measure.restrict_apply measurableSet_ball]
  by_cases hsmall : r ≤ r0
  · by_cases hcenter : dist x x0 < A + r0
    · exact (measure_mono inter_subset_left).trans (hgrowth x hcenter r hr hsmall)
    · have he : ball x r ∩ ball x0 A = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro y hy
        have ht := dist_triangle x y x0
        have hy1 : dist x y < r := by rw [dist_comm]; exact hy.1
        have hy2 : dist y x0 < A := hy.2
        exact hcenter (by linarith)
      rw [he, measure_empty]
      exact zero_le
  · refine (measure_mono inter_subset_right).trans (hmass.trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr0.le (le_of_lt (lt_of_not_ge hsmall)) hd) hK

end MeasurableSpace

end MeasurableSpace

end FunctionalInequalities.Analysis

/-! ## Lebesgue measure of Euclidean balls -/

noncomputable section EuclideanBalls

open MeasureTheory Set Metric

namespace FunctionalInequalities.Analysis

/-- For a positive radius, Lebesgue measure restricted to the closed ball equals its restriction to the open ball (the
sphere is null), in every dimension including `n = 0`. -/
theorem restrict_closedBall_eq_ball {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall x R) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x R) := by
  have hs := Measure.addHaar_sphere_of_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin n))) x hR.ne'
  have he := sdiff_null_ae_eq_self (s := closedBall x R) hs
  rw [Metric.closedBall_sdiff_sphere] at he
  exact Measure.restrict_congr_set he.symm

/-- The real Lebesgue mass of `B(x, a R)` is `|B(0,1)| · aⁿ · Rⁿ` for `a, R > 0`. -/
theorem restricted_ball_real_mass {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {a R : ℝ}
    (ha : 0 < a) (hR : 0 < R) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x (a*R))).real Set.univ =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * a^n) * R^(n:ℝ) := by
  simp only [measureReal_def,Measure.restrict_apply_univ]
  rw [Measure.addHaar_ball_of_pos _ x (mul_pos ha hR),finrank_euclideanSpace_fin,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg (mul_pos ha hR).le _),
    mul_pow,Real.rpow_natCast]
  ring

/-- Lebesgue measure restricted to a ball of positive radius is nonzero. -/
theorem restricted_ball_ne_zero {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x R) ≠ 0 := by
  rw [Ne,Measure.restrict_eq_zero]
  exact (Metric.measure_ball_pos _ x hR).ne'

end FunctionalInequalities.Analysis

end EuclideanBalls

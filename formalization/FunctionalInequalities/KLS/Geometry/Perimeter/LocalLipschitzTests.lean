import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBV
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Locally Lipschitz approximating sequences on proper spaces

The bounded-support tests of the metric BV perimeter may be replaced by genuinely locally
Lipschitz approximants on a proper metric space with a finite Borel measure: a sequence of
locally Lipschitz functions converging to `1_B` in global `L¹(ν)` is matched by the explicit
truncated tests `Test.truncateOfLocallyLipschitz x₀ n (f n)` with the same limit and no larger
liminf slope integral (`exists_approximatingSequence_of_locallyLipschitz`), so the perimeter is
at most that liminf (`perimeter_le_liminf_of_locallyLipschitz`).

The truncation `truncateFun x₀ R f = cutoff x₀ R · clampUnit ∘ f` is the one of the globally
Lipschitz bridge; its pointwise slope and error bounds hold for every real function. The only
new input is global Lipschitz continuity of the truncation: on a proper space the closed ball
`closedBall x₀ (R + 1)` carrying the truncation is compact, so `f` is Lipschitz on it
(`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`), and pairs crossing the ball are
controlled by `cutoff x₀ R x ≤ dist x y`. No uniform Lipschitz constant, boundedness or bounded
support of the approximants is assumed; the empty carrier, the zero measure, infinite slope
integrals and every `ENNReal` convention are included. This is the locally Lipschitz variant
(Ambrosio--Di Marino--Gigli, Remark 3.5) with global `L¹` convergence on proper spaces; `L¹_loc`
convergence and the identification of the relaxation infimum are not addressed here.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

section Pointwise

variable {X : Type*} [MetricSpace X]

/-- The truncation `χ_R · clamp f` of an arbitrary real function. -/
def truncateFun (x₀ : X) (R : ℝ) (f : X → ℝ) (x : X) : ℝ := cutoff x₀ R x * clampUnit (f x)

/-- The globally Lipschitz truncated test is the truncation of its function. -/
theorem Test.truncate_toFun (x₀ : X) (R : ℝ) {f : X → ℝ} (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    (Test.truncate x₀ R f hf : X → ℝ) = truncateFun x₀ R f := rfl

/-- Outside the closed ball of radius `R + 1` the truncation vanishes. -/
theorem truncateFun_eq_zero (x₀ : X) (R : ℝ) (f : X → ℝ) {x : X} (hx : R + 1 ≤ dist x x₀) :
    truncateFun x₀ R f x = 0 := by
  simp [truncateFun, cutoff_eq_zero hx]

theorem truncateFun_nonneg (x₀ : X) (R : ℝ) (f : X → ℝ) (x : X) : 0 ≤ truncateFun x₀ R f x :=
  mul_nonneg (cutoff_nonneg x₀ R x) (clampUnit_nonneg _)

theorem truncateFun_le_one (x₀ : X) (R : ℝ) (f : X → ℝ) (x : X) : truncateFun x₀ R f x ≤ 1 :=
  mul_le_one₀ (cutoff_le_one x₀ R x) (clampUnit_nonneg _) (clampUnit_le_one _)

/-- The cutoff at `x` is at most the distance from `x` to any point outside the ball of radius
`R + 1`. -/
theorem cutoff_le_dist_of_le {x₀ x y : X} {R : ℝ} (hy : R + 1 ≤ dist y x₀) :
    cutoff x₀ R x ≤ dist x y := by
  unfold cutoff clampUnit
  have h := dist_triangle y x x₀
  rw [dist_comm x y]
  refine max_le ((min_le_left _ _).trans ?_) dist_nonneg
  linarith

/-- The truncation's slope exceeds the original slope by at most the indicator of the
complement of the inner ball. -/
theorem apply_truncateFun_le (x₀ : X) (R : ℝ) (f : X → ℝ) (x : X) :
    Energy.LocalSlope.apply (truncateFun x₀ R f) x ≤
      Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x := by
  have hsec : Energy.LocalSlope.apply (truncateFun x₀ R f) x ≤
      Energy.LocalSlope.apply f x + Energy.LocalSlope.apply (cutoff x₀ R) x := by
    refine Energy.LocalSlope.apply_le_add zero_lt_one fun y _ => ?_
    change |cutoff x₀ R y * clampUnit (f y) - cutoff x₀ R x * clampUnit (f x)| ≤
      dist (f y) (f x) + dist (cutoff x₀ R y) (cutoff x₀ R x)
    rw [Real.dist_eq, Real.dist_eq]
    exact (abs_mul_sub_mul_le (cutoff_nonneg x₀ R y) (cutoff_le_one x₀ R y)
      (clampUnit_nonneg _) (clampUnit_le_one _)).trans (add_le_add (abs_clampUnit_sub_le _ _) le_rfl)
  refine hsec.trans (add_le_add le_rfl ?_)
  by_cases hx : x ∈ Metric.ball x₀ R
  · have hr : 0 < R - dist x x₀ := by rw [Metric.mem_ball] at hx; linarith
    rw [Energy.LocalSlope.apply_eq_zero_of_eqOn_ball hr fun y hy => ?_]
    · exact zero_le
    · have hy' : dist y x₀ ≤ R := by
        have := dist_triangle y x x₀
        linarith
      rw [cutoff_eq_one hy', cutoff_eq_one (le_of_lt (Metric.mem_ball.mp hx))]
  · rw [Set.indicator_of_mem (Set.mem_compl hx), Pi.one_apply]
    have hlip : LipschitzWith 1 (cutoff x₀ R) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        rw [Real.dist_eq, NNReal.coe_one, one_mul]; exact abs_cutoff_sub_le x₀ R a b
    simpa using Energy.LocalSlope.apply_le_of_lipschitzWith hlip x

/-- The truncation's pointwise distance to an indicator exceeds that of the original by at most
the indicator of the complement of the inner ball. -/
theorem enorm_truncateFun_sub_le (x₀ : X) (R : ℝ) (f : X → ℝ) (B : Set X) (x : X) :
    ‖truncateFun x₀ R f x - B.indicator (1 : X → ℝ) x‖ₑ ≤
      ‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x := by
  set i := B.indicator (1 : X → ℝ) x
  have hi01 : 0 ≤ i ∧ i ≤ 1 := by
    by_cases hx : x ∈ B <;> simp [i, hx]
  have hci : clampUnit i = i := clampUnit_of_mem hi01.1 hi01.2
  have hc0 : 0 ≤ clampUnit (f x) := clampUnit_nonneg _
  have hc1 : clampUnit (f x) ≤ 1 := clampUnit_le_one _
  have hu0 : 0 ≤ cutoff x₀ R x := cutoff_nonneg x₀ R x
  have hu1 : cutoff x₀ R x ≤ 1 := cutoff_le_one x₀ R x
  have hcf : |clampUnit (f x) - i| ≤ |f x - i| := by
    calc |clampUnit (f x) - i| = |clampUnit (f x) - clampUnit i| := by rw [hci]
      _ ≤ |f x - i| := abs_clampUnit_sub_le _ _
  have hreal : |cutoff x₀ R x * clampUnit (f x) - i| ≤ |f x - i| + (1 - cutoff x₀ R x) := by
    have key : cutoff x₀ R x * clampUnit (f x) - i =
        (clampUnit (f x) - i) - (1 - cutoff x₀ R x) * clampUnit (f x) := by ring
    rw [key]
    refine (abs_sub _ _).trans (add_le_add hcf ?_)
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - cutoff x₀ R x), abs_of_nonneg hc0]
    exact mul_le_of_le_one_right (by linarith) hc1
  change ‖cutoff x₀ R x * clampUnit (f x) - i‖ₑ ≤ _
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  refine ENNReal.ofReal_add_le.trans (add_le_add le_rfl ?_)
  by_cases hx : x ∈ Metric.ball x₀ R
  · rw [cutoff_eq_one (le_of_lt (Metric.mem_ball.mp hx)), sub_self, ENNReal.ofReal_zero]
    exact zero_le
  · rw [Set.indicator_of_mem (Set.mem_compl hx), Pi.one_apply]
    exact ENNReal.ofReal_le_one.mpr (by linarith)

/-- On a proper space the truncation of a locally Lipschitz function is globally Lipschitz: `f`
is Lipschitz on the compact closed ball carrying the truncation, the product secant bound holds
inside it, and a pair crossing it is controlled by `cutoff_le_dist_of_le`. -/
theorem lipschitzWith_truncateFun_of_locallyLipschitz [ProperSpace X] (x₀ : X) (R : ℝ)
    {f : X → ℝ} (hf : LocallyLipschitz f) :
    ∃ K : ℝ≥0, LipschitzWith K (truncateFun x₀ R f) := by
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall x₀ (R + 1)) hf.locallyLipschitzOn
  refine ⟨L + 1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hK : (0 : ℝ) ≤ L := L.2
  have hcast : ((L + 1 : ℝ≥0) : ℝ) = (L : ℝ) + 1 := by push_cast; ring
  rw [Real.dist_eq, hcast]
  by_cases hx : dist x x₀ ≤ R + 1 <;> by_cases hy : dist y x₀ ≤ R + 1
  · have hfd : |f x - f y| ≤ L * dist x y := by
      rw [← Real.dist_eq]
      exact hL.dist_le_mul x (Metric.mem_closedBall.2 hx) y (Metric.mem_closedBall.2 hy)
    calc |truncateFun x₀ R f x - truncateFun x₀ R f y|
        = |cutoff x₀ R x * clampUnit (f x) - cutoff x₀ R y * clampUnit (f y)| := rfl
      _ ≤ |clampUnit (f x) - clampUnit (f y)| + |cutoff x₀ R x - cutoff x₀ R y| :=
          abs_mul_sub_mul_le (cutoff_nonneg x₀ R x) (cutoff_le_one x₀ R x)
            (clampUnit_nonneg _) (clampUnit_le_one _)
      _ ≤ L * dist x y + dist x y :=
          add_le_add ((abs_clampUnit_sub_le _ _).trans hfd) (abs_cutoff_sub_le x₀ R x y)
      _ = ((L : ℝ) + 1) * dist x y := by ring
  · rw [truncateFun_eq_zero x₀ R f (not_le.1 hy).le, sub_zero,
      abs_of_nonneg (truncateFun_nonneg x₀ R f x)]
    calc truncateFun x₀ R f x ≤ cutoff x₀ R x :=
          mul_le_of_le_one_right (cutoff_nonneg x₀ R x) (clampUnit_le_one _)
      _ ≤ dist x y := cutoff_le_dist_of_le (not_le.1 hy).le
      _ ≤ ((L : ℝ) + 1) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y)]
  · rw [truncateFun_eq_zero x₀ R f (not_le.1 hx).le, zero_sub, abs_neg,
      abs_of_nonneg (truncateFun_nonneg x₀ R f y)]
    calc truncateFun x₀ R f y ≤ cutoff x₀ R y :=
          mul_le_of_le_one_right (cutoff_nonneg x₀ R y) (clampUnit_le_one _)
      _ ≤ dist y x := cutoff_le_dist_of_le (not_le.1 hx).le
      _ = dist x y := dist_comm y x
      _ ≤ ((L : ℝ) + 1) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y)]
  · rw [truncateFun_eq_zero x₀ R f (not_le.1 hx).le, truncateFun_eq_zero x₀ R f (not_le.1 hy).le,
      sub_zero, abs_zero]
    positivity

/-- The truncated test of a locally Lipschitz function on a proper space. -/
def Test.truncateOfLocallyLipschitz [ProperSpace X] (x₀ : X) (R : ℝ) (f : X → ℝ)
    (hf : LocallyLipschitz f) : Test X where
  toFun := truncateFun x₀ R f
  lipschitz := lipschitzWith_truncateFun_of_locallyLipschitz x₀ R hf
  bounded := by
    refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨truncateFun_nonneg x₀ R f x, truncateFun_le_one x₀ R f x⟩
  boundedSupport := by
    refine (Metric.isBounded_ball (x := x₀) (r := R + 1)).subset fun x hx => ?_
    by_contra hnot
    rw [Metric.mem_ball, not_lt] at hnot
    exact hx (truncateFun_eq_zero x₀ R f hnot)

theorem coe_truncateOfLocallyLipschitz [ProperSpace X] (x₀ : X) (R : ℝ) (f : X → ℝ)
    (hf : LocallyLipschitz f) :
    (Test.truncateOfLocallyLipschitz x₀ R f hf : X → ℝ) = truncateFun x₀ R f := rfl

end Pointwise

section Bridge

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The cost of the truncated test is at most the slope integral of the original plus the mass
outside the inner ball. -/
theorem cost_truncateOfLocallyLipschitz_le (ν : Measure X) (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : LocallyLipschitz f) :
    cost ν (Test.truncateOfLocallyLipschitz x₀ R f hf) ≤
      ∫⁻ x, Energy.LocalSlope.apply f x ∂ν + ν (Metric.ball x₀ R)ᶜ := by
  unfold cost
  rw [coe_truncateOfLocallyLipschitz]
  calc ∫⁻ x, Energy.LocalSlope.apply (truncateFun x₀ R f) x ∂ν
      ≤ ∫⁻ x, (Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x) ∂ν :=
        lintegral_mono fun x => apply_truncateFun_le x₀ R f x
    _ = _ := by
        rw [lintegral_add_right _ (measurable_one.indicator Metric.isOpen_ball.measurableSet.compl),
          lintegral_indicator_one Metric.isOpen_ball.measurableSet.compl]

/-- The `L¹` distance of the truncated test to an indicator. -/
theorem indicatorDistance_truncateOfLocallyLipschitz_le (ν : Measure X) (x₀ : X) (R : ℝ)
    {f : X → ℝ} (hf : LocallyLipschitz f) (B : Set X) :
    indicatorDistance ν (Test.truncateOfLocallyLipschitz x₀ R f hf) B ≤
      ∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν + ν (Metric.ball x₀ R)ᶜ := by
  unfold indicatorDistance
  rw [coe_truncateOfLocallyLipschitz]
  calc ∫⁻ x, ‖truncateFun x₀ R f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν
      ≤ ∫⁻ x, (‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x) ∂ν :=
        lintegral_mono fun x => enorm_truncateFun_sub_le x₀ R f B x
    _ = _ := by
        rw [lintegral_add_right _ (measurable_one.indicator Metric.isOpen_ball.measurableSet.compl),
          lintegral_indicator_one Metric.isOpen_ball.measurableSet.compl]

/-- The explicit truncated sequence converges to the indicator in `L¹(ν)`. -/
theorem tendsto_indicatorDistance_truncateOfLocallyLipschitz (ν : Measure X) [IsFiniteMeasure ν]
    (x₀ : X) {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => indicatorDistance ν (Test.truncateOfLocallyLipschitz x₀ n (f n) (hf n)) B)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hconv.add (tendsto_measure_compl_ball ν x₀)) (fun _ => zero_le) fun n => ?_
  exact indicatorDistance_truncateOfLocallyLipschitz_le ν x₀ n (hf n) B

/-- The explicit truncated sequence does not increase the liminf of the slope integrals. -/
theorem liminf_cost_truncateOfLocallyLipschitz_le (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X)
    {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n)) :
    liminf (fun n : ℕ => cost ν (Test.truncateOfLocallyLipschitz x₀ n (f n) (hf n))) atTop ≤
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  calc liminf (fun n : ℕ => cost ν (Test.truncateOfLocallyLipschitz x₀ n (f n) (hf n))) atTop
      ≤ liminf (fun n : ℕ => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν +
          ν (Metric.ball x₀ n)ᶜ) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n =>
          cost_truncateOfLocallyLipschitz_le ν x₀ n (hf n))
    _ = liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop :=
        ENNReal.liminf_add_of_right_tendsto_zero (tendsto_measure_compl_ball ν x₀) _

/-- Every locally Lipschitz sequence converging to `1_B` in `L¹(ν)` on a proper space with a
finite measure is matched by an approximating test sequence with no larger liminf cost. No
uniform Lipschitz constant, bounded values or bounded supports are assumed; the empty carrier is
included. -/
theorem exists_approximatingSequence_of_locallyLipschitz (ν : Measure X) [IsFiniteMeasure ν]
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine ⟨⟨fun _ => Test.zero, ?_⟩, ?_⟩
    · simp [indicatorDistance, Measure.eq_zero_of_isEmpty ν]
    · simp
  · exact ⟨⟨fun n => Test.truncateOfLocallyLipschitz x₀ n (f n) (hf n),
      tendsto_indicatorDistance_truncateOfLocallyLipschitz ν x₀ hf hconv⟩,
      liminf_cost_truncateOfLocallyLipschitz_le ν x₀ hf⟩

/-- The perimeter is bounded by the liminf slope integral of every locally Lipschitz sequence
converging to the indicator in `L¹(ν)`, on a proper space with a finite measure. -/
theorem perimeter_le_liminf_of_locallyLipschitz (ν : Measure X) [IsFiniteMeasure ν]
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  obtain ⟨g, hg⟩ := exists_approximatingSequence_of_locallyLipschitz ν hf hconv
  exact (perimeter_le_sequence ν B g).trans hg

end Bridge

section Clamp

/-! ### Clamping and bounded-ball `L¹` convergence

Clamping to `[0, 1]` contracts both the pointwise error to an indicator and the local slope, and
bounds the error by one. For a finite measure, convergence on the closed balls around one centre
therefore upgrades the clamped sequence to global `L¹` convergence, with a fixed radius chosen for
each tolerance; the un-clamped sequence is not claimed to converge globally. No properness is
used in this section. -/

variable {X : Type*} [MetricSpace X]

/-- The clamp is nonexpansive. -/
theorem lipschitzWith_clampUnit : LipschitzWith 1 clampUnit :=
  LipschitzWith.of_dist_le_mul fun s t => by
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_clampUnit_sub_le s t

/-- Clamping does not increase the local slope. -/
theorem apply_clampUnit_comp_le (f : X → ℝ) (x : X) :
    Energy.LocalSlope.apply (fun y => clampUnit (f y)) x ≤ Energy.LocalSlope.apply f x :=
  Energy.LocalSlope.apply_le_of_dist_le zero_lt_one fun y _ => by
    rw [Real.dist_eq, Real.dist_eq]
    exact abs_clampUnit_sub_le _ _

/-- The clamp of a locally Lipschitz function is locally Lipschitz. -/
theorem locallyLipschitz_clampUnit_comp {f : X → ℝ} (hf : LocallyLipschitz f) :
    LocallyLipschitz (fun y => clampUnit (f y)) :=
  lipschitzWith_clampUnit.locallyLipschitz.comp hf

omit [MetricSpace X] in
/-- Clamping contracts the pointwise error to an indicator. -/
theorem enorm_clampUnit_sub_indicator_le (f : X → ℝ) (B : Set X) (x : X) :
    ‖clampUnit (f x) - B.indicator (1 : X → ℝ) x‖ₑ ≤ ‖f x - B.indicator (1 : X → ℝ) x‖ₑ := by
  set i := B.indicator (1 : X → ℝ) x
  have hi01 : 0 ≤ i ∧ i ≤ 1 := by
    by_cases hx : x ∈ B <;> simp [i, hx]
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  calc |clampUnit (f x) - i| = |clampUnit (f x) - clampUnit i| := by
        rw [clampUnit_of_mem hi01.1 hi01.2]
    _ ≤ |f x - i| := abs_clampUnit_sub_le _ _

omit [MetricSpace X] in
/-- The clamped error to an indicator is at most one. -/
theorem enorm_clampUnit_sub_indicator_le_one (f : X → ℝ) (B : Set X) (x : X) :
    ‖clampUnit (f x) - B.indicator (1 : X → ℝ) x‖ₑ ≤ 1 := by
  set i := B.indicator (1 : X → ℝ) x
  have hi01 : 0 ≤ i ∧ i ≤ 1 := by
    by_cases hx : x ∈ B <;> simp [i, hx]
  have hc0 := clampUnit_nonneg (f x)
  have hc1 := clampUnit_le_one (f x)
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_one.2 (abs_le.2 ⟨by linarith, by linarith⟩)

variable [MeasurableSpace X]

/-- On a space where every compact set lies in a closed ball, convergence of set integrals on
every closed ball gives convergence on every compact set (the bounded-ball notion implies the
compact-set notion; on a proper space the two agree since closed balls are compact). -/
theorem tendsto_setLIntegral_of_isCompact (ν : Measure X) {g : ℕ → X → ℝ≥0∞}
    (hloc : ∀ (x₀ : X) (r : ℝ), 0 < r →
      Tendsto (fun n => ∫⁻ x in Metric.closedBall x₀ r, g n x ∂ν) atTop (𝓝 0))
    {K : Set X} (hK : IsCompact K) :
    Tendsto (fun n => ∫⁻ x in K, g n x ∂ν) atTop (𝓝 0) := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · simp [Measure.eq_zero_of_isEmpty ν]
  · obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x₀).1 hK.isBounded
    have hsub : K ⊆ Metric.closedBall x₀ (max R 1) :=
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hloc x₀ (max R 1) (lt_of_lt_of_le one_pos (le_max_right _ _))) (fun _ => zero_le)
      fun n => lintegral_mono_set hsub

variable [BorelSpace X]

/-- Finite-measure clamp lemma: if `f n` converges to `1_B` in `L¹(ν)` on every closed ball
around one centre, the clamped sequence converges globally. For each tolerance a fixed radius
captures all but half of it outside, and the ball integral is eventually below the other half. -/
theorem tendsto_lintegral_clampUnit_of_forall_closedBall (ν : Measure X) [IsFiniteMeasure ν]
    (x₀ : X) {B : Set X} {f : ℕ → X → ℝ}
    (hloc : ∀ r : ℝ, 0 < r → Tendsto (fun n =>
      ∫⁻ x in Metric.closedBall x₀ r, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖clampUnit (f n x) - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨N, hN⟩ :=
    ((ENNReal.tendsto_nhds_zero.1 (tendsto_measure_compl_ball ν x₀)) (ε / 2) hε2).exists
  set r : ℝ := (N : ℝ) + 1 with hr_def
  have hr : 0 < r := by positivity
  have hcompl : ν (Metric.closedBall x₀ r)ᶜ ≤ ε / 2 := by
    refine le_trans (measure_mono (Set.compl_subset_compl.2 ?_)) hN
    exact Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by rw [hr_def]; linarith))
  have hmeas : MeasurableSet (Metric.closedBall x₀ r) := Metric.isClosed_closedBall.measurableSet
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hloc r hr) (ε / 2) hε2] with n hn
  calc ∫⁻ x, ‖clampUnit (f n x) - B.indicator (1 : X → ℝ) x‖ₑ ∂ν
      = ∫⁻ x in Metric.closedBall x₀ r, ‖clampUnit (f n x) - B.indicator (1 : X → ℝ) x‖ₑ ∂ν +
          ∫⁻ x in (Metric.closedBall x₀ r)ᶜ, ‖clampUnit (f n x) - B.indicator (1 : X → ℝ) x‖ₑ ∂ν :=
        (lintegral_add_compl _ hmeas).symm
    _ ≤ ∫⁻ x in Metric.closedBall x₀ r, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν +
          ν (Metric.closedBall x₀ r)ᶜ := by
        refine add_le_add (lintegral_mono fun x => enorm_clampUnit_sub_indicator_le (f n) B x) ?_
        calc ∫⁻ x in (Metric.closedBall x₀ r)ᶜ, ‖clampUnit (f n x) - B.indicator (1 : X → ℝ) x‖ₑ ∂ν
            ≤ ∫⁻ _ in (Metric.closedBall x₀ r)ᶜ, (1 : ℝ≥0∞) ∂ν :=
              lintegral_mono fun x => enorm_clampUnit_sub_indicator_le_one (f n) B x
          _ = ν (Metric.closedBall x₀ r)ᶜ := setLIntegral_one _
    _ ≤ ε / 2 + ε / 2 := add_le_add hn hcompl
    _ = ε := ENNReal.add_halves ε

end Clamp

section BoundedBall

/-! ### Bounded-ball `L¹` convergence to actual tests -/

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Every locally Lipschitz sequence converging to `1_B` in `L¹(ν)` on every closed ball, on a
proper space with a finite measure, is matched by an actual approximating test sequence with no
larger liminf slope integral: the clamped sequence converges globally and the locally Lipschitz
bridge applies to it, with the slope contraction of the clamp. No global `L¹` convergence,
global Lipschitz constant or integrability of `f n` is assumed; the empty carrier is included. -/
theorem exists_approximatingSequence_of_locallyLipschitz_of_forall_closedBall (ν : Measure X)
    [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hloc : ∀ (x₀ : X) (r : ℝ), 0 < r → Tendsto (fun n =>
      ∫⁻ x in Metric.closedBall x₀ r, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine ⟨⟨fun _ => Test.zero, ?_⟩, ?_⟩
    · simp [indicatorDistance, Measure.eq_zero_of_isEmpty ν]
    · simp
  · obtain ⟨g, hg⟩ := exists_approximatingSequence_of_locallyLipschitz ν
      (f := fun n y => clampUnit (f n y)) (fun n => locallyLipschitz_clampUnit_comp (hf n))
      (tendsto_lintegral_clampUnit_of_forall_closedBall ν x₀ (hloc x₀))
    exact ⟨g, hg.trans (liminf_le_liminf (Eventually.of_forall fun n =>
      lintegral_mono fun x => apply_clampUnit_comp_le (f n) x))⟩

/-- The perimeter bound under bounded-ball `L¹` convergence of locally Lipschitz approximants. -/
theorem perimeter_le_liminf_of_locallyLipschitz_of_forall_closedBall (ν : Measure X)
    [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hloc : ∀ (x₀ : X) (r : ℝ), 0 < r → Tendsto (fun n =>
      ∫⁻ x in Metric.closedBall x₀ r, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  obtain ⟨g, hg⟩ := exists_approximatingSequence_of_locallyLipschitz_of_forall_closedBall ν hf hloc
  exact (perimeter_le_sequence ν B g).trans hg

/-- The same bound from convergence on every compact set: on a proper space closed balls are
compact. -/
theorem perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact (ν : Measure X)
    [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hloc : ∀ K : Set X, IsCompact K → Tendsto (fun n =>
      ∫⁻ x in K, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop :=
  perimeter_le_liminf_of_locallyLipschitz_of_forall_closedBall ν hf fun x₀ r _ =>
    hloc _ (isCompact_closedBall x₀ r)

end BoundedBall

end FunctionalInequalities.KLS.MetricBV

module

public import FunctionalInequalities.Analysis.MetricBV.Basic
public import FunctionalInequalities.Analysis.MetricBV.Complement
public import FunctionalInequalities.Analysis.MetricBV.Approximation
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

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
(Ambrosio--Di Marino--Gigli, Remark 3.5) with global `L¹` convergence on proper spaces. The
bounded-ball and compact-set convergence bounds below cover `L¹_loc` convergence, and the
identification of the relaxation infima is in `TestClassRelaxation.lean`.

For a measurable finite-mass target the finite-measure premise is removed: sharper target-tail
truncation estimates (`apply_truncateFun_le_target_tail`, `enorm_truncateFun_sub_le_target_tail`)
replace the mass outside a ball by the indicator error on a closed ball and the target outside
it, so for every Borel measure on a proper space locally Lipschitz approximants converging on
every compact set bound the perimeter
(`perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact_of_measure_lt_top`), by a diagonal
choice of radii; global `L¹` convergence is a special case.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

section Pointwise

variable {X : Type*} [MetricSpace X]

/-- Target-tail slope bound: the truncation's slope exceeds the original slope by at most the
original indicator error on the closed ball of radius `R + 1` and the target outside the inner
ball. The cutoff is locally constant off the annulus, and on the annulus the clamped value is
controlled by the indicator error and the target. No measure or regularity of `f` is involved. -/
theorem apply_truncateFun_le_target_tail (x₀ : X) (R : ℝ)
    (f : X → ℝ) (B : Set X) (x : X) :
    Energy.LocalSlope.apply (truncateFun x₀ R f) x ≤
      Energy.LocalSlope.apply f x +
        ((Metric.closedBall x₀ (R + 1)).indicator
            (fun y => ‖f y - B.indicator (1 : X → ℝ) y‖ₑ) x +
          (B \ Metric.ball x₀ R).indicator 1 x) := by
  set c := clampUnit (f x)
  have hc0 : 0 ≤ c := clampUnit_nonneg _
  have hsec : Energy.LocalSlope.apply (truncateFun x₀ R f) x ≤
      Energy.LocalSlope.apply f x +
        Energy.LocalSlope.apply (fun y => c * cutoff x₀ R y) x := by
    refine Energy.LocalSlope.apply_le_add zero_lt_one fun y _ => ?_
    change |cutoff x₀ R y * clampUnit (f y) - cutoff x₀ R x * clampUnit (f x)| ≤
      dist (f y) (f x) + dist (c * cutoff x₀ R y) (c * cutoff x₀ R x)
    have key : cutoff x₀ R y * clampUnit (f y) - cutoff x₀ R x * clampUnit (f x) =
        cutoff x₀ R y * (clampUnit (f y) - clampUnit (f x)) +
          (c * cutoff x₀ R y - c * cutoff x₀ R x) := by
      dsimp [c]
      ring
    rw [key]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (cutoff_nonneg x₀ R y)]
      exact (mul_le_of_le_one_left (abs_nonneg _)
        (cutoff_le_one x₀ R y)).trans
        (by simpa only [Real.dist_eq] using abs_clampUnit_sub_le (f y) (f x))
    · rw [Real.dist_eq]
  refine hsec.trans (add_le_add le_rfl ?_)
  by_cases hx : x ∈ Metric.ball x₀ R
  · have hr : 0 < R - dist x x₀ := by
      rw [Metric.mem_ball] at hx
      linarith
    rw [Energy.LocalSlope.apply_eq_zero_of_eqOn_ball hr fun y hy => ?_]
    · exact zero_le
    · have hy' : dist y x₀ ≤ R := by
        have htri := dist_triangle y x x₀
        linarith
      rw [cutoff_eq_one hy', cutoff_eq_one (le_of_lt (Metric.mem_ball.mp hx))]
  · by_cases hxc : x ∈ Metric.closedBall x₀ (R + 1)
    · have hlip : LipschitzWith (⟨c, hc0⟩ : ℝ≥0)
          (fun y => c * cutoff x₀ R y) :=
        LipschitzWith.of_dist_le_mul fun a b => by
          rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hc0]
          exact mul_le_mul_of_nonneg_left (abs_cutoff_sub_le x₀ R a b) hc0
      have hq : Energy.LocalSlope.apply (fun y => c * cutoff x₀ R y) x ≤
          ENNReal.ofReal c := by
        exact (Energy.LocalSlope.apply_le_of_lipschitzWith hlip x).trans_eq
          (ENNReal.coe_nnreal_eq (⟨c, hc0⟩ : ℝ≥0))
      have hclamp : ENNReal.ofReal c ≤
          ‖f x - B.indicator (1 : X → ℝ) x‖ₑ +
            B.indicator (1 : X → ENNReal) x := by
        by_cases hb : x ∈ B
        · simp only [Set.indicator_of_mem hb, Pi.one_apply]
          exact (ENNReal.ofReal_le_one.2 (clampUnit_le_one _)).trans
            (le_add_left le_rfl)
        · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb,
            sub_zero, add_zero, Real.enorm_eq_ofReal_abs]
          apply ENNReal.ofReal_le_ofReal
          simpa only [clampUnit_of_mem (by norm_num : (0 : ℝ) ≤ 0)
            (by norm_num : (0 : ℝ) ≤ 1), sub_zero,
            abs_of_nonneg (clampUnit_nonneg _)] using
            abs_clampUnit_sub_le (f x) 0
      rw [Set.indicator_of_mem hxc]
      by_cases hb : x ∈ B
      · calc
          Energy.LocalSlope.apply (fun y => c * cutoff x₀ R y) x ≤
              ENNReal.ofReal c := hq
          _ ≤ ‖f x - B.indicator (1 : X → ℝ) x‖ₑ +
              B.indicator (1 : X → ENNReal) x := hclamp
          _ = ‖f x - B.indicator (1 : X → ℝ) x‖ₑ +
              (B \ Metric.ball x₀ R).indicator 1 x := by
            simp only [Set.indicator_of_mem hb, Pi.one_apply]
            rw [Set.indicator_of_mem
              (show x ∈ B \ Metric.ball x₀ R from ⟨hb, hx⟩), Pi.one_apply]
      · calc
          Energy.LocalSlope.apply (fun y => c * cutoff x₀ R y) x ≤
              ENNReal.ofReal c := hq
          _ ≤ ‖f x - B.indicator (1 : X → ℝ) x‖ₑ +
              B.indicator (1 : X → ENNReal) x := hclamp
          _ = ‖f x - B.indicator (1 : X → ℝ) x‖ₑ +
              (B \ Metric.ball x₀ R).indicator 1 x := by
            simp only [Set.indicator_of_notMem hb,
              Set.indicator_of_notMem (show x ∉ B \ Metric.ball x₀ R from
                fun h => hb h.1), add_zero]
    · have hdist : R + 1 < dist x x₀ := by
        rw [Metric.mem_closedBall] at hxc
        exact not_le.mp hxc
      have hr : 0 < dist x x₀ - (R + 1) := by
        linarith
      rw [Energy.LocalSlope.apply_eq_zero_of_eqOn_ball hr fun y hy => ?_]
      · exact zero_le
      · have hy' : R + 1 ≤ dist y x₀ := by
          have htri := dist_triangle x y x₀
          have hxy : dist x y = dist y x := dist_comm _ _
          linarith
        rw [cutoff_eq_zero hy', cutoff_eq_zero (le_of_lt hdist)]

/-- Target-tail error bound: the truncation's pointwise distance to an indicator is at most the
original error on the closed ball of radius `R + 1` plus the target outside the inner ball. -/
theorem enorm_truncateFun_sub_le_target_tail (x₀ : X) (R : ℝ)
    (f : X → ℝ) (B : Set X) (x : X) :
    ‖truncateFun x₀ R f x - B.indicator (1 : X → ℝ) x‖ₑ ≤
      (Metric.closedBall x₀ (R + 1)).indicator
          (fun y => ‖f y - B.indicator (1 : X → ℝ) y‖ₑ) x +
        (B \ Metric.ball x₀ R).indicator 1 x := by
  by_cases hx : dist x x₀ ≤ R + 1
  · rw [Set.indicator_of_mem (Metric.mem_closedBall.2 hx)]
    change
      ‖cutoff x₀ R x * clampUnit (f x) - B.indicator (1 : X → ℝ) x‖ₑ ≤
        ‖f x - B.indicator (1 : X → ℝ) x‖ₑ +
          (B \ Metric.ball x₀ R).indicator 1 x
    have hu0 := cutoff_nonneg x₀ R x
    have hu1 := cutoff_le_one x₀ R x
    have hc0 := clampUnit_nonneg (f x)
    have hc1 := clampUnit_le_one (f x)
    by_cases hb : x ∈ B
    · simp only [Set.indicator_of_mem hb, Pi.one_apply]
      by_cases hball : x ∈ Metric.ball x₀ R
      · rw [cutoff_eq_one (le_of_lt (Metric.mem_ball.mp hball)), one_mul,
          Set.indicator_of_notMem
            (show x ∉ B \ Metric.ball x₀ R from fun h => h.2 hball), add_zero,
          Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
        apply ENNReal.ofReal_le_ofReal
        simpa only [clampUnit_of_mem zero_le_one le_rfl] using
          abs_clampUnit_sub_le (f x) 1
      · rw [Set.indicator_of_mem
            (show x ∈ B \ Metric.ball x₀ R from ⟨hb, hball⟩), Pi.one_apply]
        refine (show ‖cutoff x₀ R x * clampUnit (f x) - 1‖ₑ ≤ 1 from ?_).trans
          (le_add_left le_rfl)
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2 (abs_le.2 ⟨by nlinarith, by nlinarith⟩)
    · simp only [Set.indicator_of_notMem hb, sub_zero,
        Set.indicator_of_notMem
          (show x ∉ B \ Metric.ball x₀ R from fun h => hb h.1), add_zero,
        Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (mul_nonneg hu0 hc0)]
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_of_le_one_left hc0 hu1).trans (by
        simpa only [clampUnit_of_mem (by norm_num : (0 : ℝ) ≤ 0)
          (by norm_num : (0 : ℝ) ≤ 1), sub_zero, abs_of_nonneg hc0] using
          abs_clampUnit_sub_le (f x) 0)
  · have hdist : R + 1 ≤ dist x x₀ := le_of_not_ge hx
    have hball : x ∉ Metric.ball x₀ R := by
      intro h
      have h' := Metric.mem_ball.mp h
      linarith
    have hclosed : x ∉ Metric.closedBall x₀ (R + 1) := by
      exact fun h => hx (Metric.mem_closedBall.mp h)
    rw [truncateFun_eq_zero x₀ R f hdist,
      Set.indicator_of_notMem hclosed]
    by_cases hb : x ∈ B
    · have htail : x ∈ B \ Metric.ball x₀ R := ⟨hb, hball⟩
      rw [Set.indicator_of_mem hb, Pi.one_apply,
        Set.indicator_of_mem htail, Pi.one_apply]
      norm_num
    · have htail : x ∉ B \ Metric.ball x₀ R := fun h => hb h.1
      rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem htail]
      norm_num

/-- On a proper space the truncation of a locally Lipschitz function is globally Lipschitz: `f`
is Lipschitz on the compact closed ball carrying the truncation, the product secant bound holds
inside it, and a pair crossing it is controlled by `cutoff_le_dist_of_le`. -/
theorem lipschitzWith_truncateFun_of_locallyLipschitz [ProperSpace X] (x₀ : X) (R : ℝ)
    {f : X → ℝ} (hf : LocallyLipschitz f) : ∃ K : ℝ≥0, LipschitzWith K (truncateFun x₀ R f) := by
  obtain ⟨L, hL⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_closedBall x₀ (R + 1))
      hf.locallyLipschitzOn
  refine ⟨L + 1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hK : (0 : ℝ) ≤ L := L.2
  have hcast : ((L + 1 : ℝ≥0) : ℝ) = (L : ℝ) + 1 := by push_cast; ring
  rw [Real.dist_eq, hcast]
  by_cases hx : dist x x₀ ≤ R + 1 <;> by_cases hy : dist y x₀ ≤ R + 1
  · have hfd : |f x - f y| ≤ L * dist x y := by
      rw [← Real.dist_eq]
      exact hL.dist_le_mul x (Metric.mem_closedBall.2 hx) y (Metric.mem_closedBall.2 hy)
    calc
      |truncateFun x₀ R f x - truncateFun x₀ R f y| =
          |cutoff x₀ R x * clampUnit (f x) - cutoff x₀ R y * clampUnit (f y)| :=
        rfl
      _ ≤ |clampUnit (f x) - clampUnit (f y)| + |cutoff x₀ R x - cutoff x₀ R y| :=
        abs_mul_sub_mul_le (cutoff_nonneg x₀ R x) (cutoff_le_one x₀ R x) (clampUnit_nonneg _)
          (clampUnit_le_one _)
      _ ≤ L * dist x y + dist x y :=
        add_le_add ((abs_clampUnit_sub_le _ _).trans hfd) (abs_cutoff_sub_le x₀ R x y)
      _ = ((L : ℝ) + 1) * dist x y := by ring
  · rw [truncateFun_eq_zero x₀ R f (not_le.1 hy).le, sub_zero,
      abs_of_nonneg (truncateFun_nonneg x₀ R f x)]
    calc
      truncateFun x₀ R f x ≤ cutoff x₀ R x :=
        mul_le_of_le_one_right (cutoff_nonneg x₀ R x) (clampUnit_le_one _)
      _ ≤ dist x y := cutoff_le_dist_of_le (not_le.1 hy).le
      _ ≤ ((L : ℝ) + 1) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y)]
  · rw [truncateFun_eq_zero x₀ R f (not_le.1 hx).le, zero_sub, abs_neg,
      abs_of_nonneg (truncateFun_nonneg x₀ R f y)]
    calc
      truncateFun x₀ R f y ≤ cutoff x₀ R y :=
        mul_le_of_le_one_right (cutoff_nonneg x₀ R y) (clampUnit_le_one _)
      _ ≤ dist y x := cutoff_le_dist_of_le (not_le.1 hx).le
      _ = dist x y := dist_comm y x
      _ ≤ ((L : ℝ) + 1) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y)]
  · rw [truncateFun_eq_zero x₀ R f (not_le.1 hx).le,
      truncateFun_eq_zero x₀ R f (not_le.1 hy).le, sub_zero, abs_zero]
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

/-- The cost of the truncated test is at most the slope integral of the original plus the
indicator error on the closed ball of radius `R + 1` and the target mass outside the inner
ball, for every Borel measure (no finiteness of the measure). -/
theorem cost_truncateOfLocallyLipschitz_le_target_tail (ν : Measure X) (x₀ : X) (R : ℝ)
    {f : X → ℝ} (hf : LocallyLipschitz f) {B : Set X} (hB : MeasurableSet B) :
    cost ν (Test.truncateOfLocallyLipschitz x₀ R f hf) ≤
      (∫⁻ x, Energy.LocalSlope.apply f x ∂ν) +
        ((∫⁻ x in Metric.closedBall x₀ (R + 1), ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) +
          ν (B \ Metric.ball x₀ R)) := by
  unfold cost
  rw [coe_truncateOfLocallyLipschitz]
  have he : Measurable (fun x => ‖f x - B.indicator (1 : X → ℝ) x‖ₑ) :=
    (hf.continuous.measurable.sub (measurable_one.indicator hB)).enorm
  have ht : MeasurableSet (B \ Metric.ball x₀ R) :=
    hB.diff Metric.isOpen_ball.measurableSet
  have hc :
      Measurable
        ((Metric.closedBall x₀ (R + 1)).indicator
          (fun y => ‖f y - B.indicator (1 : X → ℝ) y‖ₑ)) :=
    he.indicator Metric.isClosed_closedBall.measurableSet
  calc
    ∫⁻ x, Energy.LocalSlope.apply (truncateFun x₀ R f) x ∂ν
        ≤ ∫⁻ x,
            Energy.LocalSlope.apply f x +
              ((Metric.closedBall x₀ (R + 1)).indicator
                  (fun y => ‖f y - B.indicator (1 : X → ℝ) y‖ₑ) x +
                (B \ Metric.ball x₀ R).indicator 1 x) ∂ν :=
      lintegral_mono fun x =>
        apply_truncateFun_le_target_tail x₀ R f B x
    _ =
        (∫⁻ x, Energy.LocalSlope.apply f x ∂ν) +
          ∫⁻ x,
            ((Metric.closedBall x₀ (R + 1)).indicator
                (fun y => ‖f y - B.indicator (1 : X → ℝ) y‖ₑ) x +
              (B \ Metric.ball x₀ R).indicator 1 x) ∂ν :=
      lintegral_add_right _
        (hc.add (measurable_one.indicator ht))
    _ =
        (∫⁻ x, Energy.LocalSlope.apply f x ∂ν) +
          ((∫⁻ x in Metric.closedBall x₀ (R + 1),
              ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) +
            ν (B \ Metric.ball x₀ R)) := by
      rw [lintegral_add_right _ (measurable_one.indicator ht),
        lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        lintegral_indicator_one ht]

/-- The `L¹` distance of the truncated test to a measurable target is at most the indicator
error on the closed ball of radius `R + 1` plus the target mass outside the inner ball, for every
Borel measure. -/
theorem indicatorDistance_truncateOfLocallyLipschitz_le_target_tail (ν : Measure X) (x₀ : X) (R : ℝ)
    {f : X → ℝ} (hf : LocallyLipschitz f) {B : Set X} (hB : MeasurableSet B) :
    indicatorDistance ν (Test.truncateOfLocallyLipschitz x₀ R f hf) B ≤
      (∫⁻ x in Metric.closedBall x₀ (R + 1), ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) +
        ν (B \ Metric.ball x₀ R) := by
  have he : Measurable (fun x => ‖f x - B.indicator (1 : X → ℝ) x‖ₑ) :=
    (hf.continuous.measurable.sub (measurable_one.indicator hB)).enorm
  have ht : MeasurableSet (B \ Metric.ball x₀ R) :=
    hB.diff Metric.isOpen_ball.measurableSet
  unfold indicatorDistance
  rw [coe_truncateOfLocallyLipschitz]
  calc
    ∫⁻ x, ‖truncateFun x₀ R f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν
        ≤ ∫⁻ x, ((Metric.closedBall x₀ (R + 1)).indicator
            (fun y => ‖f y - B.indicator (1 : X → ℝ) y‖ₑ) x +
          (B \ Metric.ball x₀ R).indicator 1 x) ∂ν :=
      lintegral_mono fun x => enorm_truncateFun_sub_le_target_tail x₀ R f B x
    _ = (∫⁻ x in Metric.closedBall x₀ (R + 1),
          ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) +
        ν (B \ Metric.ball x₀ R) := by
      rw [lintegral_add_right _ (measurable_one.indicator ht),
        lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        lintegral_indicator_one ht]

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

section ClampErrors

omit [MetricSpace X]
/-- Clamping contracts the pointwise error to an indicator. -/
theorem enorm_clampUnit_sub_indicator_le (f : X → ℝ) (B : Set X) (x : X) :
    ‖clampUnit (f x) - B.indicator (1 : X → ℝ) x‖ₑ ≤ ‖f x - B.indicator (1 : X → ℝ) x‖ₑ := by
  set i := B.indicator (1 : X → ℝ) x
  have hi01 : 0 ≤ i ∧ i ≤ 1 := by by_cases hx : x ∈ B <;> simp [i, hx]
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  calc
    |clampUnit (f x) - i| = |clampUnit (f x) - clampUnit i| := by
      rw [clampUnit_of_mem hi01.1 hi01.2]
    _ ≤ |f x - i| := abs_clampUnit_sub_le _ _

/-- The clamped error to an indicator is at most one. -/
theorem enorm_clampUnit_sub_indicator_le_one (f : X → ℝ) (B : Set X) (x : X) :
    ‖clampUnit (f x) - B.indicator (1 : X → ℝ) x‖ₑ ≤ 1 := by
  set i := B.indicator (1 : X → ℝ) x
  have hi01 : 0 ≤ i ∧ i ≤ 1 := by by_cases hx : x ∈ B <;> simp [i, hx]
  have hc0 := clampUnit_nonneg (f x)
  have hc1 := clampUnit_le_one (f x)
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_one.2 (abs_le.2 ⟨by linarith, by linarith⟩)

end ClampErrors

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

section TargetTail

/-! ### Measurable finite-mass targets under arbitrary Borel measures

ADMG Remark 3.5 on proper spaces without finite total mass: locally Lipschitz approximants
converging to a measurable finite-mass target in `L¹(ν)` on every compact set (or globally) bound
the bounded-support perimeter. A diagonal choice pairs the radius `k` with an index where the
error on the closed ball of radius `k + 1` is below `1/(k+1)`; the remaining error is the target
mass outside the ball of radius `k`. No finiteness of `ν` on bounded or compact sets is used. -/

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Compact-local `L¹` convergence of locally Lipschitz approximants to a measurable finite-mass
target bounds the perimeter by their liminf slope integral, for every Borel measure on a proper
space. The empty carrier is included; no global `L¹` convergence, integrability or bounded
support of the approximants is assumed. -/
theorem perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact_of_measure_lt_top
    (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) {f : ℕ → X → ℝ}
    (hf : ∀ n, LocallyLipschitz (f n))
    (hloc : ∀ K : Set X, IsCompact K → Tendsto (fun n =>
      ∫⁻ x in K, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · have hB' : B = ∅ := Set.eq_empty_of_isEmpty B
    rw [hB', perimeter_empty]
    exact zero_le
  · refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
    have hfreq : ∃ᶠ n in atTop,
        ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν < a :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) ha
    have hε0 : ∀ k : ℕ, 0 < (((k + 1 : ℕ) : ENNReal))⁻¹ := fun k =>
      ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
    have hεlim : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ENNReal))⁻¹)
        atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hidx : ∀ k : ℕ, ∃ n,
        (∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) < a ∧
          (∫⁻ x in Metric.closedBall x₀ ((k : ℝ) + 1),
            ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) <
            (((k + 1 : ℕ) : ENNReal))⁻¹ := fun k =>
      (hfreq.and_eventually
        ((hloc (Metric.closedBall x₀ ((k : ℝ) + 1))
          (isCompact_closedBall x₀ ((k : ℝ) + 1))).eventually
            (gt_mem_nhds (hε0 k)))).exists
    choose m hm using hidx
    let g : ℕ → Test X := fun k =>
      Test.truncateOfLocallyLipschitz x₀ (k : ℝ) (f (m k)) (hf (m k))
    have htail : Tendsto (fun k : ℕ => ν (B \ Metric.ball x₀ (k : ℝ)))
        atTop (𝓝 0) :=
      tendsto_measure_diff_ball ν x₀ hB hνB.ne
    have hδ : Tendsto
        (fun k : ℕ => (((k + 1 : ℕ) : ENNReal))⁻¹ +
          ν (B \ Metric.ball x₀ (k : ℝ))) atTop (𝓝 0) := by
      simpa using hεlim.add htail
    have hd : ∀ k : ℕ, indicatorDistance ν (g k) B ≤
        (((k + 1 : ℕ) : ENNReal))⁻¹ + ν (B \ Metric.ball x₀ (k : ℝ)) := by
      intro k
      exact
        (indicatorDistance_truncateOfLocallyLipschitz_le_target_tail
          ν x₀ (k : ℝ) (hf (m k)) hB).trans
          (add_le_add (hm k).2.le le_rfl)
    let s : ApproximatingSequence ν B :=
      ⟨g, tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hδ (fun _ => zero_le) hd⟩
    have hcost : ∀ k : ℕ, cost ν (g k) ≤
        a + ((((k + 1 : ℕ) : ENNReal))⁻¹ +
          ν (B \ Metric.ball x₀ (k : ℝ))) := by
      intro k
      exact
        (cost_truncateOfLocallyLipschitz_le_target_tail
          ν x₀ (k : ℝ) (hf (m k)) hB).trans
          (add_le_add (hm k).1.le (add_le_add (hm k).2.le le_rfl))
    calc
      perimeter ν B ≤ liminf (fun k => cost ν (s.1 k)) atTop :=
        perimeter_le_sequence ν B s
      _ ≤ liminf
          (fun k => a + ((((k + 1 : ℕ) : ENNReal))⁻¹ +
            ν (B \ Metric.ball x₀ (k : ℝ)))) atTop :=
        liminf_le_liminf (Eventually.of_forall hcost)
      _ = liminf (fun _ : ℕ => a) atTop :=
        ENNReal.liminf_add_of_right_tendsto_zero hδ _
      _ = a := liminf_const a

/-- Global `L¹` convergence of locally Lipschitz approximants to a measurable finite-mass target
bounds the perimeter by their liminf slope integral, for every Borel measure on a proper space. -/
theorem perimeter_le_liminf_of_locallyLipschitz_of_measure_lt_top (ν : Measure X) {B : Set X}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop :=
  perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact_of_measure_lt_top ν hB hνB hf
    fun K _ => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => zero_le) fun _ => setLIntegral_le_lintegral K _

end TargetTail

end FunctionalInequalities.KLS.MetricBV

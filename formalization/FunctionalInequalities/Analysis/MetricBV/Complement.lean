import FunctionalInequalities.Analysis.MetricBV.Basic

/-!
# Metric BV complement symmetry for finite measures
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable [BorelSpace X]
section Complement

/-! ### Complement symmetry for finite measures

The reflection `1 - f` of a bounded-support test does not have bounded support. It is
cut off by a radial function after clamping to `[0, 1]`; the errors are the masses of the
complements of large balls, which vanish for a finite measure. -/

/-- Clamping of real values to `[0, 1]`. -/
def clampUnit (t : ℝ) : ℝ := max (min t 1) 0

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem clampUnit_nonneg (t : ℝ) : 0 ≤ clampUnit t := le_max_right _ _

theorem clampUnit_le_one (t : ℝ) : clampUnit t ≤ 1 :=
  max_le (min_le_right _ _) zero_le_one

theorem clampUnit_zero : clampUnit 0 = 0 := by simp [clampUnit]

theorem clampUnit_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clampUnit t = t := by
  simp [clampUnit, min_eq_left h1, max_eq_left h0]

theorem abs_clampUnit_sub_le (s t : ℝ) : |clampUnit s - clampUnit t| ≤ |s - t| := by
  unfold clampUnit
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

/-- The radial cutoff equal to `1` on `closedBall x₀ R` and `0` outside `ball x₀ (R + 1)`. -/
def cutoff (x₀ : X) (R : ℝ) (x : X) : ℝ := clampUnit (R + 1 - dist x x₀)

omit [MeasurableSpace X] [BorelSpace X] in
theorem abs_cutoff_sub_le (x₀ : X) (R : ℝ) (x y : X) :
    |cutoff x₀ R x - cutoff x₀ R y| ≤ dist x y := by
  refine (abs_clampUnit_sub_le _ _).trans ?_
  rw [show R + 1 - dist x x₀ - (R + 1 - dist y x₀) = dist y x₀ - dist x x₀ by ring, abs_sub_comm]
  exact abs_dist_sub_le x y x₀

omit [MeasurableSpace X] [BorelSpace X] in
theorem cutoff_eq_one {x₀ x : X} {R : ℝ} (h : dist x x₀ ≤ R) : cutoff x₀ R x = 1 := by
  unfold cutoff clampUnit
  rw [min_eq_right (by linarith), max_eq_left zero_le_one]

omit [MeasurableSpace X] [BorelSpace X] in
theorem cutoff_eq_zero {x₀ x : X} {R : ℝ} (h : R + 1 ≤ dist x x₀) : cutoff x₀ R x = 0 := by
  unfold cutoff clampUnit
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The secant estimate behind the reflected test. -/
theorem abs_mul_one_sub_sub_le {u v c c' : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hc0 : 0 ≤ c')
    (hc1 : c' ≤ 1) :
    |u * (1 - c) - v * (1 - c')| ≤ |c - c'| + |u - v| := by
  have key : u * (1 - c) - v * (1 - c') = u * (c' - c) + (u - v) * (1 - c') := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg (sub_nonneg.2 hc1), abs_sub_comm c' c]
  have h1 : u * |c - c'| ≤ |c - c'| := mul_le_of_le_one_left (abs_nonneg _) hu1
  have h2 : |u - v| * (1 - c') ≤ |u - v| :=
    mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  linarith

omit [MeasurableSpace X] [BorelSpace X] in
theorem cutoff_nonneg (x₀ : X) (R : ℝ) (x : X) : 0 ≤ cutoff x₀ R x := clampUnit_nonneg _

omit [MeasurableSpace X] [BorelSpace X] in
theorem cutoff_le_one (x₀ : X) (R : ℝ) (x : X) : cutoff x₀ R x ≤ 1 := clampUnit_le_one _

/-- The reflected test `χ_R · (1 - clamp f)`: a bounded-support approximation of `1 - f`. -/
def Test.reflect (x₀ : X) (R : ℝ) (f : Test X) : Test X where
  toFun := fun x => cutoff x₀ R x * (1 - clampUnit (f x))
  lipschitz := by
    obtain ⟨K, hK⟩ := f.lipschitz
    refine ⟨K + 1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Real.dist_eq]
    have hfd : |f x - f y| ≤ K * dist x y := by
      rw [← Real.dist_eq]; exact hK.dist_le_mul x y
    calc |cutoff x₀ R x * (1 - clampUnit (f x)) - cutoff x₀ R y * (1 - clampUnit (f y))|
        ≤ |clampUnit (f x) - clampUnit (f y)| + |cutoff x₀ R x - cutoff x₀ R y| :=
          abs_mul_one_sub_sub_le (cutoff_nonneg x₀ R x) (cutoff_le_one x₀ R x)
            (clampUnit_nonneg _) (clampUnit_le_one _)
      _ ≤ K * dist x y + dist x y :=
          add_le_add ((abs_clampUnit_sub_le _ _).trans hfd) (abs_cutoff_sub_le x₀ R x y)
      _ = (↑(K + 1) : ℝ) * dist x y := by push_cast; ring
  bounded := by
    refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
    rintro _ ⟨x, rfl⟩
    have hu0 := cutoff_nonneg x₀ R x
    have hu1 := cutoff_le_one x₀ R x
    have hc0 := clampUnit_nonneg (f x)
    have hc1 := clampUnit_le_one (f x)
    exact ⟨mul_nonneg hu0 (by linarith), mul_le_one₀ hu1 (by linarith) (by linarith)⟩
  boundedSupport := by
    refine (Metric.isBounded_ball (x := x₀) (r := R + 1)).subset fun x hx => ?_
    by_contra hnot
    rw [Metric.mem_ball, not_lt] at hnot
    exact hx (by simp [cutoff_eq_zero hnot])

omit [MeasurableSpace X] [BorelSpace X] in
/-- The local slope of the reflected test exceeds that of the original by at most the
indicator of the complement of the inner ball. -/
theorem apply_reflect_le (x₀ : X) (R : ℝ) (f : Test X) (x : X) :
    Energy.LocalSlope.apply (Test.reflect x₀ R f) x ≤
      Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x := by
  have hsec : Energy.LocalSlope.apply (Test.reflect x₀ R f) x ≤
      Energy.LocalSlope.apply f x + Energy.LocalSlope.apply (cutoff x₀ R) x := by
    refine Energy.LocalSlope.apply_le_add zero_lt_one fun y _ => ?_
    change |cutoff x₀ R y * (1 - clampUnit (f y)) - cutoff x₀ R x * (1 - clampUnit (f x))| ≤
      dist (f y) (f x) + dist (cutoff x₀ R y) (cutoff x₀ R x)
    rw [Real.dist_eq, Real.dist_eq]
    exact (abs_mul_one_sub_sub_le (cutoff_nonneg x₀ R y) (cutoff_le_one x₀ R y)
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

omit [MeasurableSpace X] [BorelSpace X] in
/-- The reflected test is `L¹`-close to the complementary indicator, up to the indicator of the
complement of the inner ball. -/
theorem enorm_reflect_sub_le (x₀ : X) (R : ℝ) (f : Test X) (B : Set X) (x : X) :
    ‖Test.reflect x₀ R f x - Bᶜ.indicator (1 : X → ℝ) x‖ₑ ≤
      ‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x := by
  set i := B.indicator (1 : X → ℝ) x
  have hi : Bᶜ.indicator (1 : X → ℝ) x = 1 - i := by
    by_cases hx : x ∈ B <;> simp [i, hx]
  have hi01 : 0 ≤ i ∧ i ≤ 1 := by
    by_cases hx : x ∈ B <;> simp [i, hx]
  have hci : clampUnit i = i := clampUnit_of_mem hi01.1 hi01.2
  have hc0 : 0 ≤ clampUnit (f x) := clampUnit_nonneg _
  have hc1 : clampUnit (f x) ≤ 1 := clampUnit_le_one _
  have hu0 : 0 ≤ cutoff x₀ R x := cutoff_nonneg x₀ R x
  have hu1 : cutoff x₀ R x ≤ 1 := cutoff_le_one x₀ R x
  have hcf : |i - clampUnit (f x)| ≤ |f x - i| := by
    calc |i - clampUnit (f x)| = |clampUnit i - clampUnit (f x)| := by rw [hci]
      _ ≤ |i - f x| := abs_clampUnit_sub_le _ _
      _ = |f x - i| := abs_sub_comm _ _
  have hreal : |cutoff x₀ R x * (1 - clampUnit (f x)) - (1 - i)| ≤
      |f x - i| + (1 - cutoff x₀ R x) := by
    have key : cutoff x₀ R x * (1 - clampUnit (f x)) - (1 - i) =
        (i - clampUnit (f x)) - (1 - cutoff x₀ R x) * (1 - clampUnit (f x)) := by ring
    rw [key]
    refine (abs_sub _ _).trans (add_le_add hcf ?_)
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - cutoff x₀ R x),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - clampUnit (f x))]
    exact mul_le_of_le_one_right (by linarith) (by linarith)
  change ‖cutoff x₀ R x * (1 - clampUnit (f x)) - Bᶜ.indicator (1 : X → ℝ) x‖ₑ ≤ _
  rw [hi, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  refine ENNReal.ofReal_add_le.trans (add_le_add le_rfl ?_)
  by_cases hx : x ∈ Metric.ball x₀ R
  · rw [cutoff_eq_one (le_of_lt (Metric.mem_ball.mp hx)), sub_self, ENNReal.ofReal_zero]
    exact zero_le
  · rw [Set.indicator_of_mem (Set.mem_compl hx), Pi.one_apply]
    exact ENNReal.ofReal_le_one.mpr (by linarith)

/-- The cost of the reflected test is at most that of the original plus the mass outside the
inner ball. -/
theorem cost_reflect_le (ν : Measure X) (x₀ : X) (R : ℝ) (f : Test X) :
    cost ν (Test.reflect x₀ R f) ≤ cost ν f + ν (Metric.ball x₀ R)ᶜ := by
  unfold cost
  calc ∫⁻ x, Energy.LocalSlope.apply (Test.reflect x₀ R f) x ∂ν
      ≤ ∫⁻ x, (Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x) ∂ν :=
        lintegral_mono fun x => apply_reflect_le x₀ R f x
    _ = ∫⁻ x, Energy.LocalSlope.apply f x ∂ν + ν (Metric.ball x₀ R)ᶜ := by
        rw [lintegral_add_right _ (measurable_one.indicator Metric.isOpen_ball.measurableSet.compl),
          lintegral_indicator_one Metric.isOpen_ball.measurableSet.compl]

/-- The `L¹` distance of the reflected test to the complementary indicator. -/
theorem indicatorDistance_reflect_le (ν : Measure X) (x₀ : X) (R : ℝ) (f : Test X)
    (B : Set X) :
    indicatorDistance ν (Test.reflect x₀ R f) Bᶜ ≤
      indicatorDistance ν f B + ν (Metric.ball x₀ R)ᶜ := by
  unfold indicatorDistance
  calc ∫⁻ x, ‖Test.reflect x₀ R f x - Bᶜ.indicator (1 : X → ℝ) x‖ₑ ∂ν
      ≤ ∫⁻ x, (‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x) ∂ν :=
        lintegral_mono fun x => enorm_reflect_sub_le x₀ R f B x
    _ = _ := by
        rw [lintegral_add_right _ (measurable_one.indicator Metric.isOpen_ball.measurableSet.compl),
          lintegral_indicator_one Metric.isOpen_ball.measurableSet.compl]

/-- For a finite measure, the mass outside the ball of radius `n` tends to zero. -/
theorem tendsto_measure_compl_ball (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X) :
    Tendsto (fun n : ℕ => ν (Metric.ball x₀ n)ᶜ) atTop (𝓝 0) := by
  have hanti : Antitone fun n : ℕ => (Metric.ball x₀ (n : ℝ))ᶜ := fun m n hmn =>
    Set.compl_subset_compl.mpr (Metric.ball_subset_ball (by exact_mod_cast hmn))
  have hinter : (⋂ n : ℕ, (Metric.ball x₀ (n : ℝ))ᶜ) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_empty_iff_false,
      iff_false, not_forall, not_le]
    exact exists_nat_gt _
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => Metric.isOpen_ball.measurableSet.compl.nullMeasurableSet) hanti
    ⟨0, measure_ne_top ν _⟩
  rw [hinter, measure_empty] at h
  exact h

/-- One inequality of complement symmetry for a finite measure. -/
theorem perimeter_compl_le_of_isFiniteMeasure (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    perimeter ν Bᶜ ≤ perimeter ν B := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · rw [Subsingleton.elim Bᶜ B]
  refine le_iInf fun s => ?_
  have hε := tendsto_measure_compl_ball ν x₀
  have hconv : Tendsto (fun n : ℕ => indicatorDistance ν (Test.reflect x₀ n (s.1 n)) Bᶜ)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using s.2.add hε) (fun _ => zero_le) fun n => ?_
    exact indicatorDistance_reflect_le ν x₀ n (s.1 n) B
  calc perimeter ν Bᶜ
      ≤ liminf (fun n : ℕ => cost ν (Test.reflect x₀ n (s.1 n))) atTop :=
        perimeter_le_sequence ν Bᶜ ⟨fun n => Test.reflect x₀ n (s.1 n), hconv⟩
    _ ≤ liminf (fun n : ℕ => cost ν (s.1 n) + ν (Metric.ball x₀ n)ᶜ) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => cost_reflect_le ν x₀ n (s.1 n))
    _ = liminf (fun n => cost ν (s.1 n)) atTop := ENNReal.liminf_add_of_right_tendsto_zero hε _

/-- Complement symmetry of the metric BV perimeter for every finite measure on a metric space.
Finiteness is necessary: see `perimeter_compl_ne_real_volume`. -/
theorem perimeter_compl_of_isFiniteMeasure (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    perimeter ν Bᶜ = perimeter ν B :=
  le_antisymm (perimeter_compl_le_of_isFiniteMeasure ν B)
    (by simpa only [compl_compl] using perimeter_compl_le_of_isFiniteMeasure ν Bᶜ)


end Complement
end FunctionalInequalities.KLS.MetricBV

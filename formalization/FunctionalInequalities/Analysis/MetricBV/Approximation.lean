import FunctionalInequalities.Analysis.MetricBV.Basic
import FunctionalInequalities.Analysis.MetricBV.Complement

/-!
# Bounded-support reductions for globally Lipschitz approximations
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable [BorelSpace X]
section LipschitzBridge

/-! ### Globally Lipschitz approximating sequences

A globally Lipschitz function need neither be bounded nor have bounded support. Clamping it to
`[0, 1]` and multiplying by the radial cutoff gives a test whose slope and `L¹` errors exceed
those of the original by at most the indicator of the complement of a ball. -/

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The secant estimate behind the truncated test. -/
theorem abs_mul_sub_mul_le {u v c c' : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hc0 : 0 ≤ c')
    (hc1 : c' ≤ 1) : |u * c - v * c'| ≤ |c - c'| + |u - v| := by
  have key : u * c - v * c' = u * (c - c') + (u - v) * c' := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hc0]
  have h1 : u * |c - c'| ≤ |c - c'| := mul_le_of_le_one_left (abs_nonneg _) hu1
  have h2 : |u - v| * c' ≤ |u - v| := mul_le_of_le_one_right (abs_nonneg _) hc1
  linarith

/-- The truncated test `χ_R · clamp f` of a globally Lipschitz function. -/
def Test.truncate (x₀ : X) (R : ℝ) (f : X → ℝ) (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    Test X where
  toFun := fun x => cutoff x₀ R x * clampUnit (f x)
  lipschitz := by
    obtain ⟨K, hK⟩ := hf
    refine ⟨K + 1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Real.dist_eq]
    have hfd : |f x - f y| ≤ K * dist x y := by
      rw [← Real.dist_eq]; exact hK.dist_le_mul x y
    calc |cutoff x₀ R x * clampUnit (f x) - cutoff x₀ R y * clampUnit (f y)|
        ≤ |clampUnit (f x) - clampUnit (f y)| + |cutoff x₀ R x - cutoff x₀ R y| :=
          abs_mul_sub_mul_le (cutoff_nonneg x₀ R x) (cutoff_le_one x₀ R x)
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
    exact ⟨mul_nonneg hu0 hc0, mul_le_one₀ hu1 hc0 hc1⟩
  boundedSupport := by
    refine (Metric.isBounded_ball (x := x₀) (r := R + 1)).subset fun x hx => ?_
    by_contra hnot
    rw [Metric.mem_ball, not_lt] at hnot
    exact hx (by simp [cutoff_eq_zero hnot])

omit [MeasurableSpace X] [BorelSpace X] in
/-- The truncated test's slope exceeds the original slope by at most the indicator of the
complement of the inner ball. -/
theorem apply_truncate_le (x₀ : X) (R : ℝ) {f : X → ℝ} (hf : ∃ K : ℝ≥0, LipschitzWith K f)
    (x : X) :
    Energy.LocalSlope.apply (Test.truncate x₀ R f hf) x ≤
      Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x := by
  have hsec : Energy.LocalSlope.apply (Test.truncate x₀ R f hf) x ≤
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

omit [MeasurableSpace X] [BorelSpace X] in
/-- The truncated test's pointwise distance to an indicator exceeds that of the original by at
most the indicator of the complement of the inner ball. -/
theorem enorm_truncate_sub_le (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) (B : Set X) (x : X) :
    ‖Test.truncate x₀ R f hf x - B.indicator (1 : X → ℝ) x‖ₑ ≤
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

/-- The cost of the truncated test is at most the slope integral of the original plus the mass
outside the inner ball. -/
theorem cost_truncate_le (ν : Measure X) (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    cost ν (Test.truncate x₀ R f hf) ≤
      ∫⁻ x, Energy.LocalSlope.apply f x ∂ν + ν (Metric.ball x₀ R)ᶜ := by
  unfold cost
  calc ∫⁻ x, Energy.LocalSlope.apply (Test.truncate x₀ R f hf) x ∂ν
      ≤ ∫⁻ x, (Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x) ∂ν :=
        lintegral_mono fun x => apply_truncate_le x₀ R hf x
    _ = _ := by
        rw [lintegral_add_right _ (measurable_one.indicator Metric.isOpen_ball.measurableSet.compl),
          lintegral_indicator_one Metric.isOpen_ball.measurableSet.compl]

/-- The `L¹` distance of the truncated test to an indicator. -/
theorem indicatorDistance_truncate_le (ν : Measure X) (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) (B : Set X) :
    indicatorDistance ν (Test.truncate x₀ R f hf) B ≤
      ∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν + ν (Metric.ball x₀ R)ᶜ := by
  unfold indicatorDistance
  calc ∫⁻ x, ‖Test.truncate x₀ R f hf x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν
      ≤ ∫⁻ x, (‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x) ∂ν :=
        lintegral_mono fun x => enorm_truncate_sub_le x₀ R hf B x
    _ = _ := by
        rw [lintegral_add_right _ (measurable_one.indicator Metric.isOpen_ball.measurableSet.compl),
          lintegral_indicator_one Metric.isOpen_ball.measurableSet.compl]

/-- The explicit truncated sequence converges to the indicator in `L¹(ν)`. -/
theorem tendsto_indicatorDistance_truncate (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X)
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => indicatorDistance ν (Test.truncate x₀ n (f n) (hf n)) B)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hconv.add (tendsto_measure_compl_ball ν x₀)) (fun _ => zero_le) fun n => ?_
  exact indicatorDistance_truncate_le ν x₀ n (hf n) B

/-- The explicit truncated sequence does not increase the liminf of the slope integrals. -/
theorem liminf_cost_truncate_le (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X)
    {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n)) :
    liminf (fun n : ℕ => cost ν (Test.truncate x₀ n (f n) (hf n))) atTop ≤
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  calc liminf (fun n : ℕ => cost ν (Test.truncate x₀ n (f n) (hf n))) atTop
      ≤ liminf (fun n : ℕ => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν +
          ν (Metric.ball x₀ n)ᶜ) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => cost_truncate_le ν x₀ n (hf n))
    _ = liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop :=
        ENNReal.liminf_add_of_right_tendsto_zero (tendsto_measure_compl_ball ν x₀) _

/-- Every globally Lipschitz sequence converging to `1_B` in `L¹(ν)` is matched by an
approximating test sequence with no larger liminf cost. The Lipschitz constants may depend on
`n`, and neither values nor supports are assumed bounded; the empty carrier is included. -/
theorem exists_approximatingSequence_of_lipschitz (ν : Measure X) [IsFiniteMeasure ν]
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine ⟨⟨fun _ => Test.zero, ?_⟩, ?_⟩
    · simp [indicatorDistance, Measure.eq_zero_of_isEmpty ν]
    · simp
  · exact ⟨⟨fun n => Test.truncate x₀ n (f n) (hf n),
      tendsto_indicatorDistance_truncate ν x₀ hf hconv⟩, liminf_cost_truncate_le ν x₀ hf⟩

/-- The perimeter is bounded by the liminf slope integral of every globally Lipschitz sequence
converging to the indicator in `L¹(ν)`. -/
theorem perimeter_le_liminf_of_lipschitz (ν : Measure X) [IsFiniteMeasure ν]
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  obtain ⟨g, hg⟩ := exists_approximatingSequence_of_lipschitz ν hf hconv
  exact (perimeter_le_sequence ν B g).trans hg

/-! ### Finite-mass targets without finite total mass -/

omit [MeasurableSpace X] [BorelSpace X] in
private theorem apply_truncate_le_clamp (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) (x : X) :
    Energy.LocalSlope.apply (Test.truncate x₀ R f hf) x ≤
      Energy.LocalSlope.apply f x +
        (Metric.ball x₀ R)ᶜ.indicator (fun y => ENNReal.ofReal (clampUnit (f y))) x := by
  set c := clampUnit (f x)
  have hc0 : 0 ≤ c := clampUnit_nonneg _
  have hsec : Energy.LocalSlope.apply (Test.truncate x₀ R f hf) x ≤
      Energy.LocalSlope.apply f x +
        Energy.LocalSlope.apply (fun y => c * cutoff x₀ R y) x := by
    refine Energy.LocalSlope.apply_le_add zero_lt_one fun y _ => ?_
    change |cutoff x₀ R y * clampUnit (f y) - cutoff x₀ R x * clampUnit (f x)| ≤
      dist (f y) (f x) + dist (c * cutoff x₀ R y) (c * cutoff x₀ R x)
    have key : cutoff x₀ R y * clampUnit (f y) - cutoff x₀ R x * clampUnit (f x) =
        cutoff x₀ R y * (clampUnit (f y) - clampUnit (f x)) +
          (c * cutoff x₀ R y - c * cutoff x₀ R x) := by dsimp [c]; ring
    rw [key]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (cutoff_nonneg x₀ R y)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (cutoff_le_one x₀ R y)).trans
        (by simpa only [Real.dist_eq] using abs_clampUnit_sub_le (f y) (f x))
    · rw [Real.dist_eq]
  refine hsec.trans (add_le_add le_rfl ?_)
  by_cases hx : x ∈ Metric.ball x₀ R
  · have hr : 0 < R - dist x x₀ := by rw [Metric.mem_ball] at hx; linarith
    rw [Energy.LocalSlope.apply_eq_zero_of_eqOn_ball hr fun y hy => ?_]
    · exact zero_le
    · have hy' : dist y x₀ ≤ R := by
        have := dist_triangle y x x₀
        linarith
      rw [cutoff_eq_one hy', cutoff_eq_one (le_of_lt (Metric.mem_ball.mp hx))]
  · rw [Set.indicator_of_mem (Set.mem_compl hx)]
    have hlip : LipschitzWith ⟨c, hc0⟩ (fun y => c * cutoff x₀ R y) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hc0]
        exact mul_le_mul_of_nonneg_left (abs_cutoff_sub_le x₀ R a b) hc0
    exact (Energy.LocalSlope.apply_le_of_lipschitzWith hlip x).trans_eq
      (ENNReal.coe_nnreal_eq ⟨c, hc0⟩)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
private theorem ofReal_clampUnit_le_indicator_error (f : X → ℝ) (B : Set X) (x : X) :
    ENNReal.ofReal (clampUnit (f x)) ≤ ‖f x - B.indicator (1 : X → ℝ) x‖ₑ +
      B.indicator (1 : X → ENNReal) x := by
  by_cases hx : x ∈ B
  · simp only [Set.indicator_of_mem hx, Pi.one_apply]
    exact (ENNReal.ofReal_le_one.2 (clampUnit_le_one _)).trans (le_add_left le_rfl)
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, sub_zero, add_zero,
      Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    simpa only [clampUnit_of_mem (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1),
      sub_zero, abs_of_nonneg (clampUnit_nonneg _)] using abs_clampUnit_sub_le (f x) 0

omit [MeasurableSpace X] [BorelSpace X] in
private theorem apply_truncate_le_indicator_error (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) (B : Set X) (x : X) :
    Energy.LocalSlope.apply (Test.truncate x₀ R f hf) x ≤
      Energy.LocalSlope.apply f x +
        (‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (B \ Metric.ball x₀ R).indicator 1 x) := by
  refine (apply_truncate_le_clamp x₀ R hf x).trans (add_le_add le_rfl ?_)
  by_cases hx : x ∈ Metric.ball x₀ R
  · rw [Set.indicator_of_notMem (show x ∉ (Metric.ball x₀ R)ᶜ from fun h => h hx)]
    exact zero_le
  · rw [Set.indicator_of_mem (Set.mem_compl hx)]
    by_cases hb : x ∈ B <;> simpa [hb, hx] using ofReal_clampUnit_le_indicator_error f B x

omit [MeasurableSpace X] [BorelSpace X] in
/-- The cutoff error is controlled by the original indicator error and the target outside the
inner ball, rather than by all the mass outside that ball. -/
theorem enorm_truncate_sub_le_target_tail (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) (B : Set X) (x : X) :
    ‖Test.truncate x₀ R f hf x - B.indicator (1 : X → ℝ) x‖ₑ ≤
      ‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (B \ Metric.ball x₀ R).indicator 1 x := by
  have hu0 := cutoff_nonneg x₀ R x
  have hu1 := cutoff_le_one x₀ R x
  have hc0 := clampUnit_nonneg (f x)
  have hc1 := clampUnit_le_one (f x)
  change ‖cutoff x₀ R x * clampUnit (f x) - B.indicator (1 : X → ℝ) x‖ₑ ≤ _
  by_cases hb : x ∈ B
  · simp only [Set.indicator_of_mem hb, Pi.one_apply]
    by_cases hx : x ∈ Metric.ball x₀ R
    · rw [cutoff_eq_one (le_of_lt (Metric.mem_ball.mp hx)), one_mul,
        Set.indicator_of_notMem (show x ∉ B \ Metric.ball x₀ R from fun h => h.2 hx), add_zero,
        Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      apply ENNReal.ofReal_le_ofReal
      simpa only [clampUnit_of_mem zero_le_one le_rfl] using abs_clampUnit_sub_le (f x) 1
    · rw [Set.indicator_of_mem (show x ∈ B \ Metric.ball x₀ R from ⟨hb, hx⟩), Pi.one_apply]
      refine (show ‖cutoff x₀ R x * clampUnit (f x) - 1‖ₑ ≤ 1 from ?_).trans
        (le_add_left le_rfl)
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_one.2 (abs_le.2 ⟨by nlinarith, by nlinarith⟩)
  · simp only [Set.indicator_of_notMem hb, sub_zero,
      Set.indicator_of_notMem (show x ∉ B \ Metric.ball x₀ R from fun h => hb h.1), add_zero,
      Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (mul_nonneg hu0 hc0)]
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_of_le_one_left hc0 hu1).trans (by
      simpa only [clampUnit_of_mem (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1),
        sub_zero, abs_of_nonneg hc0] using abs_clampUnit_sub_le (f x) 0)

/-- The cutoff adds at most the original indicator L1 error and the target mass outside
the inner ball to the slope integral. No finite-total-mass hypothesis is needed. -/
theorem cost_truncate_le_target_tail (ν : Measure X) (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) {B : Set X} (hB : MeasurableSet B) :
    cost ν (Test.truncate x₀ R f hf) ≤
      (∫⁻ x, Energy.LocalSlope.apply f x ∂ν) +
        ((∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) + ν (B \ Metric.ball x₀ R)) := by
  obtain ⟨K, hK⟩ := hf
  have he : Measurable (fun x => ‖f x - B.indicator (1 : X → ℝ) x‖ₑ) :=
    (hK.continuous.measurable.sub (measurable_one.indicator hB)).enorm
  have ht : MeasurableSet (B \ Metric.ball x₀ R) := hB.diff Metric.isOpen_ball.measurableSet
  calc cost ν (Test.truncate x₀ R f ⟨K, hK⟩)
      ≤ ∫⁻ x, Energy.LocalSlope.apply f x +
          (‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (B \ Metric.ball x₀ R).indicator 1 x) ∂ν :=
        lintegral_mono (apply_truncate_le_indicator_error x₀ R ⟨K, hK⟩ B)
    _ = (∫⁻ x, Energy.LocalSlope.apply f x ∂ν) +
        ∫⁻ x, (‖f x - B.indicator (1 : X → ℝ) x‖ₑ +
          (B \ Metric.ball x₀ R).indicator 1 x) ∂ν :=
      lintegral_add_right _ (he.add (measurable_one.indicator ht))
    _ = _ := by
      rw [lintegral_add_right _ (measurable_one.indicator ht), lintegral_indicator_one ht]

/-- The indicator L1 error after truncation is at most the original error plus target
mass outside the inner ball, for every Borel measure. -/
theorem indicatorDistance_truncate_le_target_tail (ν : Measure X) (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) {B : Set X} (hB : MeasurableSet B) :
    indicatorDistance ν (Test.truncate x₀ R f hf) B ≤
      (∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) + ν (B \ Metric.ball x₀ R) := by
  have ht : MeasurableSet (B \ Metric.ball x₀ R) := hB.diff Metric.isOpen_ball.measurableSet
  calc indicatorDistance ν (Test.truncate x₀ R f hf) B
      ≤ ∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (B \ Metric.ball x₀ R).indicator 1 x ∂ν :=
        lintegral_mono (enorm_truncate_sub_le_target_tail x₀ R hf B)
    _ = _ := by
      rw [lintegral_add_right _ (measurable_one.indicator ht), lintegral_indicator_one ht]

/-- A measurable target of finite mass has vanishing mass outside expanding balls,
even when the measure has infinite total mass. -/
theorem tendsto_measure_diff_ball (ν : Measure X) (x₀ : X) {B : Set X} (hB : MeasurableSet B)
    (hνB : ν B ≠ ⊤) :
    Tendsto (fun n : ℕ => ν (B \ Metric.ball x₀ (n : ℝ))) atTop (𝓝 0) := by
  have hanti : Antitone fun n : ℕ => B \ Metric.ball x₀ (n : ℝ) := fun m n hmn =>
    Set.sdiff_subset_sdiff_right (Metric.ball_subset_ball (by exact_mod_cast hmn))
  have hinter : (⋂ n : ℕ, B \ Metric.ball x₀ (n : ℝ)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (dist x x₀)
    exact (Set.mem_iInter.1 hx n).2 (Metric.mem_ball.2 hn)
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (hB.diff Metric.isOpen_ball.measurableSet).nullMeasurableSet) hanti
    ⟨0, ne_top_of_le_ne_top hνB (measure_mono Set.sdiff_subset)⟩
  rwa [hinter, measure_empty] at h

/-- Fixed radii n suffice for the truncated sequence to converge in global L1 to a
measurable finite-mass target. No finite-total-mass hypothesis is needed. -/
theorem tendsto_indicatorDistance_truncate_of_measure_lt_top (ν : Measure X) (x₀ : X) {B : Set X}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) {f : ℕ → X → ℝ}
    (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => indicatorDistance ν (Test.truncate x₀ n (f n) (hf n)) B)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hconv.add (tendsto_measure_diff_ball ν x₀ hB hνB.ne)) (fun _ => zero_le) fun n => ?_
  exact indicatorDistance_truncate_le_target_tail ν x₀ n (hf n) hB

/-- For a measurable finite-mass target and an actual global L1-convergent Lipschitz
sequence, fixed-radius truncation does not increase the liminf slope integral. -/
theorem liminf_cost_truncate_le_of_measure_lt_top (ν : Measure X) (x₀ : X) {B : Set X}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) {f : ℕ → X → ℝ}
    (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    liminf (fun n : ℕ => cost ν (Test.truncate x₀ n (f n) (hf n))) atTop ≤
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  calc liminf (fun n : ℕ => cost ν (Test.truncate x₀ n (f n) (hf n))) atTop
      ≤ liminf (fun n : ℕ => (∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) +
          ((∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) +
            ν (B \ Metric.ball x₀ (n : ℝ)))) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => cost_truncate_le_target_tail ν x₀ n (hf n) hB)
    _ = _ := ENNReal.liminf_add_of_right_tendsto_zero
        (by simpa using hconv.add (tendsto_measure_diff_ball ν x₀ hB hνB.ne)) _

/-- The bounded-support reduction of ADMG Remark 3.4 at a measurable finite-mass target,
for every Borel measure: globally Lipschitz approximants are matched by actual tests
with the same global L1 limit and no larger liminf slope integral. Empty carriers
and infinite costs are included. -/
theorem exists_approximatingSequence_of_lipschitz_of_measure_lt_top (ν : Measure X) {B : Set X}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) {f : ℕ → X → ℝ}
    (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine ⟨⟨fun _ => Test.zero, ?_⟩, ?_⟩
    · simp [indicatorDistance, Measure.eq_zero_of_isEmpty ν]
    · simp
  · exact ⟨⟨fun n => Test.truncate x₀ n (f n) (hf n),
      tendsto_indicatorDistance_truncate_of_measure_lt_top ν x₀ hB hνB hf hconv⟩,
      liminf_cost_truncate_le_of_measure_lt_top ν x₀ hB hνB hf hconv⟩

/-- Every globally Lipschitz sequence converging in global L1 to a measurable finite-mass
target bounds the metric BV perimeter, without requiring finite total mass. -/
theorem perimeter_le_liminf_of_lipschitz_of_measure_lt_top (ν : Measure X) {B : Set X}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) {f : ℕ → X → ℝ}
    (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  obtain ⟨g, hg⟩ := exists_approximatingSequence_of_lipschitz_of_measure_lt_top ν hB hνB hf hconv
  exact (perimeter_le_sequence ν B g).trans hg

end LipschitzBridge

end FunctionalInequalities.KLS.MetricBV

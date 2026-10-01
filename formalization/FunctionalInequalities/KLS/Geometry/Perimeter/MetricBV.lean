import FunctionalInequalities.Energy.LocalSlope.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.Bornology.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Fintype.EquivFin

/-!
# Metric BV perimeter

The test class and sequential relaxation use the metric and the actual measure on the
space. In particular this is distinct from weighted smooth-domain relative perimeter.
The local slope is `Energy.LocalSlope.apply`, which is zero at isolated points.

For every Borel measure, a threshold above the perimeter admits single tests arbitrarily close to
the indicator (`exists_test_lt_of_perimeter_lt`), and finite perimeter is the limit of the costs of
an explicitly selected approximating sequence (`recoverySequence`, `exists_recoverySequence`).
Infinite perimeter may come from an empty approximation class; no recovery sequence is claimed.
The perimeter is sequentially lower semicontinuous under global `L¹(ν)` convergence of measurable
set indicators (`perimeter_le_liminf_of_tendsto`), by a diagonal choice of epsilon tests.
Every test's cost is bounded by its Lipschitz constant times the mass of its closed function
support (`cost_le_mul_measure_closure_support`); finite mass of that closed support suffices for
finite cost (`cost_ne_top_of_support_measure`), including measures with infinite total mass.

Complement symmetry holds on finite spaces for every measure (`perimeter_compl`) and on every
metric space for every finite measure (`perimeter_compl_of_isFiniteMeasure`), through the
clamped, radially cut-off reflection `Test.reflect`; in particular it holds for the closed
support law (`perimeter_compl_closedSupportLaw`). Finiteness cannot be dropped: for Lebesgue
measure on `ℝ` the empty set has perimeter zero and the line has infinite perimeter
(`perimeter_compl_ne_real_volume`).

For a finite measure, globally Lipschitz approximants may replace tests: a sequence of globally
Lipschitz functions, with arbitrary constants, values and supports, converging to `1_B` in
`L¹(ν)` is matched by the explicit truncated tests `Test.truncate x₀ n (f n)` with the same limit
and no larger liminf cost (`exists_approximatingSequence_of_lipschitz`), so the perimeter is
bounded by its liminf slope integral (`perimeter_le_liminf_of_lipschitz`). This is a statement
about global Lipschitz functions and global `L¹` convergence only. For a measurable target of
finite mass the same reduction holds for every Borel measure, including infinite total mass
(`exists_approximatingSequence_of_lipschitz_of_measure_lt_top`): stronger cutoff estimates use
the original indicator error and target mass outside the inner ball, both tending to zero.
Fixed radii `n` suffice, and the original finite-measure arbitrary-target signatures remain.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Bounded Lipschitz functions with bounded (function) support, the `Lip_b(X)`
class used by De Ponti--Mondino. -/
structure Test (X : Type*) [MetricSpace X] where
  toFun : X → ℝ
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K toFun
  bounded : Bornology.IsBounded (Set.range toFun)
  boundedSupport : Bornology.IsBounded (Function.support toFun)

instance : CoeFun (Test X) (fun _ => X → ℝ) := ⟨Test.toFun⟩

omit [MeasurableSpace X] in
/-- The local slope is invariant under reflection of values about `1/2`. -/
theorem localSlope_one_sub (f : X → ℝ) (x : X) :
    Energy.LocalSlope.apply (fun y => 1 - f y) x = Energy.LocalSlope.apply f x := by
  unfold Energy.LocalSlope.apply
  congr 1
  funext r
  congr 1
  funext hr
  congr 1
  funext y
  congr 1
  funext hy
  simp only [Real.dist_eq]
  rw [show (1 - f y) - (1 - f x) = f x - f y by ring, abs_sub_comm]

/-- The integral of the pointwise local metric slope, without a factor `1/2`. -/
def cost [BorelSpace X] (ν : Measure X) (f : Test X) : ENNReal :=
  ∫⁻ x, Energy.LocalSlope.apply f x ∂ν

/-- Extended-real `L¹` distance from a test to the indicator of a set. -/
def indicatorDistance [BorelSpace X] (ν : Measure X) (f : Test X) (B : Set X) : ENNReal :=
  ∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν

/-- A concrete test sequence converging to the indicator in `L¹(ν)`. -/
def ApproximatingSequence [BorelSpace X] (ν : Measure X) (B : Set X) : Type _ :=
  {f : ℕ → Test X // Tendsto (fun n => indicatorDistance ν (f n) B) atTop (𝓝 0)}

/-- Metric BV perimeter as the `L¹` relaxation of the local-slope integral.
An empty approximation class has perimeter `⊤`. -/
def perimeter [BorelSpace X] (ν : Measure X) (B : Set X) : ENNReal :=
  ⨅ f : ApproximatingSequence ν B, liminf (fun n => cost ν (f.1 n)) atTop

variable [BorelSpace X]

theorem perimeter_le_sequence (ν : Measure X) (B : Set X)
    (f : ApproximatingSequence ν B) :
    perimeter ν B ≤ liminf (fun n => cost ν (f.1 n)) atTop :=
  iInf_le _ f

/-- Epsilon recovery test: below any threshold above the perimeter there are single tests that
are arbitrarily `L¹`-close to the indicator. The liminf only gives frequently small costs, which
are intersected with the eventually small distances. The threshold may be `⊤`; no finiteness of
the measure or perimeter is assumed (an empty approximation class makes the perimeter `⊤`). -/
theorem exists_test_lt_of_perimeter_lt (ν : Measure X) (B : Set X) {a : ENNReal}
    (ha : perimeter ν B < a) {ε : ENNReal} (hε : 0 < ε) :
    ∃ g : Test X, indicatorDistance ν g B < ε ∧ cost ν g < a := by
  obtain ⟨s, hs⟩ := iInf_lt_iff.mp ha
  have hfreq : ∃ᶠ n in atTop, cost ν (s.1 n) < a := frequently_lt_of_liminf_lt (by isBoundedDefault) hs
  have hev : ∀ᶠ n in atTop, indicatorDistance ν (s.1 n) B < ε := s.2.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := (hfreq.and_eventually hev).exists
  exact ⟨s.1 n, hn.2, hn.1⟩

/-- An approximating sequence whose limsup cost is at most the perimeter has costs converging to
the perimeter: the liminf lower bound is `perimeter_le_sequence`. No finiteness is assumed. -/
theorem tendsto_cost_of_limsup_le {ν : Measure X} {B : Set X} (s : ApproximatingSequence ν B)
    (h : limsup (fun n => cost ν (s.1 n)) atTop ≤ perimeter ν B) :
    Tendsto (fun n => cost ν (s.1 n)) atTop (𝓝 (perimeter ν B)) :=
  tendsto_of_le_liminf_of_limsup_le (perimeter_le_sequence ν B s) h

/-- For finite perimeter, a test chosen by the epsilon recovery test with error below `ε` and
cost below `perimeter ν B + η`. -/
def recoveryTest {ν : Measure X} {B : Set X} (hB : perimeter ν B < ⊤) {ε η : ENNReal}
    (hε : 0 < ε) (hη : 0 < η) : Test X :=
  Classical.choose
    (exists_test_lt_of_perimeter_lt ν B (ENNReal.lt_add_right hB.ne hη.ne') hε)

theorem indicatorDistance_recoveryTest_lt {ν : Measure X} {B : Set X} (hB : perimeter ν B < ⊤)
    {ε η : ENNReal} (hε : 0 < ε) (hη : 0 < η) :
    indicatorDistance ν (recoveryTest hB hε hη) B < ε :=
  (Classical.choose_spec
    (exists_test_lt_of_perimeter_lt ν B (ENNReal.lt_add_right hB.ne hη.ne') hε)).1

theorem cost_recoveryTest_lt {ν : Measure X} {B : Set X} (hB : perimeter ν B < ⊤)
    {ε η : ENNReal} (hε : 0 < ε) (hη : 0 < η) :
    cost ν (recoveryTest hB hε hη) < perimeter ν B + η :=
  (Classical.choose_spec
    (exists_test_lt_of_perimeter_lt ν B (ENNReal.lt_add_right hB.ne hη.ne') hε)).2

/-- The recovery sequence for finite perimeter, from positive errors `ε n → 0` and positive
threshold excesses `η n`: the `n`-th term is `recoveryTest hB (hε0 n) (hη0 n)`. -/
def recoverySequence {ν : Measure X} {B : Set X} (hB : perimeter ν B < ⊤) {ε η : ℕ → ENNReal}
    (hε0 : ∀ n, 0 < ε n) (hη0 : ∀ n, 0 < η n) (hε : Tendsto ε atTop (𝓝 0)) :
    ApproximatingSequence ν B :=
  ⟨fun n => recoveryTest hB (hε0 n) (hη0 n),
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε (fun _ => zero_le)
      (fun n => (indicatorDistance_recoveryTest_lt hB (hε0 n) (hη0 n)).le)⟩

theorem indicatorDistance_recoverySequence_lt {ν : Measure X} {B : Set X}
    (hB : perimeter ν B < ⊤) {ε η : ℕ → ENNReal} (hε0 : ∀ n, 0 < ε n) (hη0 : ∀ n, 0 < η n)
    (hε : Tendsto ε atTop (𝓝 0)) (n : ℕ) :
    indicatorDistance ν ((recoverySequence hB hε0 hη0 hε).1 n) B < ε n :=
  indicatorDistance_recoveryTest_lt hB (hε0 n) (hη0 n)

theorem cost_recoverySequence_lt {ν : Measure X} {B : Set X}
    (hB : perimeter ν B < ⊤) {ε η : ℕ → ENNReal} (hε0 : ∀ n, 0 < ε n) (hη0 : ∀ n, 0 < η n)
    (hε : Tendsto ε atTop (𝓝 0)) (n : ℕ) :
    cost ν ((recoverySequence hB hε0 hη0 hε).1 n) < perimeter ν B + η n :=
  cost_recoveryTest_lt hB (hε0 n) (hη0 n)

/-- If also `η n → 0`, the costs of the recovery sequence converge to the perimeter. -/
theorem tendsto_cost_recoverySequence {ν : Measure X} {B : Set X}
    (hB : perimeter ν B < ⊤) {ε η : ℕ → ENNReal} (hε0 : ∀ n, 0 < ε n) (hη0 : ∀ n, 0 < η n)
    (hε : Tendsto ε atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => cost ν ((recoverySequence hB hε0 hη0 hε).1 n)) atTop
      (𝓝 (perimeter ν B)) := by
  refine tendsto_cost_of_limsup_le _ ?_
  have hlim : Tendsto (fun n => perimeter ν B + η n) atTop (𝓝 (perimeter ν B)) := by
    simpa using tendsto_const_nhds.add hη
  calc limsup (fun n => cost ν ((recoverySequence hB hε0 hη0 hε).1 n)) atTop
      ≤ limsup (fun n => perimeter ν B + η n) atTop :=
        limsup_le_limsup (Eventually.of_forall fun n =>
          (cost_recoverySequence_lt hB hε0 hη0 hε n).le)
    _ = perimeter ν B := hlim.limsup_eq

/-- Recovery sequence: finite perimeter is attained as the limit of the costs of an actual
approximating sequence (errors and threshold excesses `(n + 1)⁻¹`). For infinite perimeter the
approximation class may be empty, and nothing is claimed. -/
theorem exists_recoverySequence (ν : Measure X) (B : Set X) (hB : perimeter ν B < ⊤) :
    ∃ g : ApproximatingSequence ν B,
      Tendsto (fun n => cost ν (g.1 n)) atTop (𝓝 (perimeter ν B)) := by
  have h0 : ∀ n : ℕ, 0 < (((n + 1 : ℕ) : ENNReal))⁻¹ := fun n =>
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  have hlim : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ENNReal))⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  exact ⟨recoverySequence hB h0 h0 hlim, tendsto_cost_recoverySequence hB h0 h0 hlim hlim⟩

/-- Triangle bound for the indicator distance through a measurable intermediate set. -/
theorem indicatorDistance_le_add (ν : Measure X) (g : Test X) (B : Set X) {C : Set X}
    (hC : MeasurableSet C) :
    indicatorDistance ν g B ≤
      indicatorDistance ν g C + ∫⁻ x, ‖C.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν := by
  obtain ⟨K, hK⟩ := g.lipschitz
  have hmeas : AEMeasurable (fun x => ‖g x - C.indicator (1 : X → ℝ) x‖ₑ) ν :=
    (hK.continuous.measurable.sub (measurable_one.indicator hC)).enorm.aemeasurable
  unfold indicatorDistance
  calc ∫⁻ x, ‖g x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν
      ≤ ∫⁻ x, (‖g x - C.indicator (1 : X → ℝ) x‖ₑ +
          ‖C.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ) ∂ν :=
        lintegral_mono fun x => by
          rw [← sub_add_sub_cancel (g x) (C.indicator (1 : X → ℝ) x)]
          exact enorm_add_le _ _
    _ = _ := lintegral_add_left' hmeas _

/-- Sequential lower semicontinuity of the perimeter under global `L¹(ν)` convergence of set
indicators, for every Borel measure. Diagonal selection: below any `a` above the liminf, frequent
indices with perimeter below `a` and small set distance carry epsilon tests, which approximate
the limit set by the triangle bound. The liminf and the perimeters may be `⊤`; measurability of
the limit set is not needed. -/
theorem perimeter_le_liminf_of_tendsto (ν : Measure X) {B : Set X} {Bn : ℕ → Set X}
    (hBn : ∀ n, MeasurableSet (Bn n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(Bn n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => perimeter ν (Bn n)) atTop := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  have hfreq : ∃ᶠ n in atTop, perimeter ν (Bn n) < a :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) ha
  have hε0 : ∀ k : ℕ, 0 < (((k + 1 : ℕ) : ENNReal))⁻¹ := fun k =>
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  have hεlim : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ENNReal))⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hidx : ∀ k : ℕ, ∃ n, perimeter ν (Bn n) < a ∧
      ∫⁻ x, ‖(Bn n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν <
        (((k + 1 : ℕ) : ENNReal))⁻¹ := fun k =>
    (hfreq.and_eventually (hconv.eventually (gt_mem_nhds (hε0 k)))).exists
  choose m hm using hidx
  have htest : ∀ k : ℕ, ∃ g : Test X, indicatorDistance ν g (Bn (m k)) <
      (((k + 1 : ℕ) : ENNReal))⁻¹ ∧ cost ν g < a := fun k =>
    exists_test_lt_of_perimeter_lt ν _ (hm k).1 (hε0 k)
  choose g hg using htest
  have hd : ∀ k, indicatorDistance ν (g k) B ≤
      (((k + 1 : ℕ) : ENNReal))⁻¹ + (((k + 1 : ℕ) : ENNReal))⁻¹ := fun k =>
    (indicatorDistance_le_add ν (g k) B (hBn (m k))).trans (add_le_add (hg k).1.le (hm k).2.le)
  have hlim : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ENNReal))⁻¹ + (((k + 1 : ℕ) : ENNReal))⁻¹)
      atTop (𝓝 0) := by
    simpa using hεlim.add hεlim
  let s : ApproximatingSequence ν B :=
    ⟨g, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hd⟩
  calc perimeter ν B ≤ liminf (fun k => cost ν (s.1 k)) atTop := perimeter_le_sequence ν B s
    _ ≤ a := liminf_le_of_frequently_le' (Frequently.of_forall fun k => (hg k).2.le)

/-- Mass is controlled by the set-indicator `L¹` distance: `ν A ≤ ν B + ∫ ‖1_A - 1_B‖ₑ dν`. -/
theorem measure_le_add_lintegral_indicator_sub {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ν A ≤ ν B + ∫⁻ x, ‖A.indicator (1 : α → ℝ) x - B.indicator 1 x‖ₑ ∂ν := by
  have hdiff : ν (A \ B) ≤ ∫⁻ x, ‖A.indicator (1 : α → ℝ) x - B.indicator 1 x‖ₑ ∂ν := by
    rw [← lintegral_indicator_one (hA.diff hB)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ A \ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx.1, Set.indicator_of_notMem hx.2]
      simp
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc ν A ≤ ν (B ∪ A \ B) := measure_mono fun x hx => by
        by_cases h : x ∈ B
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
    _ ≤ ν B + ν (A \ B) := measure_union_le _ _
    _ ≤ ν B + ∫⁻ x, ‖A.indicator (1 : α → ℝ) x - B.indicator 1 x‖ₑ ∂ν := by gcongr

/-- Mass continuity: for a finite measure, measurable sets converging to a measurable `B` in the
set-indicator `L¹` distance have masses converging to `ν B`. -/
theorem tendsto_measure_of_tendsto_indicator {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] {A : ℕ → Set α} {B : Set α} (hA : ∀ n, MeasurableSet (A n))
    (hB : MeasurableSet B)
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : α → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    Tendsto (fun n => ν (A n)) atTop (𝓝 (ν B)) := by
  rw [ENNReal.tendsto_nhds (measure_ne_top ν B)]
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hconv ε hε] with n hn
  refine ⟨tsub_le_iff_right.2 ?_, ?_⟩
  · have h := measure_le_add_lintegral_indicator_sub ν hB (hA n)
    simp_rw [enorm_sub_rev (B.indicator (1 : α → ℝ) _)] at h
    exact h.trans (by gcongr)
  · exact (measure_le_add_lintegral_indicator_sub ν (hA n) hB).trans (by gcongr)

/-- The zero function is a test on every metric space: its support is empty. -/
def Test.zero : Test X where
  toFun := fun _ => 0
  lipschitz := ⟨0, LipschitzWith.const 0⟩
  bounded := (Bornology.isBounded_singleton (x := (0 : ℝ))).subset (by
    rintro y ⟨x, rfl⟩
    simp)
  boundedSupport := by simp

@[simp] theorem cost_zero (ν : Measure X) : cost ν Test.zero = 0 := by
  simp [cost, Test.zero, Energy.LocalSlope.apply_const]

omit [MeasurableSpace X] [BorelSpace X] in
private theorem localSlope_eq_zero_outside_closure_support (f : Test X) {x : X}
    (hx : x ∉ closure (Function.support f)) : Energy.LocalSlope.apply f x = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hx
  have hx0 : f x = 0 := by
    simpa only [Function.mem_support, not_not] using
      (show x ∉ Function.support f from fun h => hx (subset_closure h))
  refine Energy.LocalSlope.apply_eq_zero_of_eqOn_ball hr fun y hy => ?_
  have hy0 : f y = 0 := by
    simpa only [Function.mem_support, not_not] using
      (show y ∉ Function.support f from fun h =>
        hball (by simpa only [Metric.mem_ball, dist_comm] using hy) (subset_closure h))
  rw [hx0, hy0]

/-- The test cost is controlled by the mass of its closed function support, even when the
measure has infinite total mass. Boundary points of the function support are retained. -/
theorem cost_le_mul_measure_closure_support (ν : Measure X) (f : Test X) {K : ℝ≥0}
    (hK : LipschitzWith K f) : cost ν f ≤ K * ν (closure (Function.support f)) := by
  have hbound : ∀ x, Energy.LocalSlope.apply f x ≤
      (closure (Function.support f)).indicator (fun _ => (K : ENNReal)) x := by
    intro x
    by_cases hx : x ∈ closure (Function.support f)
    · rw [Set.indicator_of_mem hx]
      exact Energy.LocalSlope.apply_le_of_lipschitzWith hK x
    · rw [localSlope_eq_zero_outside_closure_support f hx, Set.indicator_of_notMem hx]
  exact (lintegral_mono hbound).trans_eq
    (lintegral_indicator_const isClosed_closure.measurableSet _)

/-- Finite mass of the closed function support suffices for finite test cost; no finiteness
of the measure on the whole space is required. -/
theorem cost_ne_top_of_support_measure (ν : Measure X) (f : Test X)
    (hf : ν (closure (Function.support f)) ≠ ⊤) : cost ν f ≠ ⊤ := by
  obtain ⟨K, hK⟩ := f.lipschitz
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hf)
    (cost_le_mul_measure_closure_support ν f hK)

/-- For a finite measure every test has finite cost. -/
theorem cost_ne_top (ν : Measure X) [IsFiniteMeasure ν] (f : Test X) : cost ν f ≠ ⊤ :=
  cost_ne_top_of_support_measure ν f (measure_ne_top ν _)

/-- The empty set has zero perimeter for every measure, witnessed by the zero test. -/
theorem perimeter_empty (ν : Measure X) : perimeter ν (∅ : Set X) = 0 := by
  have h : perimeter ν ∅ ≤ liminf (fun _ : ℕ => cost ν Test.zero) atTop :=
    perimeter_le_sequence ν ∅ ⟨fun _ => Test.zero, by
      simp [indicatorDistance, Test.zero]⟩
  exact le_antisymm (h.trans_eq (by simp)) bot_le

section FiniteSpace

variable [Finite X]

/-- A constant is a bounded-support test on a finite space. -/
def Test.const (c : ℝ) : Test X where
  toFun := fun _ => c
  lipschitz := ⟨0, LipschitzWith.const c⟩
  bounded := (Bornology.isBounded_singleton (x := c)).subset (by
    rintro y ⟨x, rfl⟩
    simp)
  boundedSupport := Set.finite_univ.isBounded.subset (Set.subset_univ _)

@[simp] theorem cost_const (ν : Measure X) (c : ℝ) :
    cost ν (Test.const c) = 0 := by
  simp [cost, Test.const, Energy.LocalSlope.apply_const]

theorem perimeter_univ (ν : Measure X) : perimeter ν (Set.univ : Set X) = 0 := by
  have h : perimeter ν Set.univ ≤ liminf (fun _ : ℕ => cost ν (Test.const 1)) atTop :=
    perimeter_le_sequence ν Set.univ ⟨fun _ => Test.const 1, by
      simp [indicatorDistance, Test.const]⟩
  simpa [cost_const] using (le_antisymm (h.trans_eq (by simp [cost_const])) bot_le)

end FiniteSpace

section FiniteComplement

variable [Finite X]

/-- Reflection preserves the bounded-support test class on a finite space. -/
def Test.oneSub (f : Test X) : Test X where
  toFun := fun x => 1 - f x
  lipschitz := by
    obtain ⟨K, hK⟩ := f.lipschitz
    exact ⟨K, by simpa using (LipschitzWith.const (1 : ℝ)).sub hK⟩
  bounded := (Set.finite_range (fun x => 1 - f x)).isBounded
  boundedSupport := Set.finite_univ.isBounded.subset (Set.subset_univ _)

@[simp] theorem cost_oneSub (ν : Measure X) (f : Test X) :
    cost ν (Test.oneSub f) = cost ν f := by
  simp [cost, Test.oneSub, localSlope_one_sub]

theorem indicatorDistance_oneSub (ν : Measure X) (f : Test X) (B : Set X) :
    indicatorDistance ν (Test.oneSub f) Bᶜ = indicatorDistance ν f B := by
  have hpoint (x : X) : Bᶜ.indicator (1 : X → ℝ) x =
      1 - B.indicator (1 : X → ℝ) x := by
    by_cases hx : x ∈ B
    · simp [hx]
    · simp [hx]
  unfold indicatorDistance
  congr 1
  funext x
  simp only [Test.oneSub, hpoint]
  rw [show (1 - f x) - (1 - B.indicator (1 : X → ℝ) x) =
      -(f x - B.indicator (1 : X → ℝ) x) by ring, enorm_neg]

/-- Complement symmetry on a finite metric space. -/
theorem perimeter_compl (ν : Measure X) (B : Set X) :
    perimeter ν Bᶜ = perimeter ν B := by
  have hle (A : Set X) : perimeter ν Aᶜ ≤ perimeter ν A := by
    unfold perimeter
    refine le_iInf fun s => ?_
    have hconv : Tendsto
        (fun n => indicatorDistance ν (Test.oneSub (s.1 n)) Aᶜ) atTop (𝓝 0) := by
      simpa only [indicatorDistance_oneSub] using s.2
    have h := iInf_le (fun f : ApproximatingSequence ν Aᶜ =>
      liminf (fun n => cost ν (f.1 n)) atTop)
        (⟨fun n => Test.oneSub (s.1 n), hconv⟩ : ApproximatingSequence ν Aᶜ)
    exact h.trans_eq (by simp only [cost_oneSub])
  exact le_antisymm (hle B) (by simpa only [compl_compl] using hle Bᶜ)

end FiniteComplement

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

/-- If every bounded set has co-infinite mass, no bounded-support test approximates the constant
one, so the whole space has infinite perimeter. -/
theorem perimeter_univ_eq_top_of_forall_isBounded (ν : Measure X)
    (h : ∀ S : Set X, Bornology.IsBounded S → ν Sᶜ = ⊤) :
    perimeter ν Set.univ = ⊤ := by
  refine iInf_eq_top.mpr fun s => ?_
  exfalso
  have hlarge (f : Test X) : indicatorDistance ν f Set.univ = ⊤ := by
    set K := closure (Function.support f.toFun)
    have hK : Bornology.IsBounded K := f.boundedSupport.closure
    have hbound : ∀ x, Kᶜ.indicator (1 : X → ENNReal) x ≤
        ‖f x - (Set.univ : Set X).indicator (1 : X → ℝ) x‖ₑ := by
      intro x
      by_cases hx : x ∈ K
      · simp [hx]
      · have hfx : f x = 0 := by
          by_contra hne
          exact hx (subset_closure hne)
        simp [hx, hfx]
    refine top_le_iff.mp ?_
    calc (⊤ : ENNReal) = ν Kᶜ := (h K hK).symm
      _ = ∫⁻ x, Kᶜ.indicator 1 x ∂ν := (lintegral_indicator_one isClosed_closure.measurableSet.compl).symm
      _ ≤ indicatorDistance ν f Set.univ := lintegral_mono hbound
  have := s.2
  simp only [hlarge] at this
  exact ENNReal.top_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)

/-- Complement symmetry fails for Lebesgue measure on the real line: the empty set has perimeter
zero while the whole line has infinite perimeter. -/
theorem perimeter_compl_ne_real_volume :
    perimeter (volume : Measure ℝ) (∅ : Set ℝ)ᶜ ≠ perimeter (volume : Measure ℝ) ∅ := by
  rw [Set.compl_empty, perimeter_empty,
    perimeter_univ_eq_top_of_forall_isBounded (volume : Measure ℝ) fun S hS => ?_]
  · exact ENNReal.top_ne_zero
  obtain ⟨b, hb⟩ := hS.bddAbove
  refine top_le_iff.mp ((Real.volume_Ioi (a := b)).symm.le.trans (measure_mono fun x hx => ?_))
  exact fun hxS => not_le.mpr (Set.mem_Ioi.mp hx) (hb hxS)

end Complement

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

/-- On a one-point metric space every set has zero metric BV perimeter. -/
theorem perimeter_eq_zero_of_subsingleton [Subsingleton X] [Nonempty X]
    (ν : Measure X) (B : Set X) : perimeter ν B = 0 := by
  rcases Set.eq_empty_or_nonempty B with hB | ⟨x, hx⟩
  · simpa [hB] using perimeter_empty ν
  · have hB : B = Set.univ := Set.eq_univ_of_forall fun y => by
      rwa [Subsingleton.elim y x]
    simpa [hB] using perimeter_univ ν

section SubsetRestriction

/-! ### Restriction to a measurable subset

A test restricts to a test on a subset with its induced metric; its slope does not increase
(`Energy.LocalSlope.apply_comp_le_of_isometry`), so for the pulled-back measure
`ν.comap Subtype.val` neither the cost nor the indicator distance increases, and the perimeter of
the trace `Subtype.val ⁻¹' B` is at most that of `B`. -/

/-- The restriction of a test to a subset, with the induced metric. -/
def Test.restrict (f : Test X) (s : Set X) : Test s where
  toFun := fun z => f z
  lipschitz := by
    obtain ⟨K, hK⟩ := f.lipschitz
    exact ⟨K * 1, hK.comp (LipschitzWith.subtype_val s)⟩
  bounded := f.bounded.subset (by
    rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl⟩)
  boundedSupport := by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 f.boundedSupport
    exact Metric.isBounded_iff.2 ⟨C, fun z hz w hw => hC hz hw⟩

theorem cost_restrict_le (ν : Measure X) {s : Set X} (hs : MeasurableSet s) (f : Test X) :
    cost (ν.comap Subtype.val) (f.restrict s) ≤ cost ν f := by
  unfold cost
  calc ∫⁻ z, Energy.LocalSlope.apply (f.restrict s) z ∂(ν.comap Subtype.val)
      ≤ ∫⁻ z : s, Energy.LocalSlope.apply f z ∂(ν.comap Subtype.val) :=
        lintegral_mono fun z => Energy.LocalSlope.apply_comp_le_of_isometry isometry_subtype_coe f z
    _ = ∫⁻ x in s, Energy.LocalSlope.apply f x ∂ν := lintegral_subtype_comap hs _
    _ ≤ ∫⁻ x, Energy.LocalSlope.apply f x ∂ν := setLIntegral_le_lintegral _ _

theorem indicatorDistance_restrict_le (ν : Measure X) {s : Set X} (hs : MeasurableSet s)
    (f : Test X) (B : Set X) :
    indicatorDistance (ν.comap Subtype.val) (f.restrict s) (Subtype.val ⁻¹' B) ≤
      indicatorDistance ν f B := by
  unfold indicatorDistance
  have hpt : ∀ z : s, ‖(f.restrict s) z - (Subtype.val ⁻¹' B).indicator (1 : s → ℝ) z‖ₑ =
      ‖f z - B.indicator (1 : X → ℝ) z‖ₑ := fun z => by
    by_cases hz : (z : X) ∈ B
    · rw [Set.indicator_of_mem (show z ∈ Subtype.val ⁻¹' B from hz), Set.indicator_of_mem hz]
      rfl
    · rw [Set.indicator_of_notMem (show z ∉ Subtype.val ⁻¹' B from hz),
        Set.indicator_of_notMem hz]
      rfl
  calc ∫⁻ z, ‖(f.restrict s) z - (Subtype.val ⁻¹' B).indicator (1 : s → ℝ) z‖ₑ
        ∂(ν.comap Subtype.val)
      = ∫⁻ z : s, ‖f z - B.indicator (1 : X → ℝ) z‖ₑ ∂(ν.comap Subtype.val) := lintegral_congr hpt
    _ = ∫⁻ x in s, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν :=
        lintegral_subtype_comap hs (fun x => ‖f x - B.indicator (1 : X → ℝ) x‖ₑ)
    _ ≤ ∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν := setLIntegral_le_lintegral _ _

/-- The restriction of an actual approximating sequence of `B` approximates the trace of `B`. -/
def ApproximatingSequence.restrict {ν : Measure X} {B : Set X} {s : Set X}
    (hs : MeasurableSet s) (g : ApproximatingSequence ν B) :
    ApproximatingSequence (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) :=
  ⟨fun n => (g.1 n).restrict s,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds g.2 (fun _ => zero_le)
      fun n => indicatorDistance_restrict_le ν hs (g.1 n) B⟩

/-- Restriction to a measurable subset does not increase the perimeter. An empty ambient
approximation class gives `⊤` on the right. -/
theorem perimeter_comap_subtype_le (ν : Measure X) {s : Set X} (hs : MeasurableSet s)
    (B : Set X) :
    perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) ≤ perimeter ν B := by
  show _ ≤ ⨅ g : ApproximatingSequence ν B, liminf (fun n => cost ν (g.1 n)) atTop
  refine le_iInf fun g => ?_
  calc perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B)
      ≤ liminf (fun n => cost (ν.comap (Subtype.val : s → X)) ((g.restrict hs).1 n)) atTop :=
        perimeter_le_sequence _ _ _
    _ ≤ liminf (fun n => cost ν (g.1 n)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => cost_restrict_le ν hs (g.1 n))

/-- Reverse comparison under a nonexpansive retraction onto a full-mass measurable subset: for an
actual approximating sequence of the trace, the composed functions `g n ∘ r` are globally
Lipschitz (in general without bounded support, so not tests); full mass moves their `L¹` errors
and slope integrals to the subset, where they are the trace errors and at most the trace costs,
and the finite-measure Lipschitz bridge bounds the perimeter. An empty trace class gives `⊤`. -/
theorem perimeter_le_comap_subtype_of_retraction (ν : Measure X) [IsFiniteMeasure ν]
    {s : Set X} (hs : MeasurableSet s) (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r)
    (hrs : ∀ z : s, r z = z) (B : Set X) :
    perimeter ν B ≤ perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) := by
  have hres : ν.restrict s = ν := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hfull)
  have hmove : ∀ h : X → ENNReal,
      ∫⁻ x, h x ∂ν = ∫⁻ z : s, h z ∂(ν.comap (Subtype.val : s → X)) := fun h => by
    rw [lintegral_subtype_comap hs h, hres]
  show _ ≤ ⨅ g : ApproximatingSequence (ν.comap (Subtype.val : s → X))
      ((Subtype.val : s → X) ⁻¹' B),
    liminf (fun n => cost (ν.comap (Subtype.val : s → X)) (g.1 n)) atTop
  refine le_iInf fun g => ?_
  have hF : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (fun x => g.1 n (r x)) := fun n => by
    obtain ⟨K, hK⟩ := (g.1 n).lipschitz
    exact ⟨K * 1, hK.comp hr⟩
  have hdist : ∀ n, ∫⁻ x, ‖g.1 n (r x) - B.indicator (1 : X → ℝ) x‖ₑ ∂ν =
      indicatorDistance (ν.comap (Subtype.val : s → X)) (g.1 n) ((Subtype.val : s → X) ⁻¹' B) :=
    fun n => by
      rw [hmove (fun x => ‖g.1 n (r x) - B.indicator (1 : X → ℝ) x‖ₑ)]
      unfold indicatorDistance
      refine lintegral_congr fun z => ?_
      simp only [hrs]
      by_cases hz : (z : X) ∈ B
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ Subtype.val ⁻¹' B from hz)]
        rfl
      · rw [Set.indicator_of_notMem hz,
          Set.indicator_of_notMem (show z ∉ Subtype.val ⁻¹' B from hz)]
  have hcost : ∀ n, ∫⁻ x, Energy.LocalSlope.apply (fun x => g.1 n (r x)) x ∂ν ≤
      cost (ν.comap (Subtype.val : s → X)) (g.1 n) := fun n => by
    rw [hmove (fun x => Energy.LocalSlope.apply (fun x => g.1 n (r x)) x)]
    unfold cost
    refine lintegral_mono fun z => ?_
    have h := Energy.LocalSlope.apply_comp_le_of_lipschitzWith_one hr (g.1 n) (z : X)
    rw [hrs] at h
    exact h
  calc perimeter ν B
      ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (fun x => g.1 n (r x)) x ∂ν) atTop :=
        perimeter_le_liminf_of_lipschitz ν hF ((tendsto_congr hdist).2 g.2)
    _ ≤ liminf (fun n => cost (ν.comap (Subtype.val : s → X)) (g.1 n)) atTop :=
        liminf_le_liminf (Eventually.of_forall hcost)

/-- Perimeter equality under a nonexpansive retraction onto a full-mass measurable subset. -/
theorem perimeter_eq_comap_subtype_of_retraction (ν : Measure X) [IsFiniteMeasure ν]
    {s : Set X} (hs : MeasurableSet s) (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r)
    (hrs : ∀ z : s, r z = z) (B : Set X) :
    perimeter ν B = perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) :=
  le_antisymm (perimeter_le_comap_subtype_of_retraction ν hs hfull hr hrs B)
    (perimeter_comap_subtype_le ν hs B)

end SubsetRestriction

section ClosedSupport

variable [SecondCountableTopology X]

/-- The actual law on its closed measure support, with the induced metric. -/
def closedSupportLaw (ν : ProbabilityMeasure X) : ProbabilityMeasure (ν : Measure X).support := by
  letI : IsProbabilityMeasure
      (Measure.comap (Subtype.val : (ν : Measure X).support → X) (ν : Measure X)) := by
    refine ⟨?_⟩
    rw [comap_subtype_coe_apply (ν : Measure X).isClosed_support.measurableSet]
    simp only [Set.image_univ, Subtype.range_coe_subtype]
    change (ν : Measure X) (ν : Measure X).support = 1
    have hdiff : (Set.univ : Set X) \ (ν : Measure X).support =
        (ν : Measure X).supportᶜ := by ext x; simp
    rw [measure_eq_measure_of_null_sdiff (Set.subset_univ _)
      (by rw [hdiff]; exact Measure.measure_compl_support)]
    exact measure_univ
  exact ⟨Measure.comap Subtype.val (ν : Measure X), inferInstance⟩

/-- Set masses for the restricted law are measured by the original law on the
corresponding set of points in the closed support. -/
theorem closedSupportLaw_apply (ν : ProbabilityMeasure X)
    (B : Set (ν : Measure X).support) :
    (closedSupportLaw ν : Measure (ν : Measure X).support) B =
      (ν : Measure X) (Subtype.val '' B) := by
  change Measure.comap Subtype.val (ν : Measure X) B = _
  exact comap_subtype_coe_apply (ν : Measure X).isClosed_support.measurableSet _ _

/-- The trace of a set on the closed support has the mass of the set: the support carries all
mass. -/
theorem closedSupportLaw_preimage (ν : ProbabilityMeasure X) (B : Set X) :
    (closedSupportLaw ν : Measure (ν : Measure X).support) (Subtype.val ⁻¹' B) =
      (ν : Measure X) B := by
  rw [closedSupportLaw_apply, Subtype.image_preimage_coe, Set.inter_comm,
    measure_inter_conull Measure.measure_compl_support]

/-- Complement symmetry on the closed support of a probability law, whose carrier is in
general neither finite nor bounded. -/
theorem perimeter_compl_closedSupportLaw (ν : ProbabilityMeasure X)
    (B : Set (ν : Measure X).support) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) Bᶜ =
      perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) B :=
  perimeter_compl_of_isFiniteMeasure _ B

/-- Restriction to the closed measure support does not increase the metric BV perimeter. -/
theorem perimeter_closedSupportLaw_le (ν : ProbabilityMeasure X) (B : Set X) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) (Subtype.val ⁻¹' B) ≤
      perimeter (ν : Measure X) B :=
  perimeter_comap_subtype_le _ (ν : Measure X).isClosed_support.measurableSet B

end ClosedSupport

/-! ### Scaling by a nonnegative real scalar, the zero measure and normalization

Costs and indicator distances are linear in the measure; the approximating class of `c • ν` is
the class of `ν` for `c ≠ 0`; hence `perimeter (c • ν) B = c * perimeter ν B` for every nonzero
`c : ℝ≥0`, including the empty class (`⊤`).  The zero measure has zero perimeter for every set.
A finite nonzero measure is `c • ν` with `c : ℝ≥0` nonzero and `ν` a probability measure
(`exists_probability_smul`); scalars are always finite reals, so `⊤ - ⊤` never enters.
-/

section Scaling

/-- `liminf` commutes with multiplication by a finite constant on `ℝ≥0∞` (a local tool). -/
private theorem liminf_coe_mul {ι : Type*} {l : Filter ι} [l.NeBot] (c : ℝ≥0) (u : ι → ℝ≥0∞) :
    liminf (fun i => (c : ℝ≥0∞) * u i) l = c * liminf u l := by
  have hmono : Monotone fun x : ℝ≥0∞ => (c : ℝ≥0∞) * x := fun _ _ h => mul_le_mul' le_rfl h
  have h := hmono.map_liminf_of_continuousAt (F := l) u
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).continuousAt
  simpa [Function.comp_def] using h.symm

theorem cost_smul (c : ℝ≥0) (ν : Measure X) (f : Test X) : cost (c • ν) f = c * cost ν f := by
  simp only [cost, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

theorem indicatorDistance_smul (c : ℝ≥0) (ν : Measure X) (f : Test X) (B : Set X) :
    indicatorDistance (c • ν) f B = c * indicatorDistance ν f B := by
  simp only [indicatorDistance, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

@[simp] theorem cost_zero_measure (f : Test X) : cost (0 : Measure X) f = 0 := by
  simp [cost]

@[simp] theorem indicatorDistance_zero_measure (f : Test X) (B : Set X) :
    indicatorDistance (0 : Measure X) f B = 0 := by
  simp [indicatorDistance]

/-- An approximating sequence for `ν` approximates for `c • ν` (any `c : ℝ≥0`). -/
def ApproximatingSequence.smul (c : ℝ≥0) {ν : Measure X} {B : Set X}
    (f : ApproximatingSequence ν B) : ApproximatingSequence (c • ν) B :=
  ⟨f.1, by
    have h := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) f.2 (Or.inr ENNReal.coe_ne_top)
    simpa [indicatorDistance_smul] using h⟩

/-- An approximating sequence for `c • ν` with `c ≠ 0` approximates for `ν`. -/
def ApproximatingSequence.smulInv {c : ℝ≥0} (hc : c ≠ 0) {ν : Measure X} {B : Set X}
    (f : ApproximatingSequence (c • ν) B) : ApproximatingSequence ν B :=
  ⟨f.1, by
    have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
    have h := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)⁻¹) f.2
      (Or.inr (ENNReal.inv_ne_top.2 hc'))
    simp only [indicatorDistance_smul, ← mul_assoc, ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top,
      one_mul, mul_zero] at h
    exact h⟩

theorem perimeter_smul_le (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure X) (B : Set X) :
    perimeter (c • ν) B ≤ c * perimeter ν B := by
  unfold perimeter
  rw [ENNReal.mul_iInf' (fun h => absurd h ENNReal.coe_ne_top)
    (fun h => absurd (ENNReal.coe_eq_zero.1 h) hc)]
  refine le_iInf fun f => (iInf_le _ (f.smul c)).trans (le_of_eq ?_)
  simp only [ApproximatingSequence.smul, cost_smul]
  exact liminf_coe_mul c _

/-- **Perimeter scaling**: `perimeter (c • ν) B = c * perimeter ν B` for every nonzero `c : ℝ≥0`
and every set `B` (also when the class is empty and both sides are `⊤`). -/
theorem perimeter_smul (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure X) (B : Set X) :
    perimeter (c • ν) B = c * perimeter ν B := by
  refine le_antisymm (perimeter_smul_le c hc ν B) ?_
  have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  have h := perimeter_smul_le c⁻¹ (inv_ne_zero hc) (c • ν) B
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  calc (c : ℝ≥0∞) * perimeter ν B ≤ c * ((c⁻¹ : ℝ≥0) * perimeter (c • ν) B) :=
        mul_le_mul' le_rfl h
    _ = perimeter (c • ν) B := by
        rw [← mul_assoc, ENNReal.coe_inv hc, ENNReal.mul_inv_cancel hc' ENNReal.coe_ne_top, one_mul]

/-- The zero measure has zero perimeter for every set: the zero test approximates at zero cost. -/
theorem perimeter_zero_measure (B : Set X) : perimeter (0 : Measure X) B = 0 := by
  refine le_antisymm ?_ bot_le
  have h := perimeter_le_sequence (0 : Measure X) B ⟨fun _ => Test.zero, by simp⟩
  simpa using h

omit [MetricSpace X] [BorelSpace X] in
/-- **Normalization**: a finite nonzero measure is a nonzero nonnegative real multiple of a
probability measure. -/
theorem exists_probability_smul (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    ∃ (c : ℝ≥0) (ν : ProbabilityMeasure X), c ≠ 0 ∧ μ = c • (ν : Measure X) := by
  have : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hμ (Measure.eq_zero_of_isEmpty μ)
  set μ' : FiniteMeasure X := ⟨μ, inferInstance⟩ with hμ'
  have hne : μ' ≠ 0 := by
    intro h
    apply hμ
    have := congrArg FiniteMeasure.toMeasure h
    simpa [hμ'] using this
  refine ⟨μ'.mass, μ'.normalize, (FiniteMeasure.mass_nonzero_iff μ').2 hne, ?_⟩
  have h := congrArg FiniteMeasure.toMeasure (FiniteMeasure.self_eq_mass_smul_normalize μ')
  rw [FiniteMeasure.toMeasure_smul] at h
  exact h

end Scaling

end FunctionalInequalities.KLS.MetricBV

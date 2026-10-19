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
# Metric BV tests, relaxation, recovery and elementary bounds
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


end FunctionalInequalities.KLS.MetricBV

import FunctionalInequalities.Energy.LocalSlope.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Bornology.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Fintype.EquivFin

/-!
# Metric BV perimeter

The test class and sequential relaxation use the metric and the actual measure on the
space. In particular this is distinct from weighted smooth-domain relative perimeter.
The local slope is `Energy.LocalSlope.apply`, which is zero at isolated points.
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

theorem perimeter_empty (ν : Measure X) : perimeter ν (∅ : Set X) = 0 := by
  have h : perimeter ν ∅ ≤ liminf (fun _ : ℕ => cost ν (Test.const 0)) atTop :=
    perimeter_le_sequence ν ∅ ⟨fun _ => Test.const 0, by
      simp [indicatorDistance, Test.const]⟩
  simpa [cost_const] using (le_antisymm (h.trans_eq (by simp [cost_const])) bot_le)

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

/-- On a one-point metric space every set has zero metric BV perimeter. -/
theorem perimeter_eq_zero_of_subsingleton [Subsingleton X] [Nonempty X]
    (ν : Measure X) (B : Set X) : perimeter ν B = 0 := by
  rcases Set.eq_empty_or_nonempty B with hB | ⟨x, hx⟩
  · simpa [hB] using perimeter_empty ν
  · have hB : B = Set.univ := Set.eq_univ_of_forall fun y => by
      rwa [Subsingleton.elim y x]
    simpa [hB] using perimeter_univ ν

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

end ClosedSupport

end FunctionalInequalities.KLS.MetricBV

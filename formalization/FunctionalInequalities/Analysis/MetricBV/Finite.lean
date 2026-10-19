import FunctionalInequalities.Analysis.MetricBV.Basic

/-!
# Metric BV on finite and singleton metric spaces
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable [BorelSpace X]
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
/-- On a one-point metric space every set has zero metric BV perimeter. -/
theorem perimeter_eq_zero_of_subsingleton [Subsingleton X] [Nonempty X]
    (ν : Measure X) (B : Set X) : perimeter ν B = 0 := by
  rcases Set.eq_empty_or_nonempty B with hB | ⟨x, hx⟩
  · simpa [hB] using perimeter_empty ν
  · have hB : B = Set.univ := Set.eq_univ_of_forall fun y => by
      rwa [Subsingleton.elim y x]
    simpa [hB] using perimeter_univ ν


end FunctionalInequalities.KLS.MetricBV

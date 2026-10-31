module

public import FunctionalInequalities.Analysis.MetricBV.Basic
public import FunctionalInequalities.Analysis.MetricBV.Finite
public import FunctionalInequalities.Analysis.MetricBV.Approximation
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent full-signature clients for the recovery sequence of the metric BV perimeter:
for every Borel measure and every set of finite perimeter, an actual approximating sequence whose
costs converge to the perimeter in the `ENNReal` topology, with the explicit error and threshold
bounds. Boundary cases: an empty carrier, zero perimeter (the empty set for Lebesgue measure on
`ℝ`, the whole line for the standard Gaussian law), and infinite perimeter (the whole line for
Lebesgue measure), where the hypothesis fails and no recovery sequence is claimed. This is not a
Minkowski recovery or lower semicontinuity statement. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace MetricBVRecoverySequenceAudit

open FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem recoverySequenceExists (ν : Measure X) (B : Set X) (hB : perimeter ν B < ⊤) :
    ∃ g : ApproximatingSequence ν B,
      Tendsto (fun n => cost ν (g.1 n)) atTop (𝓝 (perimeter ν B)) := by
  exact exists_recoverySequence ν B hB

/-- The explicit sequence with arbitrary positive vanishing errors and threshold excesses: its
terms satisfy both bounds, its distances vanish and its costs converge to the perimeter. -/
theorem explicitSequence {ν : Measure X} {B : Set X} (hB : perimeter ν B < ⊤)
    {ε η : ℕ → ENNReal} (hε0 : ∀ n, 0 < ε n) (hη0 : ∀ n, 0 < η n)
    (hε : Tendsto ε atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0)) :
    (∀ n, indicatorDistance ν ((recoverySequence hB hε0 hη0 hε).1 n) B < ε n) ∧
      (∀ n, cost ν ((recoverySequence hB hε0 hη0 hε).1 n) < perimeter ν B + η n) ∧
      Tendsto (fun n => indicatorDistance ν ((recoverySequence hB hε0 hη0 hε).1 n) B) atTop
        (𝓝 0) ∧
      Tendsto (fun n => cost ν ((recoverySequence hB hε0 hη0 hε).1 n)) atTop
        (𝓝 (perimeter ν B)) := by
  exact ⟨indicatorDistance_recoverySequence_lt hB hε0 hη0 hε,
    cost_recoverySequence_lt hB hε0 hη0 hε, (recoverySequence hB hε0 hη0 hε).2,
    tendsto_cost_recoverySequence hB hε0 hη0 hε hη⟩

/-- The limsup criterion for an arbitrary approximating sequence, with no finiteness. -/
theorem limsupCriterion {ν : Measure X} {B : Set X} (s : ApproximatingSequence ν B)
    (h : limsup (fun n => cost ν (s.1 n)) atTop ≤ perimeter ν B) :
    Tendsto (fun n => cost ν (s.1 n)) atTop (𝓝 (perimeter ν B)) := by
  exact tendsto_cost_of_limsup_le s h

/-- Independent consequence: the limit of the costs is the perimeter, and the liminf equals it. -/
theorem liminfEq (ν : Measure X) (B : Set X) (hB : perimeter ν B < ⊤) :
    ∃ g : ApproximatingSequence ν B, liminf (fun n => cost ν (g.1 n)) atTop = perimeter ν B := by
  obtain ⟨g, hg⟩ := exists_recoverySequence ν B hB
  exact ⟨g, hg.liminf_eq⟩

/-- Empty carrier: every set is empty, has zero perimeter, and the costs tend to zero. -/
theorem emptyCarrier (ν : Measure Empty) (B : Set Empty) :
    ∃ g : ApproximatingSequence ν B, Tendsto (fun n => cost ν (g.1 n)) atTop (𝓝 0) := by
  have hB : B = ∅ := Set.eq_empty_of_isEmpty B
  subst hB
  have h := exists_recoverySequence ν ∅ (by rw [perimeter_empty]; exact ENNReal.zero_lt_top)
  rwa [perimeter_empty] at h

/-- Zero perimeter for an infinite measure: the empty set under Lebesgue measure on `ℝ`. -/
theorem lebesgueEmpty :
    ∃ g : ApproximatingSequence (volume : Measure ℝ) ∅,
      Tendsto (fun n => cost (volume : Measure ℝ) (g.1 n)) atTop (𝓝 0) := by
  have h := exists_recoverySequence (volume : Measure ℝ) ∅
    (by rw [perimeter_empty]; exact ENNReal.zero_lt_top)
  rwa [perimeter_empty] at h

/-- Zero perimeter of the whole line for the standard Gaussian law, via the globally Lipschitz
bridge applied to the constant one. -/
theorem gaussianWholeLine :
    ∃ g : ApproximatingSequence (ProbabilityTheory.gaussianReal 0 1) Set.univ,
      Tendsto (fun n => cost (ProbabilityTheory.gaussianReal 0 1) (g.1 n)) atTop (𝓝 0) := by
  have h := perimeter_le_liminf_of_lipschitz (ProbabilityTheory.gaussianReal 0 1)
    (B := Set.univ) (f := fun _ _ => (1 : ℝ)) (fun _ => ⟨0, LipschitzWith.const 1⟩)
    (by simp)
  simp only [FunctionalInequalities.Energy.LocalSlope.apply_const, lintegral_zero,
    Filter.liminf_const] at h
  have h0 : perimeter (ProbabilityTheory.gaussianReal 0 1) Set.univ = 0 := le_antisymm h bot_le
  have hr := exists_recoverySequence (ProbabilityTheory.gaussianReal 0 1) Set.univ
    (h0 ▸ ENNReal.zero_lt_top)
  rwa [h0] at hr

/-- Infinite perimeter: the whole line under Lebesgue measure has perimeter `⊤`, so it fails the
finiteness hypothesis; no recovery sequence is claimed there. -/
theorem lebesgueWholeLineInfinite :
    perimeter (volume : Measure ℝ) Set.univ = ⊤ ∧
      ¬ perimeter (volume : Measure ℝ) Set.univ < ⊤ := by
  have htop : perimeter (volume : Measure ℝ) Set.univ = ⊤ := by
    refine perimeter_univ_eq_top_of_forall_isBounded (volume : Measure ℝ) fun S hS => ?_
    obtain ⟨b, hb⟩ := hS.bddAbove
    refine top_le_iff.mp ((Real.volume_Ioi (a := b)).symm.le.trans (measure_mono fun x hx => ?_))
    exact fun hxS => not_le.mpr (Set.mem_Ioi.mp hx) (hb hxS)
  exact ⟨htop, by rw [htop]; exact lt_irrefl _⟩

#print axioms recoverySequenceExists
#print axioms explicitSequence
#print axioms limsupCriterion
#print axioms liminfEq
#print axioms emptyCarrier
#print axioms lebesgueEmpty
#print axioms gaussianWholeLine
#print axioms lebesgueWholeLineInfinite

end MetricBVRecoverySequenceAudit

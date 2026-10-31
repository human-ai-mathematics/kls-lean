module

public import FunctionalInequalities.Analysis.Whitney.FirstOrderJet
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Strict audit client for the first-order jet condition (necessity half of Whitney extension)

Independent client of `Analysis/Whitney/FirstOrderJet.lean`.

**The `#check` below is not a proof.** It pins the statement text of obligation `L6` of
`research/audits/Coarea/WeightedRouteStatements.lean`, the compact `C¹` Whitney extension of a
compatible first-order jet, and no theorem in this client proves that sufficiency direction. That
direction has source `Analysis/Whitney/Construction.lean`; this client concerns necessity.  What is
proved is the converse, `necessity`: a globally `C¹` realization of the jet forces the uniform
first-order remainder estimate assumed by the extension.  Together with the extension theorem this
makes the estimate a characterization; on its own it establishes only that the extension's
hypothesis is the right one and cannot be weakened to something the conclusion would not imply.

`trivial_jet` instantiates it at the jet of the realizing function itself, and `concrete`
at a square on a closed ball, so the statement is not vacuous.
-/

@[expose] public section

noncomputable section

open Metric Set MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FirstOrderJetAudit

/-! ### The sufficiency contract, recorded without a proof in this client -/

-- The statement text of obligation `L6` of `research/audits/Coarea/WeightedRouteStatements.lean`.
-- This is a type check only; it does not prove the extension.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ},
    IsCompact S → ContinuousOn f S → ContinuousOn F S →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) →
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ Set.EqOn v f S ∧
      ∀ x ∈ S, fderiv ℝ v x = F x)

/-! ### The necessity half, proved -/

/-- The converse of the Whitney extension theorem: a `C¹` realization forces the uniform
first-order remainder estimate. -/
theorem necessity : ∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ},
    IsCompact S → ∀ {v : V → ℝ}, ContDiff ℝ 1 v → Set.EqOn v f S →
    (∀ x ∈ S, fderiv ℝ v x = F x) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro V _ _ _ S f F hS v hv hvf hvF
  exact uniform_jet_remainder_of_contDiff hS hv hvf hvF

section Consumers

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- At the jet of the realizing function itself: every `C¹` function satisfies the estimate on
every compact set. -/
theorem trivial_jet {S : Set V} (hS : IsCompact S) {v : V → ℝ} (hv : ContDiff ℝ 1 v) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖v y - v x - fderiv ℝ v x (y - x)‖ ≤ ε * ‖y - x‖ :=
  uniform_jet_remainder_of_contDiff hS hv (fun _ _ => rfl) (fun _ _ => rfl)

end Consumers

/-- A concrete instance on the line: the square on a closed ball. -/
theorem concrete (r : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Metric.closedBall (0 : ℝ) r, ∀ y ∈ Metric.closedBall (0 : ℝ) r, ‖y - x‖ < δ →
        ‖y ^ 2 - x ^ 2 - fderiv ℝ (fun z : ℝ => z ^ 2) x (y - x)‖ ≤ ε * ‖y - x‖ := by
  have hv : ContDiff ℝ 1 (fun z : ℝ => z ^ 2) := contDiff_id.pow 2
  exact uniform_jet_remainder_of_contDiff (isCompact_closedBall 0 r) hv
    (fun _ _ => rfl) (fun _ _ => rfl)

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.Analysis.uniform_jet_remainder_of_contDiff
#print axioms FirstOrderJetAudit.necessity
#print axioms FirstOrderJetAudit.trivial_jet
#print axioms FirstOrderJetAudit.concrete

end FirstOrderJetAudit

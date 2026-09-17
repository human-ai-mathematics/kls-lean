import FunctionalInequalities.Analysis.FirstOrderJet
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Strict audit client for the first-order jet condition (necessity half of `L6`)

Independent client of `Analysis/FirstOrderJet.lean`.

**`L6` is NOT proved.**  The `#check` below records its statement text verbatim so that the open
obligation stays pinned, and no theorem in this client proves it.  What is proved is the converse,
`necessity`: a globally `C¹` realization of the jet forces `L6`'s uniform first-order remainder
estimate.  Together with `L6` that would make the estimate a characterization; on its own it
establishes only that `L6`'s hypothesis is the right one and cannot be weakened to something the
conclusion would not imply.

`trivial_jet` instantiates it at the jet of the realizing function itself, and `concrete`
at a square on a closed ball, so the statement is not vacuous.
-/

noncomputable section

open Metric Set MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FirstOrderJetAudit

/-! ### The obligation that remains open -/

-- The statement text of `L6` in `research/decisions/2026-09-15-weighted-coarea-route.md`.
-- This is a type check only: `L6` is NOT proved anywhere in this client or in the library.
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

/-- The converse of `L6`: a `C¹` realization forces the uniform first-order remainder estimate. -/
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
        ‖y ^ 2 - x ^ 2 - fderiv ℝ (fun z : ℝ => z ^ 2) x (y - x)‖ ≤ ε * ‖y - x‖ :=
  by
  have hv : ContDiff ℝ 1 (fun z : ℝ => z ^ 2) := contDiff_id.pow 2
  exact uniform_jet_remainder_of_contDiff (isCompact_closedBall 0 r) hv
    (fun _ _ => rfl) (fun _ _ => rfl)

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.Analysis.uniform_jet_remainder_of_contDiff
#print axioms FirstOrderJetAudit.necessity
#print axioms FirstOrderJetAudit.trivial_jet
#print axioms FirstOrderJetAudit.concrete

end FirstOrderJetAudit

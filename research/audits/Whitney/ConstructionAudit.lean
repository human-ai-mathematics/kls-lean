import FunctionalInequalities.Analysis.Whitney.Construction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Obligation `L6` of `research/audits/Coarea/WeightedRouteStatements.lean`, the compact `C¹`
Whitney extension of a compatible first-order jet, with all its original assumptions, proved by
the quantitative construction. -/

noncomputable section
open Set Metric FunctionalInequalities.Analysis
open scoped ContDiff
namespace WhitneyConstructionAudit

/-- The original Whitney extension proposition, with every instance and assumption retained. -/
theorem original_L6 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ},
    IsCompact S → ContinuousOn f S → ContinuousOn F S →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) →
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ Set.EqOn v f S ∧
      ∀ x ∈ S, fderiv ℝ v x = F x := by
  intro V _ _ _ _ _ _ S f F hS _hf hF hR
  exact WhitneyJet.exists_contDiff_extension hS hF hR

/-- Empty jets use the same public extension theorem. -/
theorem empty_extension (f : ℝ → ℝ) (F : ℝ → ℝ →L[ℝ] ℝ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 1 v ∧ EqOn v f ∅ ∧
      ∀ x ∈ (∅ : Set ℝ), fderiv ℝ v x = F x := by
  apply WhitneyJet.exists_contDiff_extension isCompact_empty (continuousOn_empty F)
  intro ε _
  exact ⟨1, one_pos, by simp⟩

/-- Sparse sets retain arbitrary ambient derivatives, including nonzero ones. -/
theorem singleton_extension {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (c : ℝ) (L : V →L[ℝ] ℝ) :
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ EqOn v (fun _ => c) {0} ∧
      fderiv ℝ v 0 = L := by
  obtain ⟨v, hv, hf, hF⟩ := WhitneyJet.exists_contDiff_extension
    (S := {(0 : V)}) isCompact_singleton (f := fun _ => c)
    (F := fun _ => L) continuousOn_const (by
      intro ε _
      refine ⟨1, one_pos, ?_⟩
      intro x hx y hy _
      simp only [mem_singleton_iff] at hx hy
      simp [hx, hy])
  exact ⟨v, hv, hf, hF 0 (by simp)⟩

theorem zero_dimension :
    ∃ v : EuclideanSpace ℝ (Fin 0) → ℝ, ContDiff ℝ 1 v ∧
      EqOn v (fun _ => (7 : ℝ)) {0} ∧ fderiv ℝ v 0 = 0 :=
  singleton_extension 7 0

/-- An infinite compact domain; both values and derivatives are extended by the construction. -/
theorem square_interval :
    ∃ v : ℝ → ℝ, ContDiff ℝ 1 v ∧ EqOn v (fun x => x ^ 2) (closedBall 0 1) ∧
      ∀ x ∈ closedBall (0 : ℝ) 1, fderiv ℝ v x = fderiv ℝ (fun y : ℝ => y ^ 2) x := by
  have hv : ContDiff ℝ 1 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  exact WhitneyJet.exists_contDiff_extension (isCompact_closedBall 0 1)
    (hv.continuous_fderiv one_ne_zero).continuousOn
    (uniform_jet_remainder_of_contDiff (isCompact_closedBall 0 1) hv
      (fun _ _ => rfl) (fun _ _ => rfl))

#print axioms FunctionalInequalities.Analysis.WhitneyCover.exists_cover
#print axioms FunctionalInequalities.Analysis.WhitneyCover.exists_derivative_bound
#print axioms FunctionalInequalities.Analysis.WhitneyCover.contDiffOn_weight
#print axioms FunctionalInequalities.Analysis.WhitneyCover.sum_weight_eq_one
#print axioms FunctionalInequalities.Analysis.WhitneyCover.exists_weight_derivative_bound
#print axioms FunctionalInequalities.Analysis.WhitneyJet.contDiffOn_candidate
#print axioms FunctionalInequalities.Analysis.WhitneyJet.exists_compl_approx
#print axioms FunctionalInequalities.Analysis.WhitneyJet.exists_contDiff_extension
#print axioms WhitneyConstructionAudit.original_L6
#print axioms WhitneyConstructionAudit.empty_extension
#print axioms WhitneyConstructionAudit.singleton_extension
#print axioms WhitneyConstructionAudit.zero_dimension
#print axioms WhitneyConstructionAudit.square_interval

end WhitneyConstructionAudit

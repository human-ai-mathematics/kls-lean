import FunctionalInequalities.Analysis.Coarea.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Compact jet extraction, the Whitney–Lusin decomposition, the Lipschitz weighted coarea formula
and the second original target (`L6a`, `L7`, `L12` and `T2` of
`research/audits/Coarea/WeightedRouteStatements.lean`), with their complete assumptions, proved as
clients. -/

noncomputable section
open Set Metric MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff
namespace LipschitzCoareaAudit

theorem original_L6a : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
    ∃ S : ℕ → Set V, (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧
      ∀ j, IsCompact (S j) ∧ (∀ x ∈ S j, DifferentiableAt ℝ u x) ∧
        ContinuousOn (fderiv ℝ u) (S j) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ x ∈ S j, ∀ y ∈ S j, ‖y - x‖ < δ →
            ‖u y - u x - fderiv ℝ u x (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro V _ _ _ _ _ _ u K hu
  exact LipschitzJet.exists_compact_jets (volume : Measure V) hu

theorem original_L7 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
    ∃ (S : ℕ → Set V) (v : ℕ → V → ℝ),
      (∀ j, MeasurableSet (S j)) ∧ Pairwise (fun i j ↦ Disjoint (S i) (S j)) ∧
      (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧
      (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ S j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x := by
  intro V _ _ _ _ _ _ u K hu
  exact Analysis.exists_contDiff_pieces hu

theorem original_L12 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {K : ℝ≥0} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ S u K g hu hS hg
  exact KLS.coarea_of_lipschitz hu hS hg

theorem original_T2 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}
    (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  simpa only [setLIntegral_univ, univ_inter] using
    (KLS.coarea_of_lipschitz (S := univ) hu MeasurableSet.univ hg).2

/-- A function which is genuinely not C¹, on an unbounded domain, with arbitrary weights. -/
theorem norm_univ (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ¬ DifferentiableAt ℝ (fun x : ℝ => ‖x‖) 0 ∧
      (∫⁻ x, ‖gradient (fun x : ℝ => ‖x‖) x‖ₑ * g x) =
        ∫⁻ t, ∫⁻ y in {x : ℝ | ‖x‖ = t}, g y ∂(KLS.surfaceMeasure ℝ) := by
  refine ⟨not_differentiableAt_norm_zero ℝ, ?_⟩
  simpa only [setLIntegral_univ, univ_inter] using
    (KLS.coarea_of_lipschitz (S := univ) lipschitzWith_one_norm MeasurableSet.univ hg).2

/-- Infinite weights and constant functions are allowed: all mass is at one exceptional level. -/
theorem constant_top (c : ℝ) :
    (∫⁻ t, ∫⁻ _y in {_x : ℝ | c = t}, (∞ : ℝ≥0∞) ∂(KLS.surfaceMeasure ℝ)) = 0 := by
  have h := (KLS.coarea_of_lipschitz (V := ℝ) (S := univ) (g := fun _ => ∞)
    (LipschitzWith.const c) MeasurableSet.univ measurable_const).2
  simpa [gradient] using h.symm

/-- No positive-dimension hypothesis is hidden in the coarea formula. -/
theorem zero_dimension {u : EuclideanSpace ℝ (Fin 0) → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) {S : Set (EuclideanSpace ℝ (Fin 0))} (hS : MeasurableSet S)
    {g : EuclideanSpace ℝ (Fin 0) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure (EuclideanSpace ℝ (Fin 0))) :=
  (KLS.coarea_of_lipschitz hu hS hg).2

#print axioms FunctionalInequalities.Analysis.LipschitzJet.measurableSet_goodSet
#print axioms FunctionalInequalities.Analysis.LipschitzJet.goodSet_iff
#print axioms FunctionalInequalities.Analysis.LipschitzJet.exists_goodSet
#print axioms FunctionalInequalities.Analysis.LipschitzJet.continuousOn_fderiv
#print axioms FunctionalInequalities.Analysis.LipschitzJet.exists_compact_uniform_cover
#print axioms FunctionalInequalities.Analysis.LipschitzJet.exists_compact_jets
#print axioms FunctionalInequalities.Analysis.exists_contDiff_pieces
#print axioms FunctionalInequalities.KLS.coarea_of_lipschitz
#print axioms LipschitzCoareaAudit.original_L6a
#print axioms LipschitzCoareaAudit.original_L7
#print axioms LipschitzCoareaAudit.original_L12
#print axioms LipschitzCoareaAudit.original_T2
#print axioms LipschitzCoareaAudit.norm_univ
#print axioms LipschitzCoareaAudit.constant_top
#print axioms LipschitzCoareaAudit.zero_dimension

end LipschitzCoareaAudit

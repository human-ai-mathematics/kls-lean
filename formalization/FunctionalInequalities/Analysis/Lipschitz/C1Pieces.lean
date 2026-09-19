import FunctionalInequalities.Analysis.Lipschitz.Jet
import FunctionalInequalities.Analysis.Whitney.Construction
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Exact C¹ pieces of a Lipschitz function
L6a extracts compact jets; L6 extends each jet. Difference sets give a disjoint measurable
partition of a conull set. Both values and ambient derivatives are preserved pointwise. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff NNReal

namespace FunctionalInequalities.Analysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **L7**: exact C¹ representatives on countably many disjoint measurable pieces,
covering almost every point, with the original ambient derivative on each piece. -/
theorem exists_contDiff_pieces {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∃ (S : ℕ → Set V) (v : ℕ → V → ℝ),
      (∀ j, MeasurableSet (S j)) ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧ (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ S j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x := by
  classical
  obtain ⟨C, hCnull, hC⟩ := LipschitzJet.exists_compact_jets (volume : Measure V) hu
  choose v hv hval hder using fun j =>
    WhitneyJet.exists_contDiff_extension (hC j).1 (hC j).2.2.1 (hC j).2.2.2
  refine ⟨disjointed C, v, MeasurableSet.disjointed (fun j => (hC j).1.measurableSet),
    disjoint_disjointed C, ?_, hv, ?_⟩
  · simpa only [iUnion_disjointed] using hCnull
  · intro j x hx
    have hxC := disjointed_subset C j hx
    exact ⟨(hC j).2.1 x hxC, hval j hxC, hder j x hxC⟩

end FunctionalInequalities.Analysis

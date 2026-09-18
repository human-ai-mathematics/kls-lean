import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # A countable common refinement of finitely many countable partitions

Bookkeeping layer of the componentwise route to the vector `C¹` pieces
(`Analysis/Lipschitz/VectorPieces.lean`).  Each coordinate of a Lipschitz map into an
`m`-dimensional target carries its own countable disjoint measurable partition of a conull set,
produced by the scalar `exists_contDiff_pieces`; the vector statement needs a **single** partition
on which all `m` coordinates are good at once.

The refinement is indexed by `ℕ` again: `Fin m → ℕ` is countable, so it injects into `ℕ`, and the
piece labelled `n` is the intersection `⋂ i, S i (f i)` of the unique tuple `f` with label `n`, or
empty when `n` is not a label.  Two distinct labels differ in some coordinate, where the two
original pieces are already disjoint, and a point outside the refinement misses some coordinate's
union, so the complement lies in the union of the `m` null complements.

No analysis: `volume` enters only through countable subadditivity of a null family.
-/

noncomputable section

open MeasureTheory Set

namespace FunctionalInequalities.Analysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **`V3`: finitely many countable measurable partitions of conull sets have a countable
measurable common refinement.**  Each piece of the refinement sits inside one piece of every given
partition, the refinement is again disjoint and measurable, and its complement is still null.

`m = 0` is allowed: the refinement is then the trivial partition `{univ}`. -/
theorem exists_common_refinement (m : ℕ) (S : Fin m → ℕ → Set V)
    (hSm : ∀ i j, MeasurableSet (S i j))
    (hSd : ∀ i, Pairwise (fun a b => Disjoint (S i a) (S i b)))
    (hSnull : ∀ i, (volume : Measure V) (⋃ j, S i j)ᶜ = 0) :
    ∃ T : ℕ → Set V, (∀ n, MeasurableSet (T n)) ∧
      Pairwise (fun a b => Disjoint (T a) (T b)) ∧
      (volume : Measure V) (⋃ n, T n)ᶜ = 0 ∧
      ∀ n, ∃ f : Fin m → ℕ, T n ⊆ ⋂ i, S i (f i) := by
  classical
  obtain ⟨c, hc⟩ := exists_injective_nat (Fin m → ℕ)
  refine ⟨fun n => ⋃ f ∈ {f : Fin m → ℕ | c f = n}, ⋂ i, S i (f i), fun n => ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.biUnion (Set.to_countable _) fun f _ =>
      MeasurableSet.iInter fun i => hSm i (f i)
  · intro a b hab
    rw [Set.disjoint_left]
    rintro x hxa hxb
    obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hxa
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 hxb
    have hfg : f ≠ g := by
      rintro rfl
      exact hab (hf.symm.trans hg)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hfg
    exact Set.disjoint_left.1 (hSd i hi) (Set.mem_iInter.1 hxf i) (Set.mem_iInter.1 hxg i)
  · refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null (fun i => hSnull i))
    by_contra hxn
    simp only [Set.mem_iUnion, not_exists] at hxn
    have hall : ∀ i, ∃ j, x ∈ S i j := by
      intro i
      have h := hxn i
      rw [Set.mem_compl_iff, not_not] at h
      exact Set.mem_iUnion.1 h
    choose f hf using hall
    exact hx (Set.mem_iUnion.2 ⟨c f, Set.mem_iUnion₂.2 ⟨f, rfl, Set.mem_iInter.2 hf⟩⟩)
  · intro n
    by_cases h : ∃ f : Fin m → ℕ, c f = n
    · obtain ⟨f, hf⟩ := h
      refine ⟨f, fun x hx => ?_⟩
      obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 hx
      exact hc (hg.trans hf.symm) ▸ hxg
    · refine ⟨fun _ => 0, fun x hx => ?_⟩
      obtain ⟨g, hg, -⟩ := Set.mem_iUnion₂.1 hx
      exact absurd ⟨g, hg⟩ h

end FunctionalInequalities.Analysis

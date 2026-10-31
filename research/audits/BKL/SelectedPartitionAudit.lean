module

public import FunctionalInequalities.Analysis.IteratedDerivative.Bilinear

/-! Audit clients for `selected_mask_partition` (`Analysis/IteratedDerivative/Bilinear.lean`):
the actual zero-slot model has no singleton selection, a one-slot selection of four identical
vectors is an actual singleton indicator, and an indexed singleton indicator selects one vector
despite the repeated data. The producer is not duplicated here. No cumulant, stochastic or energy
statement is involved. -/

@[expose] public section

namespace Stage1SelectedClients
open FunctionalInequalities.Analysis

/-- A singleton cannot occur in the actual zero-slot model, by length conservation. -/
theorem zero_slots_no_singleton :
    ¬ ∃ q : Fin 0 → Bool, (selected (fun i : Fin 0 => (Fin.elim0 i : ℝ)) q).length = 1 := by
  rintro ⟨q, hq⟩
  have hlen := (selected_mask_partition (fun i : Fin 0 => (Fin.elim0 i : ℝ)) q).1
  omega

/-- With four identical vectors, a one-slot selection still identifies an actual singleton mask. -/
theorem repeated_vectors_singleton_mask (q : Fin 4 → Bool)
    (hq : (selected (fun _ : Fin 4 => (7 : ℝ)) q).length = 1) :
    ∃ i : Fin 4, q = fun j => decide (j = i) :=
  (selected_mask_partition (fun _ : Fin 4 => (7 : ℝ)) q).2.2.2 hq

/-- An indexed singleton remains one vector despite the repeated data. -/
theorem repeated_vectors_selected_singleton (i : Fin 4) :
    selected (fun _ : Fin 4 => (7 : ℝ)) (fun j => decide (j = i)) = [7] :=
  (selected_mask_partition (fun _ : Fin 4 => (7 : ℝ)) (fun _ => false)).2.2.1 i

#print axioms zero_slots_no_singleton
#print axioms repeated_vectors_singleton_mask
#print axioms repeated_vectors_selected_singleton
#print axioms FunctionalInequalities.Analysis.selected_mask_partition
end Stage1SelectedClients

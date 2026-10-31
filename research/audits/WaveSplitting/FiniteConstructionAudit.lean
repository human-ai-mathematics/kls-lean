module

public import FunctionalInequalities.Analysis.WaveSplitting.Basic

/-! Independent clients for the explicit finite construction. No residual estimate or
form-range density is asserted. Empty coordinates and zero initial data are checked explicitly. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingAudit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A complete finite coordinate sweep, with arbitrary compact smooth initial velocity,
has jointly smooth cells and a common compact support on a finite grid. -/
theorem finite_construction (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (h : E → ℝ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (N : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (∀ k, JointSmooth (cell a b (List.finRange d) (L / N) (initial h) k)) ∧
    ∃ K : Set E, IsCompact K ∧ ∀ k < N, ∀ θ ∈ Set.Icc 0 (L / N), ∀ x ∉ K,
      (cell a b (List.finRange d) (L / N) (initial h) k θ).u x = 0 ∧
      (cell a b (List.finRange d) (L / N) (initial h) k θ).v x = 0 ∧
      ∀ j, (cell a b (List.finRange d) (L / N) (initial h) k θ).p j x = 0 :=
  initial_cells a hb _ hh hc (div_nonneg hL (Nat.cast_nonneg N)) N

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- With no coordinates the explicit evolution is just the scalar oscillator. -/
theorem empty_coordinates (h : (Fin 0 → ℝ) → ℝ) (t : ℝ) (x : Fin 0 → ℝ) :
    (step (Fin.elim0 : Fin 0 → (Fin 0 → ℝ)) (Fin.elim0 : Fin 0 → (Fin 0 → ℝ) → ℝ)
      [] t (initial h)).u x = Real.sin t * h x ∧
    (step (Fin.elim0 : Fin 0 → (Fin 0 → ℝ)) (Fin.elim0 : Fin 0 → (Fin 0 → ℝ) → ℝ)
      [] t (initial h)).v x = Real.cos t * h x := by
  simp [step, sweep, reaction, initial, coupling]

omit [FiniteDimensional ℝ E] in
/-- Zero initial data stay identically zero through every finite cell. -/
theorem zero_initial (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (js : List (Fin d)) (δ θ : ℝ) (k : ℕ) :
    cell a b js δ (initial 0) k θ = initial 0 := by
  have hs (t : ℝ) (is : List (Fin d)) : sweep a t is (initial 0) = initial 0 := by
    induction is with
    | nil => rfl
    | cons j is ih =>
      simpa [sweep, transport, initial, Pi.zero_def] using ih
  have hr (t : ℝ) : reaction b t (initial (0 : E → ℝ)) = initial 0 := by
    simp [reaction, initial, coupling, Pi.zero_def]
  have hn : nodes a b js δ (initial 0) k = initial 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [nodes, ih, step, hs, hr]
  simp [cell, hn, step, hs, hr]

#print axioms finite_construction
#print axioms empty_coordinates
#print axioms zero_initial
#print axioms FunctionalInequalities.Analysis.WaveSplitting.cell_endpoints
#print axioms FunctionalInequalities.Analysis.WaveSplitting.reaction_hasDerivAt_u
#print axioms FunctionalInequalities.Analysis.WaveSplitting.reaction_hasDerivAt_v
#print axioms FunctionalInequalities.Analysis.WaveSplitting.transport_hasDerivAt_v_zero
#print axioms FunctionalInequalities.Analysis.WaveSplitting.transport_hasDerivAt_p_zero
#print axioms FunctionalInequalities.Analysis.WaveSplitting.transport_characteristics
#print axioms FunctionalInequalities.Analysis.WaveSplitting.transport_energy
#print axioms FunctionalInequalities.Analysis.WaveSplitting.State.Supported.hasCompactSupport
end WaveSplittingAudit

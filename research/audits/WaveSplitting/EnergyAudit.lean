module

public import FunctionalInequalities.Analysis.WaveSplitting.Energy

/-! Independent clients of the actual splitting energy theorems. The coefficient bound below
is an explicit hypothesis of zero-order stability, not a proved localization for a potential.
No client here claims a high-order reaction estimate or a residual estimate. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingEnergyAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (m : Measure E) [IsFiniteMeasureOnCompacts m] [m.IsAddRightInvariant]

/-- A full coordinate sweep preserves every finite derivative energy, for arbitrary order
and arbitrary dimension including zero. No orthonormality is needed for preservation. -/
theorem all_orders (d k : ℕ) (a : Fin d → E) (t : ℝ) (Y : State E (Fin d))
    (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m a k (sweep a t (List.finRange d) Y) = derivativeEnergy m a k Y :=
  derivativeEnergy_sweep m a a k _ t hY hc

/-- Mesh refinement over a fixed horizon has a common zero-order energy bound. -/
theorem fixed_horizon (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (h : E → ℝ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {B L : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, ∑ j, b j x ^ 2 ≤ B) (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N)
    (hmesh : L / N ≤ 1) :
    energy m (nodes a b (List.finRange d) (L / N) (initial h) N) ≤
      Real.exp ((1 + 4 * B) * L) * squareIntegral m h := by
  have hcc : (initial h : State E (Fin d)).CompactSupport :=
    ⟨HasCompactSupport.zero, hc, fun _ => HasCompactSupport.zero⟩
  have he := energy_nodes_le_exp m a (List.finRange d) hb (smooth_initial hh) hcc
    hB0 hB (div_nonneg hL (Nat.cast_nonneg N)) hmesh N
  have htime : (N : ℝ) * (L / N) = L := by
    rw [mul_comm, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')]
  simpa [htime, energy, initial, squareIntegral] using he

section DegenerateEnergy

omit [BorelSpace E] [IsFiniteMeasureOnCompacts m] [m.IsAddRightInvariant]
/-- The zero-time boundary is the unchanged state, at every derivative order. -/
theorem time_zero (d k : ℕ) (a : Fin d → E) (Y : State E (Fin d)) :
    derivativeEnergy m a k (sweep a 0 (List.finRange d) Y) = derivativeEnergy m a k Y := by
  rw [sweep_zero]

/-- The empty-coordinate case does not demand a nonempty basis or a division by dimension. -/
theorem empty_coordinates (k : ℕ) (t : ℝ) (Y : State E (Fin 0)) :
    derivativeEnergy m Fin.elim0 k (sweep Fin.elim0 t [] Y) =
      derivativeEnergy m Fin.elim0 k Y := rfl

end DegenerateEnergy

#print axioms all_orders
#print axioms fixed_horizon
#print axioms time_zero
#print axioms empty_coordinates
#print axioms FunctionalInequalities.Analysis.WaveSplitting.differentiate_transport
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_zero
#print axioms FunctionalInequalities.Analysis.WaveSplitting.transport_pair_energy
#print axioms FunctionalInequalities.Analysis.WaveSplitting.reaction_pair_bound
#print axioms FunctionalInequalities.Analysis.WaveSplitting.squareIntegral_coupling_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.energy_reaction_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.energy_step_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.energy_nodes_le_exp
end WaveSplittingEnergyAudit

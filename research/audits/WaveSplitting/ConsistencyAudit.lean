import FunctionalInequalities.Analysis.WaveSplitting.Consistency

/-! Independent clients of consistency and the actual residual. No quantitative residual
bound, derivative-loss estimate or mesh-uniform convergence is asserted. -/
noncomputable section
set_option autoImplicit false
open FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingConsistencyAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every complete coordinate sweep has the intended three-component infinitesimal system. -/
theorem full_system (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (Y : State E (Fin d)) (hY : Y.Smooth) :
    HasTimeDerivative (fun t => step a b (List.finRange d) t Y) (waveGenerator a b Y) 0 := by
  simpa only [splitGenerator_finRange] using step_hasTimeDerivative_zero a b (List.finRange d) hY

/-- The same consistency statement applies to the computed state of every cell. -/
theorem every_cell (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (h : E → ℝ) (hh : ContDiff ℝ ∞ h) (δ : ℝ) (k : ℕ) :
    HasTimeDerivative (cell a b (List.finRange d) δ (initial h) k)
      (waveGenerator a b (nodes a b (List.finRange d) δ (initial h) k)) 0 := by
  simpa only [splitGenerator_finRange] using
    cell_hasTimeDerivative_zero a hb (List.finRange d) (smooth_initial hh) δ k

/-- The actual residual vanishes at the beginning of every cell. -/
theorem every_cell_residual_zero (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (Y : State E (Fin d)) (hY : Y.Smooth) (δ : ℝ) (k : ℕ) :
    residual a b (List.finRange d) (nodes a b (List.finRange d) δ Y k) 0 = zeroState :=
  residual_zero a b _ (hY.nodes a hb _ δ k)

/-- Empty dimension still gives the scalar oscillator, not a nonexistent spatial derivative. -/
theorem empty_coordinates (Y : State E (Fin 0)) (hY : Y.Smooth) (x : E) :
    HasDerivAt (fun t => (step Fin.elim0 Fin.elim0 [] t Y).u x) (Y.v x) 0 ∧
    HasDerivAt (fun t => (step Fin.elim0 Fin.elim0 [] t Y).v x) (-Y.u x) 0 := by
  have h := full_system 0 Fin.elim0 Fin.elim0 Y hY
  exact ⟨by simpa [List.finRange, waveGenerator] using h.1 x,
    by simpa [List.finRange, waveGenerator, coupling] using h.2.1 x⟩

#print axioms full_system
#print axioms every_cell
#print axioms every_cell_residual_zero
#print axioms empty_coordinates
#print axioms FunctionalInequalities.Analysis.WaveSplitting.HasTimeDerivative.transport_zero
#print axioms FunctionalInequalities.Analysis.WaveSplitting.HasTimeDerivative.sweep_zero
#print axioms FunctionalInequalities.Analysis.WaveSplitting.HasTimeDerivative.reaction_zero
#print axioms FunctionalInequalities.Analysis.WaveSplitting.step_hasTimeDerivative_zero
#print axioms FunctionalInequalities.Analysis.WaveSplitting.jointSmooth_residual
#print axioms FunctionalInequalities.Analysis.WaveSplitting.residual_integral
end WaveSplittingConsistencyAudit

import FunctionalInequalities.Analysis.WaveSplitting.Localization

/-! Independent clients of localization and fixed-horizon stability for original smooth
coefficients. No global coefficient bounds, convexity or sign assumptions are added. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingLocalizationAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- One cutoff works at all finite orders, even in dimension zero. -/
theorem all_orders (d : ℕ) (b : Fin d → E → ℝ) (hb : ∀ j, ContDiff ℝ ∞ (b j)) (R : ℝ) :
    ∃ c : Fin d → E → ℝ, (∀ j, ContDiff ℝ ∞ (c j)) ∧
      (∀ j, HasCompactSupport (c j)) ∧ (∀ j x, ‖x‖ ≤ R → c j x = b j x) ∧
      ∀ (a : Fin d → E) k, ∃ B : ℝ, 0 ≤ B ∧
        ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (c j) x ^ 2 ≤ B :=
  exists_localized_coefficient b hb R

variable [MeasurableSpace E] [BorelSpace E]
variable (m : Measure E) [IsFiniteMeasureOnCompacts m] [m.IsAddRightInvariant]

/-- Smooth potential directional coefficients need no global bound in the fifth-order estimate. -/
theorem potential_fifth_order (d : ℕ) (a : Fin d → E) (U h : E → ℝ)
    (hU : ContDiff ℝ ∞ U) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        derivativeEnergy m a 5
          (cell a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ (initial h) k θ) ≤
          Real.exp (C * L) * derivativeEnergy m a 5 (initial h) := by
  obtain ⟨R, _, hR⟩ := supported_initial hc
  have hb (j : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ U x (a j)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  exact exists_cell_energy_bound m a (List.finRange d) hb (smooth_initial hh) hR 5 L

#print axioms all_orders
#print axioms potential_fifth_order
#print axioms FunctionalInequalities.Analysis.WaveSplitting.exists_wordDerivative_bound
#print axioms FunctionalInequalities.Analysis.WaveSplitting.reaction_eq_of_supported
#print axioms FunctionalInequalities.Analysis.WaveSplitting.nodes_eq_of_supported
#print axioms FunctionalInequalities.Analysis.WaveSplitting.cell_eq_of_supported
#print axioms FunctionalInequalities.Analysis.WaveSplitting.exists_cell_energy_bound
end WaveSplittingLocalizationAudit

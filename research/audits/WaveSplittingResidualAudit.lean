import FunctionalInequalities.Analysis.WaveSplitting.Residual

/-! Independent clients of the tame estimate for the actual split residual. The residual is
the defined `residual` of the explicit step; no residual smallness, second temporal derivative
bound or operator bound is assumed. The cell clients use the original smooth coefficient
without global derivative bounds. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingResidualAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For the complete coordinate list the actual residual is measured against the wave system. -/
theorem residual_against_wave (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (Y : State E (Fin d)) (θ : ℝ) :
    residual a b (List.finRange d) Y θ =
      subState (timeDerivative (fun s => step a b (List.finRange d) s Y) θ)
        (waveGenerator a b (step a b (List.finRange d) θ Y)) := by
  rw [residual_eq_subState, splitGenerator_finRange]

/-- In dimension zero the step is the exact zero-order flow and its residual vanishes. -/
theorem zero_dimension_exact (Y : State E (Fin 0)) (hY : Y.Smooth) (θ : ℝ) :
    residual Fin.elim0 Fin.elim0 (List.finRange 0) Y θ = zeroState := by
  rw [residual_eq Fin.elim0 Fin.elim0 _ hY θ]
  simp [List.finRange, sweepDerivative, sweepGenerator, reaction_zeroState]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (m : Measure E) [IsFiniteMeasureOnCompacts m] [m.IsAddRightInvariant]

/-- The third-order residual of the complete split step is controlled by the fifth-order
energy. The constant is chosen before the state and the time. -/
theorem third_order_residual (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ 4 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : State E (Fin d), Y.Smooth → Y.CompactSupport →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        derivativeEnergy m a 3 (residual a b (List.finRange d) Y θ) ≤
          C * θ ^ 2 * derivativeEnergy m a 5 Y :=
  ⟨residualConstant (List.finRange d) 3 B, residualConstant_nonneg _ 3 hB,
    fun _ hY hc _ hθ hθ1 =>
      derivativeEnergy_residual_le m a (List.finRange d) 3 hb hB hbB hY hc hθ hθ1⟩

/-- The same explicit constant at every finite order, with two derivative losses. -/
theorem all_orders (d k : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k + 1 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B)
    (Y : State E (Fin d)) (hY : Y.Smooth) (hc : Y.CompactSupport) {θ : ℝ} (hθ : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    derivativeEnergy m a k (residual a b (List.finRange d) Y θ) ≤
      residualConstant (List.finRange d) k B * θ ^ 2 * derivativeEnergy m a (k + 2) Y :=
  derivativeEnergy_residual_le m a (List.finRange d) k hb hB hbB hY hc hθ hθ1

/-- At time zero the quantitative bound forces the residual energy to vanish. -/
theorem zero_time (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ 4 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B)
    (Y : State E (Fin d)) (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m a 3 (residual a b (List.finRange d) Y 0) = 0 := by
  have h := derivativeEnergy_residual_le m a (List.finRange d) 3 hb hB hbB hY hc le_rfl
    zero_le_one
  have h0 := derivativeEnergy_nonneg m a 3 (residual a b (List.finRange d) Y 0)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_mul] at h
  linarith

/-- Dimension zero is admitted by the general estimate, with a zero coefficient bound. -/
theorem zero_dimension (Y : State E (Fin 0)) (hY : Y.Smooth) (hc : Y.CompactSupport)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    derivativeEnergy m Fin.elim0 3 (residual Fin.elim0 Fin.elim0 (List.finRange 0) Y θ) ≤
      residualConstant (ι := Fin 0) (List.finRange 0) 3 0 * θ ^ 2 *
        derivativeEnergy m Fin.elim0 5 Y :=
  derivativeEnergy_residual_le m Fin.elim0 (List.finRange 0) 3 (b := Fin.elim0)
    (fun j => Fin.elim0 j) le_rfl (fun j => Fin.elim0 j) hY hc hθ hθ1

/-- Actual grid cells for an arbitrary original smooth coefficient and arbitrary smooth
initial state supported in a ball: one constant for all meshes of the fixed horizon. -/
theorem cells_third_order (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (Y : State E (Fin d)) (hY : Y.Smooth) {R : ℝ}
    (hR : Y.Supported R) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        derivativeEnergy m a 3
          (residual a b (List.finRange d) (nodes a b (List.finRange d) δ Y k) θ) ≤ C * δ ^ 2 :=
  exists_cell_residual_bound m a (List.finRange d) hb hY hR 3 L

/-- Smooth potential directional coefficients and compactly supported initial velocity need
neither convexity nor global derivative bounds. -/
theorem potential_cells_third_order (d : ℕ) (a : Fin d → E) (U h : E → ℝ)
    (hU : ContDiff ℝ ∞ U) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        derivativeEnergy m a 3
          (residual a (fun j x => fderiv ℝ U x (a j)) (List.finRange d)
            (nodes a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ (initial h) k) θ) ≤
          C * δ ^ 2 := by
  obtain ⟨R, _, hR⟩ := supported_initial hc
  have hb (j : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ U x (a j)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  exact exists_cell_residual_bound m a (List.finRange d) hb (smooth_initial hh) hR 3 L

#print axioms residual_against_wave
#print axioms zero_dimension_exact
#print axioms third_order_residual
#print axioms all_orders
#print axioms zero_time
#print axioms zero_dimension
#print axioms cells_third_order
#print axioms potential_cells_third_order
#print axioms FunctionalInequalities.Analysis.WaveSplitting.HasTimeDerivative.sweep
#print axioms FunctionalInequalities.Analysis.WaveSplitting.step_hasTimeDerivative
#print axioms FunctionalInequalities.Analysis.WaveSplitting.residual_eq
#print axioms FunctionalInequalities.Analysis.WaveSplitting.hasDerivAt_fderiv_slice
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_le_of_timeDerivative
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_sweepDerivative_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_sweep_commutator_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_sweepResidual_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_reaction_commutator_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_residual_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.residual_eq_of_supported
#print axioms FunctionalInequalities.Analysis.WaveSplitting.exists_cell_residual_bound
end WaveSplittingResidualAudit

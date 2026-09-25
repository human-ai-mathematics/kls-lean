import FunctionalInequalities.Analysis.WaveSplitting.Compatibility

/-! Independent clients of the weighted forced energy and the gradient-compatibility defect of
the actual splitting cells. The weight is `exp (-U)` for an arbitrary smooth potential and the
coefficient is `b_j = D_(a_j) U`; no convexity, sign or global derivative bound is assumed, and
`p = grad u` is not imposed. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingWeightedEnergyAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The potential weight satisfies the weight relation `D_(a_j) w = -b_j w`. -/
theorem potential_weight (d : ℕ) (a : Fin d → E) {U : E → ℝ} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ 1 (fun x => Real.exp (-U x)) ∧ (∀ x, 0 ≤ Real.exp (-U x)) ∧
      ∀ j x, fderiv ℝ (fun x => Real.exp (-U x)) x (a j) =
        -(fderiv ℝ U x (a j) * Real.exp (-U x)) := by
  refine ⟨Real.contDiff_exp.comp ((hU.of_le (by simp)).neg), fun x => (Real.exp_pos _).le,
    fun j x => ?_⟩
  have h : HasFDerivAt (fun x => Real.exp (-U x)) (Real.exp (-U x) • -fderiv ℝ U x) x :=
    (((hU.differentiable (by simp)) x).hasFDerivAt.neg).exp
  rw [h.fderiv]
  simp only [FunLike.coe_smul, FunLike.coe_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- Initial wave data are gradient-compatible. -/
theorem initial_compatible (d : ℕ) (a : Fin d → E) (h : E → ℝ) :
    compatibilityDefect a (initial h : State E (Fin d)) = zeroState := by
  unfold compatibilityDefect initial zeroState
  congr 1
  funext j x
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : Measure E) [m.IsAddHaarMeasure]

/-- The actual wave generator is skew for the potential weight. -/
theorem potential_skew (d : ℕ) (a : Fin d → E) {U : E → ℝ} (hU : ContDiff ℝ ∞ U)
    (Y : State E (Fin d)) (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R) :
    weightedPairing m (fun x => Real.exp (-U x)) Y
      (waveGenerator a (fun j x => fderiv ℝ U x (a j)) Y) = 0 :=
  weightedPairing_waveGenerator m a _ (potential_weight d a hU).1 (potential_weight d a hU).2.2 hY hR

/-- Forced weighted energy for the potential cells: the leading term is the initial weighted
norm `sqrt(∫ exp(-U) h^2)` with coefficient one, uniformly over the meshes of the horizon. -/
theorem potential_weighted_cells (d : ℕ) (a : Fin d → E) (U h : E → ℝ)
    (hU : ContDiff ℝ ∞ U) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        √(weightedEnergy m (fun x => Real.exp (-U x))
          (cell a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ (initial h) k θ)) ≤
          √(∫ x, Real.exp (-U x) * h x ^ 2 ∂m) + C * δ := by
  obtain ⟨R, _, hR⟩ := supported_initial (ι := Fin d) hc
  have hb (j : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ U x (a j)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨hw, hw0, hwb⟩ := potential_weight d a hU
  obtain ⟨C, hC, hbound⟩ := exists_weightedEnergy_cell_bound m a hb hw hw0 hwb
    (smooth_initial hh) hR L
  refine ⟨C, hC, fun N δ hδ hδ1 hL k hk θ hθ hθδ => ?_⟩
  have e : weightedEnergy m (fun x => Real.exp (-U x)) (initial h : State E (Fin d)) =
      ∫ x, Real.exp (-U x) * h x ^ 2 ∂m := by
    simp [weightedEnergy, initial]
  rw [← e]
  exact hbound N δ hδ hδ1 hL k hk θ hθ hθδ

/-- The compatibility defect of the potential cells is `O(δ)` in the second-order energy,
starting from compatible initial data. -/
theorem potential_defect_second_order (d : ℕ) (a : Fin d → E) (U h : E → ℝ)
    (hU : ContDiff ℝ ∞ U) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        √(derivativeEnergy m a 2 (compatibilityDefect a
          (cell a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ (initial h) k θ))) ≤
          C * δ := by
  obtain ⟨R, _, hR⟩ := supported_initial (ι := Fin d) hc
  have hb (j : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ U x (a j)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨C, hC, hbound⟩ := exists_defect_cell_bound m a hb (smooth_initial hh) hR 2 L
  refine ⟨C, hC, fun N δ hδ hδ1 hL k hk θ hθ hθδ => ?_⟩
  have h0 := hbound N δ hδ hδ1 hL k hk θ hθ hθδ
  rwa [initial_compatible, derivativeEnergy_zeroState, Real.sqrt_zero, zero_add] at h0

/-- The weighted coordinate form energy of `u` on the potential cells is bounded by the
initial weighted norm plus `C δ`. -/
theorem potential_form_energy (d : ℕ) (a : Fin d → E) (U h : E → ℝ)
    (hU : ContDiff ℝ ∞ U) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        √(weightedEnergy m (fun x => Real.exp (-U x)) (formState a
          (cell a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ (initial h) k θ))) ≤
          √(∫ x, Real.exp (-U x) * h x ^ 2 ∂m) + C * δ := by
  obtain ⟨R, _, hR⟩ := supported_initial (ι := Fin d) hc
  have hb (j : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ U x (a j)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨hw, hw0, hwb⟩ := potential_weight d a hU
  obtain ⟨C, hC, hbound⟩ := exists_formEnergy_cell_bound m a hb hw hw0 hwb
    (smooth_initial hh) hR L
  refine ⟨C, hC, fun N δ hδ hδ1 hL k hk θ hθ hθδ => ?_⟩
  have h0 := hbound N δ hδ hδ1 hL k hk θ hθ hθδ
  have e : weightedEnergy m (fun x => Real.exp (-U x)) (initial h : State E (Fin d)) =
      ∫ x, Real.exp (-U x) * h x ^ 2 ∂m := by
    simp [weightedEnergy, initial]
  rwa [initial_compatible, derivativeEnergy_zeroState, Real.sqrt_zero, zero_add, e] at h0

/-- In dimension zero the actual step conserves every weighted energy exactly up to growth
zero: the residual vanishes, so the forced bound gives no increase. -/
theorem zero_dimension (Y : State E (Fin 0)) (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R)
    {w : E → ℝ} (hw : ContDiff ℝ 1 w) (hw0 : ∀ x, 0 ≤ w x) {θ : ℝ} (hθ : 0 ≤ θ) :
    √(weightedEnergy m w (step Fin.elim0 Fin.elim0 (List.finRange 0) θ Y)) ≤
      √(weightedEnergy m w Y) := by
  have hz (s : ℝ) : residual Fin.elim0 Fin.elim0 (List.finRange 0) Y s = zeroState := by
    rw [residual_eq Fin.elim0 Fin.elim0 _ hY s]
    simp [List.finRange, sweepDerivative, sweepGenerator, reaction_zeroState]
  have h := sqrt_weightedEnergy_step_le m Fin.elim0 (b := Fin.elim0) (fun j => Fin.elim0 j)
    hw hw0 (fun j => Fin.elim0 j) hY hR hθ le_rfl fun s _ => by
      rw [hz s]; simp [weightedEnergy, zeroState]
  simpa using h

/-- At time zero the defect step bound adds nothing. -/
theorem zero_time (d k : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (Y : State E (Fin d)) (hY : Y.Smooth) {R : ℝ}
    (hR : Y.Supported R) :
    √(derivativeEnergy m a k (compatibilityDefect a (step a b (List.finRange d) 0 Y))) ≤
      √(derivativeEnergy m a k (compatibilityDefect a Y)) := by
  have h := sqrt_derivativeEnergy_defect_step_le m a hb hY hR k (θ := 0) (M := 0) le_rfl
    fun s hs => by
      rw [show s = 0 from le_antisymm hs.2 hs.1, residual_zero a b _ hY,
        derivativeEnergy_zeroState]
  simp only [zero_mul, add_zero] at h
  exact h

/-- The square root of the ordered derivative energy is subadditive. -/
theorem derivative_minkowski (d k : ℕ) (a : Fin d → E) (X Z : State E (Fin d))
    (hX : X.Smooth) (hZ : Z.Smooth) {R : ℝ} (hXR : X.Supported R) (hZR : Z.Supported R) :
    √(derivativeEnergy m a k (addState X Z)) ≤
      √(derivativeEnergy m a k X) + √(derivativeEnergy m a k Z) := by
  have h := Real.sqrt_le_sqrt (derivativeEnergy_addState_le_sq m a k hX hZ hXR hZR)
  rwa [Real.sqrt_sq (by positivity)] at h

#print axioms potential_weight
#print axioms initial_compatible
#print axioms potential_skew
#print axioms potential_weighted_cells
#print axioms potential_defect_second_order
#print axioms potential_form_energy
#print axioms zero_dimension
#print axioms zero_time
#print axioms derivative_minkowski
#print axioms FunctionalInequalities.Analysis.WaveSplitting.weightedPairing_waveGenerator
#print axioms FunctionalInequalities.Analysis.WaveSplitting.hasDerivAt_weightedEnergy
#print axioms FunctionalInequalities.Analysis.WaveSplitting.sqrt_weightedEnergy_step_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.exists_weightedEnergy_cell_bound
#print axioms FunctionalInequalities.Analysis.WaveSplitting.compatibilityDefect_timeDerivative_step
#print axioms FunctionalInequalities.Analysis.WaveSplitting.sqrt_derivativeEnergy_defect_step_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.exists_defect_cell_bound
#print axioms FunctionalInequalities.Analysis.WaveSplitting.exists_formEnergy_cell_bound
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_addState_le_sq
end WaveSplittingWeightedEnergyAudit

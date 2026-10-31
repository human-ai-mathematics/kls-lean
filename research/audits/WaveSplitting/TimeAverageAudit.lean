module

public import FunctionalInequalities.Analysis.WaveSplitting.TimeAverage

/-! Independent clients of the finite time average of the actual splitting cells and its exact
`J_cl q - h` identity. The identity involves the actual residual on every cell and the actual
compatibility defect; no residual bound, wave existence or `p = grad u` is assumed. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingTimeAverageAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- For compactly supported smooth initial velocity the time average is `C_c^∞`. -/
theorem average_smooth_compact (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (h : E → ℝ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    ContDiff ℝ ∞ (timeAverage a b (List.finRange d) δ (initial h) N) ∧
      HasCompactSupport (timeAverage a b (List.finRange d) δ (initial h) N) := by
  obtain ⟨R, _, hR⟩ := supported_initial (ι := Fin d) hc
  exact ⟨contDiff_timeAverage a hb _ (smooth_initial hh) δ N,
    hasCompactSupport_timeAverage a b _ hR hδ N⟩

/-- The `J_cl q - h` identity for wave initial data `(0,h,0)` on the horizon `L = N δ`. -/
theorem wave_identity (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (h : E → ℝ) (hh : ContDiff ℝ ∞ h) {δ : ℝ} {N : ℕ}
    (hL : (N : ℝ) * δ ≠ 0) (x : E) :
    formOperator a b (timeAverage a b (List.finRange d) δ (initial h) N) x - h x =
      -(nodes a b (List.finRange d) δ (initial h) N).u x / (N * δ) +
      (∑ k ∈ Finset.range N, ∫ θ in (0 : ℝ)..δ, (residual a b (List.finRange d)
        (nodes a b (List.finRange d) δ (initial h) k) θ).u x) / (N * δ) +
      ∑ k ∈ Finset.range N, ∫ θ in (0 : ℝ)..δ, (1 - (k * δ + θ) / (N * δ)) *
        (weightedDivergence a b (compatibilityDefect a
            (cell a b (List.finRange d) δ (initial h) k θ)).p x +
          (residual a b (List.finRange d)
            (nodes a b (List.finRange d) δ (initial h) k) θ).v x) := by
  have e := formOperator_timeAverage a hb (smooth_initial hh (ι := Fin d)) hL x
  have hu : (initial h : State E (Fin d)).u x = 0 := rfl
  have hv : (initial h : State E (Fin d)).v x = h x := rfl
  rw [hv, hu, zero_sub] at e
  exact e

omit [FiniteDimensional ℝ E] in
/-- The velocity of the actual generator is `-J_cl u + div_b (p - D u)` exactly. -/
theorem generator_split (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ) (Y : State E (Fin d))
    (hY : Y.Smooth) (x : E) :
    (waveGenerator a b Y).v x = -formOperator a b Y.u x +
      weightedDivergence a b (compatibilityDefect a Y).p x :=
  waveGenerator_v_eq a b hY x

/-- A single cell is admitted: `N = 1`. -/
theorem one_cell (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ) (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (Y : State E (Fin d)) (hY : Y.Smooth) {δ : ℝ} (hδ : δ ≠ 0) (x : E) :
    formOperator a b (timeAverage a b (List.finRange d) δ Y 1) x - Y.v x =
      (Y.u x - (nodes a b (List.finRange d) δ Y 1).u x) / ((1 : ℕ) * δ) +
      (∑ k ∈ Finset.range 1, ∫ θ in (0 : ℝ)..δ, (residual a b (List.finRange d)
        (nodes a b (List.finRange d) δ Y k) θ).u x) / ((1 : ℕ) * δ) +
      ∑ k ∈ Finset.range 1, ∫ θ in (0 : ℝ)..δ, (1 - (k * δ + θ) / ((1 : ℕ) * δ)) *
        (weightedDivergence a b (compatibilityDefect a
            (cell a b (List.finRange d) δ Y k θ)).p x +
          (residual a b (List.finRange d) (nodes a b (List.finRange d) δ Y k) θ).v x) :=
  formOperator_timeAverage a hb hY (by simpa using hδ) x

/-- In dimension zero `J_cl` is the identity, the residual vanishes and there is no defect:
the identity reduces to `q - v(0) = (u(0) - u(L))/L`. -/
theorem zero_dimension (Y : State E (Fin 0)) (hY : Y.Smooth) {δ : ℝ} {N : ℕ}
    (hL : (N : ℝ) * δ ≠ 0) (x : E) :
    timeAverage Fin.elim0 Fin.elim0 (List.finRange 0) δ Y N x - Y.v x =
      (Y.u x - (nodes Fin.elim0 Fin.elim0 (List.finRange 0) δ Y N).u x) / (N * δ) := by
  have e := formOperator_timeAverage Fin.elim0 (b := Fin.elim0) (fun j => Fin.elim0 j) hY hL x
  have hz (Z : State E (Fin 0)) (hZ : Z.Smooth) (s : ℝ) :
      residual Fin.elim0 Fin.elim0 (List.finRange 0) Z s = zeroState := by
    rw [residual_eq Fin.elim0 Fin.elim0 _ hZ s]
    simp [List.finRange, sweepDerivative, sweepGenerator, reaction_zeroState]
  simp only [hz _ (hY.nodes Fin.elim0 (fun j => Fin.elim0 j) _ δ _)] at e
  simpa [formOperator, weightedDivergence, zeroState] using e

#print axioms average_smooth_compact
#print axioms wave_identity
#print axioms generator_split
#print axioms one_cell
#print axioms zero_dimension
#print axioms FunctionalInequalities.Analysis.WaveSplitting.hasFDerivAt_intervalIntegral_slice
#print axioms FunctionalInequalities.Analysis.WaveSplitting.contDiff_intervalIntegral_slice
#print axioms FunctionalInequalities.Analysis.WaveSplitting.formOperator_intervalIntegral
#print axioms FunctionalInequalities.Analysis.WaveSplitting.integral_formOperator_step
#print axioms FunctionalInequalities.Analysis.WaveSplitting.formOperator_timeAverage
#print axioms FunctionalInequalities.Analysis.WaveSplitting.contDiff_timeAverage
#print axioms FunctionalInequalities.Analysis.WaveSplitting.hasCompactSupport_timeAverage
end WaveSplittingTimeAverageAudit

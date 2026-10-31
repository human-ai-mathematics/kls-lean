module

public import FunctionalInequalities.Analysis.WaveSplitting.Stability

/-! Independent clients: actual coefficient derivative bounds remain explicit.
Neither localization of the original potential nor residual control is claimed. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingStabilityAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (m : Measure E) [IsFiniteMeasureOnCompacts m] [m.IsAddRightInvariant]

/-- Fifth-order stability at fixed horizon for arbitrary compact smooth initial data. -/
theorem fifth_order_horizon (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (h : E → ℝ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {B L : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j r, r.length ≤ 5 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B)
    (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N) (hmesh : L / N ≤ 1) :
    derivativeEnergy m a 5 (nodes a b (List.finRange d) (L / N) (initial h) N) ≤
      Real.exp ((1 + 4 * couplingConstant (ι := Fin d) 5 B) * L) *
        derivativeEnergy m a 5 (initial h) := by
  have hcc : (initial h : State E (Fin d)).CompactSupport :=
    ⟨HasCompactSupport.zero, hc, fun _ => HasCompactSupport.zero⟩
  have he := derivativeEnergy_nodes_le_exp m a 5 (List.finRange d) hb (smooth_initial hh)
    hcc hB0 hB (div_nonneg hL (Nat.cast_nonneg N)) hmesh N
  have htime : (N : ℝ) * (L / N) = L := by
    rw [mul_comm, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')]
  simpa only [htime] using he

/-- Fifth-order control throughout every mesh cell. -/
theorem fifth_order_cell (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (Y : State E (Fin d))
    (hY : Y.Smooth) (hc : Y.CompactSupport) {B δ θ : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j r, r.length ≤ 5 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ θ) (hθδ : θ ≤ δ) (j : ℕ) :
    derivativeEnergy m a 5 (cell a b (List.finRange d) δ Y j θ) ≤
      Real.exp ((1 + 4 * couplingConstant (ι := Fin d) 5 B) * (j * δ + θ)) *
        derivativeEnergy m a 5 Y :=
  derivativeEnergy_cell_le_exp m a 5 _ hb hY hc hB0 hB hδ hδ1 hθ (hθδ.trans hδ1) j

omit [m.IsAddRightInvariant] in
/-- Empty coordinates require no dimension divisor or nonempty assumption. -/
theorem empty_coordinates (order : ℕ) (Y : State E (Fin 0)) (hY : Y.Smooth)
    (hc : Y.CompactSupport) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    derivativeEnergy m Fin.elim0 order (reaction Fin.elim0 t Y) ≤
      (1 + t) * derivativeEnergy m Fin.elim0 order Y := by
  have he := derivativeEnergy_reaction_le m Fin.elim0 order (b := Fin.elim0)
    (fun j => Fin.elim0 j) hY hc (B := 0) le_rfl (fun j => Fin.elim0 j) ht ht1
  simpa [couplingConstant] using he

omit [MeasurableSpace E] [BorelSpace E] in
/-- The product formula refers to the actual iterated Fréchet derivative at every order. -/
theorem product_formula (d n : ℕ) (a : Fin d → E) (w : Fin n → Fin d)
    (b f : E → ℝ) (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) :
    derivative (fun i => a (w i)) (fun x => b x * f x) = fun x =>
      ((wordSplits (List.ofFn w)).map (fun p => wordDerivative a p.1 b x *
        wordDerivative a p.2 f x)).sum := by
  rw [← wordDerivative_ofFn a w (hb.mul hf)]
  exact wordDerivative_mul a _ hb hf

#print axioms fifth_order_horizon
#print axioms fifth_order_cell
#print axioms empty_coordinates
#print axioms product_formula
#print axioms FunctionalInequalities.Analysis.WaveSplitting.scalarEnergy_mul_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_eq_scalarEnergy
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_reaction_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_step_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_nodes_le_exp
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_cell_le_exp
end WaveSplittingStabilityAudit

import FunctionalInequalities.Analysis.WaveSplitting.GeneratorBounds

/-! Independent energy clients. These are actual generator estimates, not a claim that the
second temporal derivative of a split product equals the square of its summed generator. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingGeneratorBoundsAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (m : Measure E) [IsFiniteMeasureOnCompacts m]

/-- The full wave generator squared is controlled from order five to order three. -/
theorem wave_five_to_three (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (Y : State E (Fin d)) (hY : Y.Smooth) (hc : Y.CompactSupport)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ 4 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) :
    derivativeEnergy m a 3 (waveGenerator a b (waveGenerator a b Y)) ≤
      generatorConstant (List.finRange d) 3 B * generatorConstant (List.finRange d) 4 B *
        derivativeEnergy m a 5 Y := by
  simpa only [splitGenerator_finRange] using
    derivativeEnergy_splitGenerator_sq_le m a (List.finRange d) 3 hb hY hc hB hbB

/-- Both mixed orders and both repeated types are covered, without commuting generators. -/
theorem mixed_five_to_three (d : ℕ) (a : Fin d → E) (b : Fin d → E → ℝ)
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (Y : State E (Fin d)) (hY : Y.Smooth) (hc : Y.CompactSupport)
    (i j : Option (Fin d)) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ 4 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) :
    derivativeEnergy m a 3 (elementaryGenerator a b i (elementaryGenerator a b j Y)) ≤
      elementaryConstant (ι := Fin d) 3 B * elementaryConstant (ι := Fin d) 4 B *
        derivativeEnergy m a 5 Y :=
  derivativeEnergy_two_elementary_le m a 3 i j hb hY hc hB hbB

/-- The one-order coordinate bound is uniform in the chosen derivative order. -/
theorem all_coordinate_orders (d k : ℕ) (a : Fin d → E) (j : Fin d)
    (Y : State E (Fin d)) (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m a k (coordinateGenerator (a j) j Y) ≤
      (jetCount (ι := Fin d) k : ℝ) * derivativeEnergy m a (k + 1) Y :=
  derivativeEnergy_coordinateGenerator_le m a k j hY hc

/-- Empty coordinates retain the reaction generator and need no nonempty-space assumption. -/
theorem empty_coordinates (k : ℕ) (Y : State E (Fin 0)) (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m Fin.elim0 k (reactionGenerator Fin.elim0 Y) ≤
      2 * derivativeEnergy m Fin.elim0 k Y := by
  have h := derivativeEnergy_reactionGenerator_le m Fin.elim0 k (b := Fin.elim0)
    (fun j => Fin.elim0 j) hY hc (B := 0) le_rfl (fun j => Fin.elim0 j)
  simpa [couplingConstant] using h

#print axioms wave_five_to_three
#print axioms mixed_five_to_three
#print axioms all_coordinate_orders
#print axioms empty_coordinates
#print axioms FunctionalInequalities.Analysis.WaveSplitting.scalarEnergy_coordinate_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_two_coordinates_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_reactionGenerator_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_splitGenerator_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_splitGenerator_sq_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.derivativeEnergy_two_elementary_le
end WaveSplittingGeneratorBoundsAudit

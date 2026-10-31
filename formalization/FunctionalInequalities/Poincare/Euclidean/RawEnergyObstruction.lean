module

public import FunctionalInequalities.Poincare.SmoothTest.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Raw ambient gradient energy depends on the representative

Source: Blueprint `obs:dirac-raw-energy` and the existing checks in
`examples/PoincareFoundation.lean`. This obstruction concerns raw gradient energy;
it does not concern the value of the intrinsic relaxed energy. It is not a ledger node.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.Euclidean

/-- At the Dirac atom, zero and the identity are equal almost everywhere. -/
theorem zero_ae_eq_id_dirac : (fun _ : ℝ ↦ (0 : ℝ)) =ᵐ[Measure.dirac 0] id := by
  change ∀ᵐ x ∂(Measure.dirac (0 : ℝ)), (0 : ℝ) = id x
  simp

/--
The named raw-energy obstruction: the same a.e. representative class has energies 0 and 1. -/
theorem dirac_raw_energy :
    (fun _ : ℝ ↦ (0 : ℝ)) =ᵐ[Measure.dirac 0] id ∧
      Poincare.SmoothTest.energy (Measure.dirac (0 : ℝ)) (fun _ ↦ 0) = 0 ∧
        Poincare.SmoothTest.energy (Measure.dirac (0 : ℝ)) id = 1 := by
  refine ⟨zero_ae_eq_id_dirac, ?_, ?_⟩ <;> rw [Poincare.SmoothTest.energy_eq_fderiv] <;> simp

/-- Both representatives are in L² and their actual `toLp` classes are equal. -/
theorem dirac_toLp_zero_eq_id :
    ∃ (hzero : MemLp (fun _ : ℝ ↦ (0 : ℝ)) 2 (Measure.dirac 0))
      (hid : MemLp (id : ℝ → ℝ) 2 (Measure.dirac 0)),
      hzero.toLp (fun _ ↦ 0) = hid.toLp id := by
  have hzero : MemLp (fun _ : ℝ ↦ (0 : ℝ)) 2 (Measure.dirac 0) := memLp_const 0
  have hid : MemLp (id : ℝ → ℝ) 2 (Measure.dirac 0) :=
    hzero.ae_eq zero_ae_eq_id_dirac
  exact ⟨hzero, hid, (MemLp.toLp_eq_toLp_iff hzero hid).mpr zero_ae_eq_id_dirac⟩

end FunctionalInequalities.Poincare.Euclidean

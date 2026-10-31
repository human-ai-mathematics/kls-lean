module

public import FunctionalInequalities.Analysis.Matrix.Integral

/-!
# Arbitrary-coefficient trace-integral extension: clients

Clients of `symmetric_trace_integral_extension_mul` with coefficients other than Letwin's `C = 2`:
- `scalar_field`: the constant field `H ≡ c • 1` (`c ≥ 0`) under a Dirac mass satisfies `tr(A H A H)
  = c² tr(A²)` for every
  `A`, so the hypothesis holds with coefficient `c²`; `indefinite_diag_three` applies it to the
  indefinite
  `B = diag(1, −2)` with coefficient `9`.
- `empty_index_negative_coefficient`: on the empty index type every hypothesis holds with `C = −1`,
  so the theorem needs no
  sign condition on the coefficient.

These are independent audit clients, not ledger certificates.
-/

@[expose] public section

noncomputable section
open Matrix MeasureTheory FunctionalInequalities.Analysis

namespace MatrixTraceIntegralCoefficientAudit

section FiniteIndex

variable {ι : Type*}
  [Fintype ι] [DecidableEq ι]

/-- `tr(A (c • 1) A (c • 1)) = c² tr(A²)`. -/
theorem scalar_field_trace (c : ℝ) (A : Matrix ι ι ℝ) :
    (A * (c • (1 : Matrix ι ι ℝ)) * A * (c • (1 : Matrix ι ι ℝ))).trace =
      c ^ 2 * (A * A).trace := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  ring

/--
The constant field `c • 1` under the Dirac mass on `Unit`: coefficient `c²` for every symmetric `B`.
-/
theorem scalar_field (c : ℝ) (hc : 0 ≤ c) {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
    Integrable
        (fun _ : Unit => (B * (c • (1 : Matrix ι ι ℝ)) * B * (c • (1 : Matrix ι ι ℝ))).trace)
        (Measure.dirac ()) ∧
      (∫ _ : Unit,
          (B * (c • (1 : Matrix ι ι ℝ)) * B *
              (c • (1 : Matrix ι ι ℝ))).trace ∂(Measure.dirac ())) ≤
        c ^ 2 * (B * B).trace := by
  refine
    symmetric_trace_integral_extension_mul (Measure.dirac ()) (fun _ => c • (1 : Matrix ι ι ℝ))
      (fun _ _ => measurable_const) (fun _ => Matrix.PosSemidef.one.smul hc)
      (fun A _ => ⟨integrable_const _, ?_⟩) hB
  rw [integral_dirac]
  exact (scalar_field_trace c A).le

end FiniteIndex

/-- The indefinite `B = diag(1, −2)` with the field `3 • 1`: coefficient `9`. -/
theorem indefinite_diag_three :
    (∫ _ : Unit,
        (!![(1 : ℝ), 0; 0, -2] * ((3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
              !![(1 : ℝ), 0; 0, -2] *
            ((3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))).trace ∂(Measure.dirac ())) ≤
      (3 : ℝ) ^ 2 * (!![(1 : ℝ), 0; 0, -2] * !![(1 : ℝ), 0; 0, -2]).trace :=
  (scalar_field 3 (by norm_num) (B := !![(1 : ℝ), 0; 0, -2])
      (by ext i j; fin_cases i <;> fin_cases j <;> simp)).2

/-- On the empty index type the coefficient `−1` is admissible: no sign condition on `C`. -/
theorem empty_index_negative_coefficient {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (H : Ω → Matrix (Fin 0) (Fin 0) ℝ) {B : Matrix (Fin 0) (Fin 0) ℝ} (hB : B.IsSymm) :
    Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤ (-1 : ℝ) * (B * B).trace := by
  refine symmetric_trace_integral_extension_mul ν H (fun i => Fin.elim0 i) (fun x => ?_)
    (fun A _ => ?_) hB
  · rw [show H x = 0 from Matrix.ext fun i => Fin.elim0 i]
    exact Matrix.PosSemidef.zero
  · simp only [Matrix.trace_fin_zero]
    exact ⟨integrable_zero _ _ _, by simp⟩

end MatrixTraceIntegralCoefficientAudit

#print axioms
  FunctionalInequalities.Analysis.symmetric_trace_integral_extension_mul_of_ae_posSemidef
#print axioms FunctionalInequalities.Analysis.symmetric_trace_integral_extension_mul
#print axioms FunctionalInequalities.Analysis.symmetric_trace_integral_extension
#print axioms FunctionalInequalities.Analysis.symmetric_trace_integral_extension_of_ae_posSemidef
#print axioms MatrixTraceIntegralCoefficientAudit.scalar_field
#print axioms MatrixTraceIntegralCoefficientAudit.indefinite_diag_three
#print axioms MatrixTraceIntegralCoefficientAudit.empty_index_negative_coefficient

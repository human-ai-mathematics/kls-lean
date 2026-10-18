import FunctionalInequalities.Analysis.Matrix.Integral

/-! Matrix integral calls with an indefinite symmetric matrix and a concrete PSD field. -/
noncomputable section
namespace Examples.MatrixIntegral
open MeasureTheory
open FunctionalInequalities.Analysis (symmetric_trace_integral_extension_mul)

private def signatureMatrix : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, -1]

-- A PSD estimate with any real C extends to this indefinite matrix, giving 2 * C.
example {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {C : ℝ}
    (H : Ω → Matrix (Fin 2) (Fin 2) ℝ)
    (hmeas : ∀ i j, Measurable (fun x => H x i j))
    (hpos : ∀ x, (H x).PosSemidef)
    (hPSD : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosSemidef →
      Integrable (fun x => (A * H x * A * H x).trace) ν ∧
        (∫ x, (A * H x * A * H x).trace ∂ν) ≤ C * (A * A).trace) :
    (∫ x, (signatureMatrix * H x * signatureMatrix * H x).trace ∂ν) ≤ 2 * C := by
  have h := symmetric_trace_integral_extension_mul ν H hmeas hpos hPSD
    (Matrix.isSymm_diagonal (![1, -1] : Fin 2 → ℝ))
  have htrace : (signatureMatrix * signatureMatrix).trace = 2 := by
    norm_num [signatureMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  have hb := h.2
  change (∫ x, (signatureMatrix * H x * signatureMatrix * H x).trace ∂ν) ≤ C * (signatureMatrix * signatureMatrix).trace at hb
  rw [htrace] at hb
  simpa only [mul_comm C 2] using hb

-- For H = Id and a probability law, the PSD premise is discharged with C = 1.
example {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] :
    (∫ _ : Ω, (signatureMatrix * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
      signatureMatrix * 1).trace ∂ν) ≤ (signatureMatrix * signatureMatrix).trace := by
  have hPSD : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosSemidef →
      Integrable (fun _ : Ω => (A * (1 : Matrix (Fin 2) (Fin 2) ℝ) * A * 1).trace) ν ∧
      (∫ _ : Ω, (A * (1 : Matrix (Fin 2) (Fin 2) ℝ) * A * 1).trace ∂ν) ≤
        (1 : ℝ) * (A * A).trace := by
    intro A _
    simp only [Matrix.mul_one]
    exact ⟨integrable_const _, by simp⟩
  simpa only [signatureMatrix, one_mul] using (symmetric_trace_integral_extension_mul ν (fun _ => 1)
    (fun _ _ => measurable_const) (fun _ => Matrix.PosSemidef.one) hPSD
    (Matrix.isSymm_diagonal (![1, -1] : Fin 2 → ℝ))).2

end Examples.MatrixIntegral

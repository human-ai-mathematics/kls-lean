import FunctionalInequalities.Analysis.Matrix.Integral
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Audit: trace energies of a symmetric matrix field under a probability law

Source: Letwin, arXiv:2607.24164v1, Theorem 2.5 (support only: the extension from positive
semidefinite to all symmetric `B`). An actual finite probability law and a nonconstant positive
semidefinite matrix field, with every premise derived: `ν = ½ δ_false + ½ δ_true` on `Bool` (total
mass `1`, nonzero), `H(false) = [[1, 1], [1, 1]]`, `H(true) = [[1, −1], [−1, 1]]` (rank one,
positive semidefinite, coordinate-measurable); the positive semidefinite bound
`∫ tr(A H A H) dν = (a + c)² + 4b² ≤ 2 tr(A²)` is proved for every positive semidefinite `A`; the
library theorem `symmetric_trace_integral_extension` is then invoked for every symmetric `C`; and
the indefinite `B = diag(1, −2)` (neither `B` nor `−B` positive semidefinite, commuting with
neither atom) has averaged trace energy `1`. A generic matrix-field client, not a moment-map or
source-law client.
-/

open Matrix MeasureTheory
open FunctionalInequalities.Analysis

namespace LetwinSymmetricIntegralAudit

/-- A genuine finite-measure client for the symmetric trace-integral extension. -/
theorem concrete_measure_matrix_client :
    letI : MeasurableSpace Bool := ⊤
    let ν : Measure Bool :=
      (1 / 2 : ENNReal) • Measure.dirac false +
        (1 / 2 : ENNReal) • Measure.dirac true
    let H : Bool → Matrix (Fin 2) (Fin 2) ℝ := fun x =>
      match x with
      | false => !![1, 1; 1, 1]
      | true => !![1, -1; -1, 1]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -2]
    ν Set.univ = (1 : ENNReal) ∧
      ν ≠ 0 ∧
      (∀ i j, Measurable (fun x => H x i j)) ∧
      (∀ x, (H x).PosSemidef) ∧
      (∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosSemidef →
        Integrable (fun x => (A * H x * A * H x).trace) ν ∧
          (∫ x, (A * H x * A * H x).trace ∂ν) ≤
            2 * (A * A).trace) ∧
      (∀ C : Matrix (Fin 2) (Fin 2) ℝ, C.IsSymm →
        Integrable (fun x => (C * H x * C * H x).trace) ν ∧
          (∫ x, (C * H x * C * H x).trace ∂ν) ≤
            2 * (C * C).trace) ∧
      B.IsSymm ∧ ¬ B.PosSemidef ∧ ¬ (-B).PosSemidef ∧
      H false ≠ H true ∧
      B * H false ≠ H false * B ∧
      B * H true ≠ H true * B ∧
      Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) = 1 := by
  let _ : MeasurableSpace Bool := ⊤
  let ν : Measure Bool :=
    (1 / 2 : ENNReal) • Measure.dirac false +
      (1 / 2 : ENNReal) • Measure.dirac true
  let H : Bool → Matrix (Fin 2) (Fin 2) ℝ := fun x =>
    match x with
    | false => !![1, 1; 1, 1]
    | true => !![1, -1; -1, 1]
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -2]
  let _ : IsFiniteMeasure ν := ⟨by simp [ν]⟩
  have hmass : ν Set.univ = (1 : ENNReal) := by
    simp [ν, ENNReal.inv_two_add_inv_two]
  have hνne : ν ≠ 0 := by
    intro h
    have hu := congrArg (fun μ : Measure Bool => μ Set.univ) h
    rw [hmass] at hu
    simp at hu
  have hcoord : ∀ i j, Measurable (fun x => H x i j) := by
    intro i j s hs
    simp
  have hHpsd : ∀ x, (H x).PosSemidef := by
    intro x
    cases x with
    | false =>
        rw [Matrix.posSemidef_iff_dotProduct_mulVec]
        refine ⟨?_, ?_⟩
        · change (H false).conjTranspose = H false
          rw [Matrix.conjTranspose_eq_transpose_of_trivial]
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
        · intro v
          simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
          nlinarith [sq_nonneg (v 0 + v 1)]
    | true =>
        rw [Matrix.posSemidef_iff_dotProduct_mulVec]
        refine ⟨?_, ?_⟩
        · change (H true).conjTranspose = H true
          rw [Matrix.conjTranspose_eq_transpose_of_trivial]
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
        · intro v
          simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
          nlinarith [sq_nonneg (v 0 - v 1)]
  have hfinite (f : Bool → ℝ) : Integrable f ν := by
    exact Integrable.of_finite
  have henergy (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsSymm) :
      (A * H false * A * H false).trace =
          (A 0 0 + A 1 1 + 2 * A 0 1)^2 ∧
      (A * H true * A * H true).trace =
          (A 0 0 + A 1 1 - 2 * A 0 1)^2 := by
    change A.transpose = A at hA
    have hab : A 1 0 = A 0 1 := by
      have hh := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hA
      simpa [Matrix.transpose_apply] using hh
    constructor
    · norm_num [H, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, hab]; ring
    · norm_num [H, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, hab]; ring
  have htraceAA (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsSymm) :
      (A * A).trace = A 0 0 ^ 2 + 2 * (A 0 1)^2 + A 1 1 ^ 2 := by
    change A.transpose = A at hA
    have hab : A 1 0 = A 0 1 := by
      have hh := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hA
      simpa [Matrix.transpose_apply] using hh
    norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, hab]; ring
  have hmeas_energy (A : Matrix (Fin 2) (Fin 2) ℝ) :
      Measurable (fun x => (A * H x * A * H x).trace) := by
    intro s hs
    simp
  have hint_formula (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsSymm) :
      (∫ x, (A * H x * A * H x).trace ∂ν) =
        (A 0 0 + A 1 1)^2 + 4 * (A 0 1)^2 := by
    have hf := hfinite (fun x => (A * H x * A * H x).trace)
    have he := henergy A hA
    have hf_false :
        Integrable (fun x => (A * H x * A * H x).trace)
          ((1 / 2 : ENNReal) • Measure.dirac false) := by
      have hf' :
          Integrable (fun x => (A * H x * A * H x).trace)
            ((1 / 2 : ENNReal) • Measure.dirac false +
              (1 / 2 : ENNReal) • Measure.dirac true) := by
        simpa only [ν] using hf
      exact hf'.left_of_add_measure
    have hf_true :
        Integrable (fun x => (A * H x * A * H x).trace)
          ((1 / 2 : ENNReal) • Measure.dirac true) := by
      have hf' :
          Integrable (fun x => (A * H x * A * H x).trace)
            ((1 / 2 : ENNReal) • Measure.dirac false +
              (1 / 2 : ENNReal) • Measure.dirac true) := by
        simpa only [ν] using hf
      exact hf'.right_of_add_measure
    calc
      (∫ x, (A * H x * A * H x).trace ∂ν) =
          ∫ x, (A * H x * A * H x).trace ∂
            ((1 / 2 : ENNReal) • Measure.dirac false +
              (1 / 2 : ENNReal) • Measure.dirac true) := by
        rfl
      _ = (∫ x, (A * H x * A * H x).trace ∂
            ((1 / 2 : ENNReal) • Measure.dirac false)) +
          ∫ x, (A * H x * A * H x).trace ∂
            ((1 / 2 : ENNReal) • Measure.dirac true) :=
        integral_add_measure hf_false hf_true
      _ = (1 / 2 : ENNReal).toReal •
            (∫ x, (A * H x * A * H x).trace ∂Measure.dirac false) +
          (1 / 2 : ENNReal).toReal •
            (∫ x, (A * H x * A * H x).trace ∂Measure.dirac true) := by
        rw [integral_smul_measure, integral_smul_measure]
      _ = (1 / 2 : ℝ) * (A * H false * A * H false).trace +
            (1 / 2 : ℝ) * (A * H true * A * H true).trace := by
        simp
      _ = (A 0 0 + A 1 1)^2 + 4 * (A 0 1)^2 := by
        rw [he.1, he.2]
        ring
  have hPSD : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosSemidef →
      Integrable (fun x => (A * H x * A * H x).trace) ν ∧
        (∫ x, (A * H x * A * H x).trace ∂ν) ≤ 2 * (A * A).trace := by
    intro A hA
    have hs : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian hA)
    refine ⟨hfinite _, ?_⟩
    rw [hint_formula A hs, htraceAA A hs]
    nlinarith [sq_nonneg (A 0 0 - A 1 1)]
  have hAllSymm : ∀ C : Matrix (Fin 2) (Fin 2) ℝ, C.IsSymm →
      Integrable (fun x => (C * H x * C * H x).trace) ν ∧
        (∫ x, (C * H x * C * H x).trace ∂ν) ≤ 2 * (C * C).trace := by
    intro C hC
    exact symmetric_trace_integral_extension ν H hcoord hHpsd hPSD hC
  have hB : B.IsSymm := by
    change B.transpose = B
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hBnotP : ¬ B.PosSemidef := by
    intro h
    have hd := h.diag_nonneg (i := (1 : Fin 2))
    norm_num [B] at hd
  have hBnotN : ¬ (-B).PosSemidef := by
    intro h
    have hd := h.diag_nonneg (i := (0 : Fin 2))
    norm_num [B] at hd
  have hnonconst : H false ≠ H true := by
    intro h
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [H] at hh
  have hcomm0 : B * H false ≠ H false * B := by
    intro h
    have hh := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [B, H, Matrix.mul_apply, Fin.sum_univ_succ] at hh
  have hcomm1 : B * H true ≠ H true * B := by
    intro h
    have hh := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [B, H, Matrix.mul_apply, Fin.sum_univ_succ] at hh
  have hBext := hAllSymm B hB
  have hBavg : (∫ x, (B * H x * B * H x).trace ∂ν) = 1 := by
    calc
      (∫ x, (B * H x * B * H x).trace ∂ν) =
          (B 0 0 + B 1 1)^2 + 4 * (B 0 1)^2 := hint_formula B hB
      _ = 1 := by
        norm_num [B]
  exact ⟨hmass, hνne, hcoord, hHpsd, hPSD, hAllSymm, hB, hBnotP,
    hBnotN, hnonconst, hcomm0, hcomm1, hBext.1, hBavg⟩

end LetwinSymmetricIntegralAudit

#print axioms FunctionalInequalities.Analysis.symmetric_trace_integral_extension
#print axioms LetwinSymmetricIntegralAudit.concrete_measure_matrix_client

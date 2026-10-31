module

public import FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
public import FunctionalInequalities.Analysis.Matrix.DeterminantInequalities

noncomputable section
open Matrix
namespace LetwinDeterminantContactAudit
open FunctionalInequalities.Analysis

private def shear : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]
private def reference : Matrix (Fin 2) (Fin 2) ℝ := shearᴴ * shear
private def singular : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1, 0]

private theorem reference_posDef : reference.PosDef := by
  have hunit : IsUnit shear := (Matrix.isUnit_iff_isUnit_det shear).mpr (by
    norm_num [shear, Matrix.det_fin_two])
  exact Matrix.PosDef.conjTranspose_mul_self shear (Matrix.mulVec_injective_of_isUnit hunit)

private theorem reference_det : reference.det = 1 := by
  norm_num [reference, shear, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fin_two]

private theorem singular_posSemidef : singular.PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num

/-- A genuine singular/noncommuting pair; the proof does not specialize to
simultaneously diagonal matrices. -/
theorem singular_noncommutes : singular * reference ≠ reference * singular := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [singular, reference, shear, Matrix.mul_apply, Fin.sum_univ_two] at hh

theorem singular_det_zero : singular.det = 0 := by
  norm_num [singular, Matrix.det_diagonal, Fin.prod_univ_two]

theorem singular_minkowski :
    Real.rpow singular.det (1 / (2 : ℝ)) + Real.rpow reference.det (1 / (2 : ℝ)) ≤
      Real.rpow (singular + reference).det (1 / (2 : ℝ)) := by
  apply det_root_add_le (by norm_num) singular_posSemidef reference_posDef.posSemidef
  simpa only [add_comm] using reference_posDef.add_posSemidef singular_posSemidef

/-- The exact residual bound for a concrete non-diagonal unit-determinant
reference and an actual varying PSD residual; epsilon/delta are not replaced
by loose constants. -/
theorem noncommuting_residual_bound {a δ ε : ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 ≤ ε)
    (hdet : (diagonal ![a, 2 * a] + (1 - δ) • reference).det ≤ (1 + ε) ^ 2) :
    2 * a ^ 2 ≤ (ε + δ) ^ 2 := by
  have hA : (diagonal ![a, 2 * a]).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i
    · exact ha
    · exact mul_nonneg (by norm_num) ha
  have hh := det_le_pow_of_det_add_smul_le (by norm_num : 0 < 2)
    hA reference_posDef reference_det hδ hδ1 hε hdet
  convert hh using 1
  simp
  ring

/-- The positive-dimensional consumer includes n=1, with actual scalar matrix
and determinant identities. -/
theorem one_dimensional_bound {a δ ε : ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 ≤ ε) (hdet : a + (1 - δ) ≤ 1 + ε) :
    a ≤ ε + δ := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := diagonal (fun _ => a)
  have hA : A.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun _ => ha)
  have hh := det_le_pow_of_det_add_smul_le (by norm_num : 0 < 1)
    hA (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef)
    Matrix.det_one hδ hδ1 hε (by
      simpa [A, Matrix.det_fin_one] using hdet)
  simpa [A, Matrix.det_fin_one] using hh

end LetwinDeterminantContactAudit
#print axioms FunctionalInequalities.Analysis.det_root_le_trace_div
#print axioms FunctionalInequalities.Analysis.det_root_add_le
#print axioms FunctionalInequalities.Analysis.det_le_pow_of_det_add_smul_le
#print axioms LetwinDeterminantContactAudit.singular_noncommutes
#print axioms LetwinDeterminantContactAudit.singular_det_zero
#print axioms LetwinDeterminantContactAudit.singular_minkowski
#print axioms LetwinDeterminantContactAudit.noncommuting_residual_bound
#print axioms LetwinDeterminantContactAudit.one_dimensional_bound

namespace LetwinDeterminantContactAudit
open FunctionalInequalities.Analysis Filter
open scoped Matrix.Norms.Elementwise Topology

/-- A genuinely varying positive definite determinant-one path, with both
linearized identities generated from its real determinant equation. -/
theorem actual_exp_diagonal_path :
    ∃ M : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      ContDiff ℝ 2 M ∧
        (∀ t, (M t).det = 1) ∧
          (∀ t, (M t).PosDef) ∧
            M 0 ≠ M 1 ∧
              (∀ v : ℝ, ((M 0)⁻¹ * fderiv ℝ M 0 v).trace = 0) ∧
                ∀ v w : ℝ,
                  ((M 0)⁻¹ * fderiv ℝ (fun y => fderiv ℝ M y w) 0 v).trace =
                    ((M 0)⁻¹ * fderiv ℝ M 0 v * (M 0)⁻¹ * fderiv ℝ M 0 w).trace := by
  let M : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => !![Real.exp t, 0; 0, Real.exp (-t)]
  have hM : ContDiff ℝ 2 M := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> dsimp [M] <;> fun_prop
  have hdet (t : ℝ) : (M t).det = 1 := by
    simp only [M, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, sub_zero]
    rw [← Real.exp_add]
    simp
  have hPD (t : ℝ) : (M t).PosDef := by
    have he :
      M t = Matrix.diagonal (fun i : Fin 2 => if i = 0 then Real.exp t else Real.exp (-t)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [M, Matrix.diagonal]
    rw [he, Matrix.posDef_diagonal_iff]
    intro i
    split_ifs <;> exact Real.exp_pos _
  have hne : M 0 ≠ M 1 := by
    intro he
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) he
    have hp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    norm_num [M] at h
    linarith
  obtain ⟨hfirst, hsecond⟩ :=
    trace_identities_of_eventually_det_const hM.contDiffAt (by norm_num : (1 : ℝ) ≠ 0)
      (Filter.Eventually.of_forall hdet) (x := 0)
  exact ⟨M, hM, hdet, hPD, hne, hfirst, hsecond⟩

/-- Empty-index matrices have determinant ONE, and the SAME generic calculus
produces both identities; no nonempty-index or mass assertion is inserted. -/
theorem actual_empty_matrix :
    (∀ v : ℝ,
        (((0 : Matrix (Fin 0) (Fin 0) ℝ))⁻¹ *
              fderiv ℝ (fun _ : ℝ => (0 : Matrix (Fin 0) (Fin 0) ℝ)) 0 v).trace =
          0) ∧
      ∀ v w : ℝ,
        ((0 : Matrix (Fin 0) (Fin 0) ℝ)⁻¹ *
              fderiv ℝ (fun y => fderiv ℝ (fun _ : ℝ => (0 : Matrix (Fin 0) (Fin 0) ℝ)) y w) 0
                v).trace =
          ((0 : Matrix (Fin 0) (Fin 0) ℝ)⁻¹ *
                  fderiv ℝ (fun _ : ℝ => (0 : Matrix (Fin 0) (Fin 0) ℝ)) 0 v *
                (0 : Matrix (Fin 0) (Fin 0) ℝ)⁻¹ *
              fderiv ℝ (fun _ : ℝ => (0 : Matrix (Fin 0) (Fin 0) ℝ)) 0 w).trace := by
  exact
    trace_identities_of_eventually_det_const (M := fun _ : ℝ => (0 : Matrix (Fin 0) (Fin 0) ℝ))
      (x := (0 : ℝ)) contDiffAt_const (by norm_num : (1 : ℝ) ≠ 0)
      (Filter.Eventually.of_forall (fun _ => Matrix.det_isEmpty))

end LetwinDeterminantContactAudit
set_option pp.fullNames true in
#print axioms LetwinDeterminantContactAudit.actual_exp_diagonal_path
set_option pp.fullNames true in
#print axioms LetwinDeterminantContactAudit.actual_empty_matrix

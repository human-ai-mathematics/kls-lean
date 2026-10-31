module

public import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
public import FunctionalInequalities.Analysis.Cutoff.Profile

/-!
# Audit: Letwin Lemma A.4 coefficient extraction, energy identity and pointwise defect domination

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17). Actual clients, every premise derived here:
- `square_extraction`: the coefficient extraction for `h(s) = s²` in an arbitrary orthonormal basis,
  `Σ_ij A_ij ∂_iφ ∂_j(φ²) = 2φ Σ_ij A_ij ∂_iφ ∂_jφ`;
- `profile_defect_le`: the pointwise defect domination for the actual profile `η = smoothTransition
  (2 − ·)` with the
  fixed common bound `B` of `η′`, `η″` and the nonnegativity of the inverse-Hessian quadratic form,
  i.e. the source
  form `|Lχ| ≤ |R⁻¹| B |Lφ| + R⁻² B Γφ` with `Γφ ≥ 0` for every real `c`, `R`;
- `energy_nonneg_of_deriv_nonpos`: the energy identity with the quadratic-form sign: for `h′ ≤ 0`
  (the sign of the tail
  primitive `q_R′ = −R⁻² w`), `∫ (Lφ) h(φ) dν ≥ 0`.
These are not the Lemma A.4 producer, its compact-support assembly or a source-law client.
-/

@[expose] public section

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff

namespace A4EnergyDefectClient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Coefficient extraction for `h(s) = s²` in an arbitrary orthonormal basis. -/
theorem square_extraction {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E) :
    (∑ i,
        ∑ j,
          inverseHessianEntry φ b x i j * fderiv ℝ φ x (b i) *
            fderiv ℝ (fun y => φ y ^ 2) x (b j)) =
      2 * φ x *
        ∑ i, ∑ j, inverseHessianEntry φ b x i j * fderiv ℝ φ x (b i) * fderiv ℝ φ x (b j) := by
  have hsq : ContDiff ℝ ∞ (fun s : ℝ => s ^ 2) := contDiff_id.pow 2
  rw [sum_inverseHessianEntry_mul_fderiv_comp b hφ hsq x]
  congr 1
  simp

/-- Pointwise defect domination for the actual profile `η`, in the source form with `Γφ ≥ 0`. -/
theorem profile_defect_le {φ V : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ c R : ℝ,
          ∀ x : E,
            |hessianInverseOperator φ V (fun y => Real.smoothTransition (2 - (φ y - c) / R))
                  x| ≤
              |R⁻¹| * B * |hessianInverseOperator φ V φ x| +
                (R⁻¹) ^ 2 * B *
                  ∑ i,
                    ∑ j,
                      inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                          fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                        fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) := by
  obtain ⟨hη, -, -, -, -, -, -, -, B, hB0, hB⟩ := smoothTransition_two_sub_cutoff
  refine ⟨B, hB0, fun c R x => ?_⟩
  have he : ContDiff ℝ 2 (fun s : ℝ => Real.smoothTransition (2 - s)) :=
    hη.of_le (WithTop.coe_le_coe.mpr le_top)
  have h := abs_hessianInverseOperator_comp_sub_div_le (V := V) hφ he c R x
  have hΓ :
    0 ≤
      ∑ i,
        ∑ j,
          inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
              fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
            fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) :=
    sum_inverseHessianEntry_mul_mul_nonneg (stdOrthonormalBasis ℝ E) hφ x (hPD x) _
  have h1 := (hB ((φ x - c) / R)).1
  have h2 := (hB ((φ x - c) / R)).2
  refine h.trans ?_
  rw [abs_of_nonneg hΓ, abs_mul]
  gcongr

section Energy

variable [MeasurableSpace E] [BorelSpace E]

/-- The energy identity with the quadratic-form sign: `h′ ≤ 0` gives `∫ (Lφ) h(φ) dν ≥ 0`. -/
theorem energy_nonneg_of_deriv_nonpos (m : Measure E) [m.IsAddHaarMeasure] {φ V : E → ℝ}
    {h : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport (fun x => h (φ x))) {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ ∞ V U) (hRange : Set.range (gradient φ) ⊆ U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) (hmono : ∀ s, deriv h s ≤ 0) :
    0 ≤ ∫ x, hessianInverseOperator φ V φ x * h (φ x) ∂(m.tilted (-φ)) := by
  rw [integral_hessianInverseOperator_self_mul_comp_eq_neg m hφ hh hc hU hV hRange hMA hPD
      hnorm,
    neg_nonneg]
  apply integral_nonpos
  intro x
  exact
    mul_nonpos_of_nonpos_of_nonneg (hmono _)
      (sum_inverseHessianEntry_mul_mul_nonneg _ (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) x
        (hPD x) _)

end Energy

end A4EnergyDefectClient

#print axioms FunctionalInequalities.Analysis.BakryEmery.sum_inverseHessianEntry_mul_fderiv_comp
#print axioms FunctionalInequalities.Analysis.BakryEmery.abs_hessianInverseOperator_comp_sub_div_le
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.integral_hessianInverseOperator_self_mul_comp_eq_neg
#print axioms A4EnergyDefectClient.square_extraction
#print axioms A4EnergyDefectClient.profile_defect_le
#print axioms A4EnergyDefectClient.energy_nonneg_of_deriv_nonpos

module

public import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
public import FunctionalInequalities.Analysis.Cutoff.Profile

/-!
# Audit: Letwin Lemma A.4 weighted energy bound

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17). Actual clients of
`integrable_and_neg_integral_deriv_comp_mul_le`, with the source hypotheses of Lemma A.4 and no
assumed energy:
- `exists_energy_bound`: from the source data (gradient image in a bounded `K`, `V` smooth on an
  open `U ⊇ closure K`, Monge–Ampère, positive definite Hessian, normalization) a constant `D ≥ 0`
  is DERIVED (bounded self-generator) such that every smooth `h` with `h ∘ φ` compactly supported
  and `|h| ≤ M` gives integrability and `−∫ h′(φ) Γφ dν ≤ D M`;
- `energy_term_nonneg_le`: for `h′ ≤ 0` (the sign of the tail primitive) the energy term lies in
  `[0, D M]`;
- `primitive_energy_le`: for the actual tail primitive `q_R` of a smooth nonnegative `w` vanishing
  off `(0, 3)`, the source energy term `R⁻² w(φ/R) Γφ` is integrable with
  `∫ R⁻² w(φ/R) Γφ dν ≤ D R⁻¹ ∫_0^3 w`, given that `q_R ∘ φ` is compactly supported.
These are not the Lemma A.4 producer or a source-law client.
-/

@[expose] public section

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff

namespace A4WeightedEnergyClient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/--
The energy bound with a constant `D` derived from the source hypotheses (bounded self-generator). -/
theorem exists_energy_bound (m : Measure E) [m.IsAddHaarMeasure] {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {K U : Set E} (hK : Bornology.IsBounded K)
    (hRange : Set.range (gradient φ) ⊆ K) (hU : IsOpen U) (hKU : closure K ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    ∃ D : ℝ,
      0 ≤ D ∧
        ∀ (h : ℝ → ℝ) (M : ℝ),
          ContDiff ℝ ∞ h →
            HasCompactSupport (fun x => h (φ x)) →
              (∀ t, |h t| ≤ M) →
                Integrable
                    (fun x =>
                      deriv h (φ x) *
                        ∑ i,
                          ∑ j,
                            inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                                fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                              fderiv ℝ φ x (stdOrthonormalBasis ℝ E j))
                    (m.tilted (-φ)) ∧
                  -(∫ x,
                        deriv h (φ x) *
                          ∑ i,
                            ∑ j,
                              inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                                  fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                                fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ))) ≤
                    D * M := by
  obtain ⟨D, hD0, hD⟩ :=
    bounded_hessianInverseOperator_self (V := V) (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hPD
      hK hRange hU hKU (hV.of_le (WithTop.coe_le_coe.mpr le_top))
  refine ⟨D, hD0, fun h M hh hc hM => ?_⟩
  exact
    integrable_and_neg_integral_deriv_comp_mul_le m hφ hh hc hU hV
      (hRange.trans (subset_closure.trans hKU)) hMA hPD hnorm hD hM

/-- For `h′ ≤ 0` the energy term lies in `[0, D M]`. -/
theorem energy_term_nonneg_le (m : Measure E) [m.IsAddHaarMeasure] {φ V : E → ℝ} {h : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport (fun x => h (φ x)))
    {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U) (hRange : Set.range (gradient φ) ⊆ U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) {D M : ℝ}
    (hD : ∀ x, |hessianInverseOperator φ V φ x| ≤ D) (hM : ∀ t, |h t| ≤ M)
    (hmono : ∀ s, deriv h s ≤ 0) :
    0 ≤
        -(∫ x,
            deriv h (φ x) *
              ∑ i,
                ∑ j,
                  inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                      fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                    fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ))) ∧
      -(∫ x,
            deriv h (φ x) *
              ∑ i,
                ∑ j,
                  inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                      fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                    fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ))) ≤
        D * M := by
  refine
    ⟨neg_nonneg.mpr
        (integral_nonpos fun x =>
          mul_nonpos_of_nonpos_of_nonneg (hmono _)
            (sum_inverseHessianEntry_mul_mul_nonneg _ (hφ.of_le (WithTop.coe_le_coe.mpr le_top))
              x (hPD x) _)),
      ?_⟩
  exact
    (integrable_and_neg_integral_deriv_comp_mul_le m hφ hh hc hU hV hRange hMA hPD hnorm hD
        hM).2

/-- The source energy term for the actual tail primitive `q_R`. -/
theorem primitive_energy_le (m : Measure E) [m.IsAddHaarMeasure] {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hRange : Set.range (gradient φ) ⊆ U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) {D : ℝ}
    (hD : ∀ x, |hessianInverseOperator φ V φ x| ≤ D) {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hw0 : ∀ t, 0 ≤ w t) (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R)
    (hc : HasCompactSupport (fun x => R⁻¹ * ∫ s in φ x / R..3, w s)) :
    Integrable
        (fun x =>
          (R ^ 2)⁻¹ * w (φ x / R) *
            ∑ i,
              ∑ j,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                    fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                  fderiv ℝ φ x (stdOrthonormalBasis ℝ E j))
        (m.tilted (-φ)) ∧
      (∫ x,
          (R ^ 2)⁻¹ * w (φ x / R) *
            ∑ i,
              ∑ j,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                    fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                  fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ))) ≤
        D * (R⁻¹ * ∫ s in (0 : ℝ)..3, w s) := by
  obtain ⟨hq, hq', hq0, hqle, -⟩ := inv_mul_intervalIntegral_div_three_cutoff hw hw0 hws hR
  have hM : ∀ t, |R⁻¹ * ∫ s in t / R..3, w s| ≤ R⁻¹ * ∫ s in (0 : ℝ)..3, w s := fun t => by
    rw [abs_of_nonneg (hq0 t)]
    exact hqle t
  obtain ⟨hi, hb⟩ :=
    integrable_and_neg_integral_deriv_comp_mul_le m hφ hq hc hU hV hRange hMA hPD hnorm hD hM
  simp only [hq', neg_mul, integral_neg, neg_neg] at hi hb
  exact ⟨hi.fun_neg.congr (Filter.Eventually.of_forall fun x => by simp), hb⟩

end A4WeightedEnergyClient

#print axioms
  FunctionalInequalities.Analysis.BakryEmery.integrable_and_neg_integral_deriv_comp_mul_le
#print axioms A4WeightedEnergyClient.exists_energy_bound
#print axioms A4WeightedEnergyClient.energy_term_nonneg_le
#print axioms A4WeightedEnergyClient.primitive_energy_le

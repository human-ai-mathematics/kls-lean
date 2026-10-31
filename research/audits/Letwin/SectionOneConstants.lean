module

public import FunctionalInequalities.KLS.Geometry.Cheeger.Comparison
public import FunctionalInequalities.KLS.Letwin.IsoperimetricBound

/-!
# Audit client for Letwin arXiv:2607.24164v1, Section 1 constants

Clients state Letwin's displays on `EuclideanSpace ℝ (Fin n)` with Lebesgue measure: the Poincaré
constant of Equation (1.1) with unit-energy locally Lipschitz tests and no `L²` premise, the
smooth-boundary isoperimetric constant `ψ_μ`, the comparison display `1/4 ≤ ψ_μ² / C_P(μ) ≤ π`
under the KLS proposition and unconditionally (the KLS proposition discharged by the proved
dimension-free bound), and both forms of the KLS conjecture.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
namespace LetwinSectionOneConstantsAudit
open FunctionalInequalities FunctionalInequalities.KLS

/-- Letwin's comparison display with both constants written as in Section 1: `C_P(μ)` from
Equation (1.1) and `ψ_μ` from the smooth-boundary infimum, for a log-concave law with a Borell
density on `ℝⁿ`, `n ≥ 1`, assuming the KLS proposition for finiteness of `C_P`. -/
theorem comparison_client (hKLS : Conjecture) {n : ℕ} (hn : n ≠ 0)
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : LogConcave μ)
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : IsBorellDensity (μ : Measure (EuclideanSpace ℝ (Fin n))) volume ρ) :
    4⁻¹ ≤
        (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ ^ 2 /
          (⨅ C :
            { C : NNReal //
              ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
                LocallyLipschitz g →
                  ∫⁻ x,
                        (ENNReal.ofReal ‖gradient g x‖) ^
                          2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
                      1 →
                    evariance g (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
                      (C : ENNReal) *
                        ∫⁻ x,
                          (ENNReal.ofReal ‖gradient g x‖) ^
                            2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) },
            (C.1 : ENNReal)) ∧
      (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ ^ 2 /
          (⨅ C :
            { C : NNReal //
              ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
                LocallyLipschitz g →
                  ∫⁻ x,
                        (ENNReal.ofReal ‖gradient g x‖) ^
                          2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
                      1 →
                    evariance g (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
                      (C : ENNReal) *
                        ∫⁻ x,
                          (ENNReal.ofReal ‖gradient g x‖) ^
                            2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) },
            (C.1 : ENNReal)) ≤
        ENNReal.ofReal Real.pi := by
  have hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume := by
    rw [← hρ.withDensity_eq]
    exact withDensity_absolutelyContinuous _ _
  have h := (hμ.inv_smoothConstant_univ_sq_div_literatureConstant_mem_Icc hKLS hn hρ).2.2
  rw [hμ.localSlope_constant_eq_ambient_gradient volume hac] at h
  exact h

/-- Letwin's comparison display, unconditionally: `0 < C_P(μ) < ∞` and
`1/4 ≤ ψ_μ² / C_P(μ) ≤ π`, with `C_P(μ)` the infimum of Equation (1.1) and `ψ_μ` the inverse of the
smooth-boundary infimum, for every log-concave law with a Borell density on `ℝⁿ`, `n ≥ 1`. -/
theorem comparison_unconditional_client {n : ℕ} (hn : n ≠ 0)
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : LogConcave μ)
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : IsBorellDensity (μ : Measure (EuclideanSpace ℝ (Fin n))) volume ρ) :
    let CP := ⨅ C : {C : NNReal // ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz g →
        ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ 1 →
        evariance g (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
          (C : ENNReal) *
            ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))},
      (C.1 : ENNReal)
    0 < CP ∧ CP < ⊤ ∧ 4⁻¹ ≤ (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ ^ 2 / CP ∧
      (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ ^ 2 / CP ≤ ENNReal.ofReal Real.pi := by
  intro CP
  have hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume := by
    rw [← hρ.withDensity_eq]
    exact withDensity_absolutelyContinuous _ _
  have h := hμ.inverseScale_sq_div_literatureConstant_mem_Icc hn hρ
  rw [hμ.localSlope_constant_eq_ambient_gradient volume hac,
    Isoperimetry.inverseScale_eq_inv_smoothConstant_univ hρ] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- `ψ_μ` in the ambient smooth-boundary convention is the library inverse scale. -/
theorem psi_client {n : ℕ} {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : IsBorellDensity (μ : Measure (EuclideanSpace ℝ (Fin n))) volume ρ) :
    Isoperimetry.inverseScale μ = (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ :=
  Isoperimetry.inverseScale_eq_inv_smoothConstant_univ hρ

/-- Both equivalent forms of the KLS conjecture, and `C_P ≥ 1` for isotropic laws. -/
theorem conjecture_client :
    (Conjecture ↔ ∃ C : NNReal, ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      LogConcave μ → Isotropic μ → Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal)) ∧
    (Conjecture ↔ ∃ C : NNReal, ∀ n : ℕ, 2 ≤ n →
      (⨆ (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (_ : LogConcave μ)
        (_ : Isotropic μ), Isoperimetry.inverseScale μ) ≤ (C : ENNReal)) ∧
    ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin (n + 1)))), LogConcave μ →
      Isotropic μ → 1 ≤ Poincare.LocalSlope.Intrinsic.constant μ :=
  ⟨conjecture_iff_isotropic, conjecture_iff_inverseScale,
    fun _ _ hμ hiso ↦ hμ.one_le_localSlope_constant hiso⟩

end LetwinSectionOneConstantsAudit

#print axioms FunctionalInequalities.Poincare.LocalSlope.Holds.memLp_two
#print axioms FunctionalInequalities.Poincare.LocalSlope.holds_iff_lintegral_gradient_le_one
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_constant_eq_ambient_gradient
#print axioms FunctionalInequalities.KLS.LogConcave.one_le_localSlope_constant
#print axioms FunctionalInequalities.KLS.conjecture_iff_isotropic
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_mono
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_univ_le_minkowskiConstant
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_le_minkowskiConstant
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant_univ
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_eq_of_isometryEquiv
#print axioms FunctionalInequalities.KLS.Isoperimetry.constant_eq_minkowskiConstant
#print axioms FunctionalInequalities.KLS.Isoperimetry.constant_eq_smoothConstant_univ
#print axioms FunctionalInequalities.KLS.Isoperimetry.inverseScale_eq_inv_smoothConstant_univ
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_constant_pos_of_affineSupport_eq_top
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_constant_lt_top_of_conjecture
#print axioms
  FunctionalInequalities.KLS.LogConcave.literatureConstant_le_four_mul_inv_smoothConstant_univ_sq
#print axioms FunctionalInequalities.KLS.LogConcave.inv_smoothConstant_univ_sq_le_pi_literature
#print axioms
  FunctionalInequalities.KLS.LogConcave.inv_smoothConstant_univ_sq_div_literatureConstant_mem_Icc
#print axioms FunctionalInequalities.KLS.LogConcave.inverseScale_sq_div_literatureConstant_mem_Icc
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_four_of_isotropic_fin_one
#print axioms FunctionalInequalities.KLS.conjecture_iff_inverseScale
#print axioms LetwinSectionOneConstantsAudit.comparison_client
#print axioms LetwinSectionOneConstantsAudit.comparison_unconditional_client
#print axioms LetwinSectionOneConstantsAudit.psi_client
#print axioms LetwinSectionOneConstantsAudit.conjecture_client

import FunctionalInequalities.Probability.Line.PrekopaEquality

/-! Client of the equality case of the midpoint Prekopa--Leindler inequality on the line. -/
noncomputable section
namespace LetwinPrekopaEqualityAudit
open MeasureTheory FunctionalInequalities.Probability.Line

/-- Three continuous positive densities of mass one with the midpoint inequality and
`∫ h ≤ 1`: the second is a translate of the first, and equals it when the means agree. -/
theorem translate_client {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ x, 0 < f x) (hg0 : ∀ y, 0 < g y)
    (hfi : Integrable f) (hhi : Integrable h) (hf1 : Integrable fun x ↦ x * f x)
    (hfm : ∫ x, f x = 1) (hgm : ∫ y, g y = 1) (hhm : ∫ z, h z ≤ 1)
    (hfgh : ∀ x y, Real.sqrt (f x * g y) ≤ h ((x + y) / 2)) :
    (∃ c : ℝ, ∀ y, g y = f (y - c)) ∧
      ((∫ y, y * g y = ∫ x, x * f x) → g = f) :=
  ⟨exists_eq_comp_sub_of_midpoint_le hf hg hf0 hg0 hfi hhi (hgm.trans hfm.symm)
      (hhm.trans hfm.ge) hfgh,
    eq_of_midpoint_le_of_integral_mul_eq hf hg hf0 hg0 hfi hhi hf1 (hgm.trans hfm.symm)
      (hhm.trans hfm.ge) hfgh⟩

end LetwinPrekopaEqualityAudit
#print axioms FunctionalInequalities.Probability.Line.exists_eq_comp_sub_of_midpoint_le
#print axioms FunctionalInequalities.Probability.Line.eq_of_midpoint_le_of_integral_mul_eq
#print axioms LetwinPrekopaEqualityAudit.translate_client

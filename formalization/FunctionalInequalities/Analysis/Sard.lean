import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Low-dimensional Sard theorem

The critical values of a real-valued `C^n` function are null when the domain has
dimension `n ≤ 1`. This independent base case does not establish general Sard.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Analysis

universe v

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Sard's theorem in dimensions zero and one, with `C^0` and `C^1` regularity,
respectively. No measure structure on the domain or measurability of the critical
set is required. -/
theorem sard_of_finrank_le_one {u : V → ℝ}
    (hdim : Module.finrank ℝ V ≤ 1)
    (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with hzero | hpos
  · have : Subsingleton V := Module.finrank_zero_iff.mp hzero
    apply measure_mono_null (t := {u 0})
    · rintro _ ⟨x, _, rfl⟩
      simp [Subsingleton.elim x 0]
    · simp
  · have hone : Module.finrank ℝ V = 1 := by omega
    let e : ℝ ≃L[ℝ] V := ContinuousLinearEquiv.ofFinrankEq (by simp [hone])
    let f : ℝ → ℝ := u ∘ e
    let S : Set ℝ := {z | fderiv ℝ u (e z) = 0}
    have hdiff : Differentiable ℝ u := hu.differentiable (by simp [hone])
    have hf : ∀ z ∈ S, HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) z := by
      intro z hz
      have hz' : fderiv ℝ u (e z) = 0 := hz
      simpa [f, hz'] using (hdiff (e z)).hasFDerivAt.comp z e.hasFDerivAt
    have hnull : (volume : Measure ℝ) (f '' S) = 0 :=
      addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
        (fun z hz ↦ (hf z hz).hasFDerivWithinAt) (by intro z hz; simp)
    have himage : f '' S = u '' {x | fderiv ℝ u x = 0} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨e z, hz, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨e.symm x, ?_, ?_⟩
        · simpa [S] using hx
        · simp [f]
    rw [himage] at hnull
    exact hnull

end FunctionalInequalities.Analysis

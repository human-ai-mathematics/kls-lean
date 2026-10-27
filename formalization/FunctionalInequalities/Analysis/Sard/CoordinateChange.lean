import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Replacing one coordinate by a scalar function

The differential of a coordinate replacement is invertible when the scalar
function has a nonzero derivative in the replaced coordinate. These tools are
shared by the finite-regularity and smooth real-product Sard charts. They use
the ordinary product norm and impose no measure or critical-set assumptions.
The regularity lemma applies to finite, smooth and analytic orders alike.
-/

noncomputable section
open scoped ContDiff

namespace FunctionalInequalities.Analysis.Sard.CoordinateChange

variable {n : ℕ}

/-- Replacing the `i`-th coordinate by `w` keeps the differentiability class. -/
theorem contDiff_update {k : ℕ∞ω} (i : Fin (n + 1)) {w : (Fin (n + 1) → ℝ) → ℝ}
    (hw : ContDiff ℝ k w) : ContDiff ℝ k (fun x => Function.update x i (w x)) := by
  rw [contDiff_pi]
  intro m
  rcases eq_or_ne m i with rfl | hm
  · simpa using hw
  · simpa [Function.update_apply, hm] using contDiff_apply ℝ ℝ m

/-- The differential of that chart. -/
theorem hasFDerivAt_update (i : Fin (n + 1)) {w : (Fin (n + 1) → ℝ) → ℝ}
    (hw : Differentiable ℝ w) (x : Fin (n + 1) → ℝ) :
    HasFDerivAt (fun x => Function.update x i (w x))
      (ContinuousLinearMap.pi fun m => if m = i then fderiv ℝ w x
        else ContinuousLinearMap.proj m) x := by
  refine hasFDerivAt_pi'' fun m => ?_
  rw [ContinuousLinearMap.proj_pi]
  rcases eq_or_ne m i with rfl | hm
  · simpa using (hw x).hasFDerivAt
  · simpa [Function.update_apply, hm] using hasFDerivAt_apply (𝕜 := ℝ) m x

/-- That differential is injective as soon as `w` really depends on the `i`-th coordinate. -/
private lemma injective_updateDeriv (i : Fin (n + 1)) {α : (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    (hα : α (Pi.single i (1 : ℝ)) ≠ 0) :
    Function.Injective (ContinuousLinearMap.pi fun m : Fin (n + 1) =>
      if m = i then α else ContinuousLinearMap.proj m) := by
  intro v₁ v₂ hv
  rw [← sub_eq_zero]
  set v : Fin (n + 1) → ℝ := v₁ - v₂ with hvdef
  have h0 : (ContinuousLinearMap.pi fun m : Fin (n + 1) =>
      if m = i then α else ContinuousLinearMap.proj m) v = 0 := by
    rw [hvdef, map_sub, hv, sub_self]
  have hoff : ∀ m, m ≠ i → v m = 0 := by
    intro m hm
    have := congrFun h0 m
    simpa [ContinuousLinearMap.pi_apply, hm] using this
  have hsingle : v = v i • Pi.single i (1 : ℝ) := by
    funext m
    rcases eq_or_ne m i with rfl | hm
    · simp
    · simp [hoff m hm, hm]
  have hαv : α v = 0 := by
    have := congrFun h0 i
    simpa [ContinuousLinearMap.pi_apply] using this
  rw [hsingle, map_smul, smul_eq_mul] at hαv
  have hvi : v i = 0 := by
    rcases mul_eq_zero.mp hαv with h | h
    · exact h
    · exact absurd h hα
  rw [hsingle, hvi, zero_smul]

/-- The straightening differential is a linear equivalence wherever `w` really depends on the
`i`-th coordinate. -/
theorem exists_updateEquiv (i : Fin (n + 1)) {α : (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    (hα : α (Pi.single i (1 : ℝ)) ≠ 0) :
    ∃ Le : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ),
      (Le : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) =
        ContinuousLinearMap.pi fun m : Fin (n + 1) =>
          if m = i then α else ContinuousLinearMap.proj m := by
  refine ⟨(LinearEquiv.ofInjectiveEndo _ (injective_updateDeriv i hα)).toContinuousLinearEquiv, ?_⟩
  ext v m
  rfl


end FunctionalInequalities.Analysis.Sard.CoordinateChange

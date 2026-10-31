module

public import FunctionalInequalities.Analysis.Sard.CoordinateChange
public import Lean
meta import Lean

@[expose] public section

open FunctionalInequalities.Analysis
open scoped ContDiff

namespace SardCoordinateChangeAudit

theorem finite_order {n k : ℕ} (i : Fin (n + 1)) {w : (Fin (n + 1) → ℝ) → ℝ}
    (hw : ContDiff ℝ k w) : ContDiff ℝ k (fun x => Function.update x i (w x)) :=
  Sard.CoordinateChange.contDiff_update i hw

theorem smooth_order {n : ℕ} (i : Fin (n + 1)) {w : (Fin (n + 1) → ℝ) → ℝ}
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (fun x => Function.update x i (w x)) :=
  Sard.CoordinateChange.contDiff_update i hw

theorem replacement_derivative {n : ℕ} (i : Fin (n + 1)) {w : (Fin (n + 1) → ℝ) → ℝ}
    (hw : Differentiable ℝ w) (x : Fin (n + 1) → ℝ) :
    HasFDerivAt (fun x => Function.update x i (w x))
      (ContinuousLinearMap.pi fun m => if m = i then fderiv ℝ w x
        else ContinuousLinearMap.proj m) x :=
  Sard.CoordinateChange.hasFDerivAt_update i hw x

theorem replacement_injective {n : ℕ} (i : Fin (n + 1))
    {α : (Fin (n + 1) → ℝ) →L[ℝ] ℝ} (hα : α (Pi.single i (1 : ℝ)) ≠ 0) :
    Function.Injective (ContinuousLinearMap.pi fun m : Fin (n + 1) =>
      if m = i then α else ContinuousLinearMap.proj m) := by
  obtain ⟨e, he⟩ := Sard.CoordinateChange.exists_updateEquiv i hα
  intro a b hab
  apply e.injective
  change (e : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) a =
    (e : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) b
  rw [he]
  exact hab

example {α : (Fin 1 → ℝ) →L[ℝ] ℝ} (hα : α (Pi.single 0 (1 : ℝ)) ≠ 0) :
    Function.Injective (ContinuousLinearMap.pi fun m : Fin 1 =>
      if m = 0 then α else ContinuousLinearMap.proj m) :=
  replacement_injective 0 hα

run_cmd do
  let env ← Lean.getEnv
  for name in #[`FunctionalInequalities.Analysis.Sard.Chart,
      `FunctionalInequalities.Analysis.Sard.Smooth,
      `FunctionalInequalities.Analysis.Sard.Disk,
      `FunctionalInequalities.Analysis.Sard.QuadraticCover] do
    if env.header.moduleNames.contains name then
      throwError "Coordinate-change tools load a Sard application: {name}"

#print axioms finite_order
#print axioms smooth_order
#print axioms replacement_derivative
#print axioms replacement_injective
end SardCoordinateChangeAudit

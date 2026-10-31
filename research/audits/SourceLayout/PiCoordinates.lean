module

public import FunctionalInequalities.Analysis.PiCoordinates
public import Lean
meta import Lean

@[expose] public section

open FunctionalInequalities.Analysis

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : (ι → ℝ) →L[ℝ] ℝ} (hα : α ≠ 0) :
    ∃ i : ι, α (Pi.single i (1 : ℝ)) ≠ 0 :=
  PiCoordinates.exists_apply_single_ne_zero hα

example {α : (Fin 0 → ℝ) →L[ℝ] ℝ} (hα : α ≠ 0) : False := by
  obtain ⟨i, _⟩ := PiCoordinates.exists_apply_single_ne_zero hα
  exact Fin.elim0 i

run_cmd do
  let env ← Lean.getEnv
  if env.header.moduleNames.any (fun n => n.toString.startsWith "FunctionalInequalities.Analysis.Sard") then
    throwError "Coordinate detection imports Sard chart applications"

module

public import FunctionalInequalities.Analysis.Sard.Disk
public import Lean
meta import Lean

@[expose] public section

open FunctionalInequalities.Analysis.MorseSard Set Metric
open scoped ContDiff
namespace SardDiskImportAudit
variable {n p k : ℕ}

example (φ : (Fin p → ℝ) → (Fin n → ℝ)) (κ : ℝ) :
    IsDisk φ κ ↔ ContDiff ℝ 1 φ ∧ 0 ≤ κ ∧
      ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
        ‖a - b‖ ≤ κ * ‖φ a - φ b‖ := Iff.rfl

theorem disk_mean_value {φ : (Fin p → ℝ) → (Fin n → ℝ)} {κ : ℝ}
    (hφ : IsDisk φ κ) {S : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (hflat : ∀ j : Fin n, FlatAlong φ S k fun x => fderiv ℝ f x (Pi.single j (1 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
        φ a ∈ S → φ b ∈ S → ‖φ a - φ b‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
          |f (φ (a + s • (b - a))) - f (φ a)| ≤ ε * ‖φ a - φ (a + s • (b - a))‖ ^ (k + 1) :=
  abs_sub_le_of_flat_fderiv hφ hf hflat

run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    if name.toString.startsWith "FunctionalInequalities.Analysis.Sard." &&
        name != `FunctionalInequalities.Analysis.Sard.Disk then
      throwError "Disk loads an unrelated Sard layer: {name}"

#print axioms disk_mean_value
end SardDiskImportAudit

import FunctionalInequalities.Analysis.Sard.Chart
import Lean

/-! The finite-regularity graph theorem is usable without the smooth chart or covering layer. -/
set_option autoImplicit false
open FunctionalInequalities.Analysis Filter Topology
open scoped ContDiff
namespace SardChartImportAudit

theorem finite_graph {n k : ℕ} (hk : 1 ≤ k) {w : (Fin (n + 1) → ℝ) → ℝ}
    {x₀ : Fin (n + 1) → ℝ} (hw : ContDiff ℝ k w) (hx₀ : w x₀ = 0) (hd : fderiv ℝ w x₀ ≠ 0) :
    ∃ (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ), ContDiff ℝ k θ ∧
      ∀ᶠ x in 𝓝 x₀, w x = 0 →
        x = Fin.insertNth (α := fun _ => ℝ) i (θ (Fin.removeNth i x)) (Fin.removeNth i x) :=
  MorseSard.exists_graph hk hw hx₀ hd

run_cmd do
  let env ← Lean.getEnv
  for name in #[`FunctionalInequalities.Analysis.Sard.Smooth,
      `FunctionalInequalities.Analysis.Sard.QuadraticCover] do
    if env.header.moduleNames.contains name then
      throwError "The finite chart loads an application layer: {name}"
  for name in #[`FunctionalInequalities.Analysis.exists_local_graph,
      `FunctionalInequalities.Analysis.critical_subset_layers] do
    if env.contains name then throwError "A smooth Sard producer leaked into the finite chart: {name}"

#print axioms finite_graph
end SardChartImportAudit

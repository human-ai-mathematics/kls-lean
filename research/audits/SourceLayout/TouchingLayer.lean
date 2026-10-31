module

public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import Lean
meta import Lean

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

namespace TouchingLayerAudit

theorem upper_touch {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x : EuclideanSpace ℝ (Fin n)}
    (hψ : ContDiffAt ℝ 2 ψ x) (hcontact : u x = ψ x)
    (htouch : ∀ᶠ y in 𝓝 x, u y ≤ ψ y) : (hessianMatrix ψ x).PosSemidef :=
  posSemidef_hessianMatrix_of_upper_touch hconv hψ hcontact htouch

run_cmd do
  let env ← Lean.getEnv
  for name in #[`FunctionalInequalities.Analysis.posDef_and_convolution_le_log_det_hessianMatrix,
      `FunctionalInequalities.Analysis.ae_exists_gradient_posDef_det_eq] do
    if (env.find? name).isSome then
      throwError "Touching tests imported mollification or AE identification: {name}"

#print axioms upper_touch
end TouchingLayerAudit

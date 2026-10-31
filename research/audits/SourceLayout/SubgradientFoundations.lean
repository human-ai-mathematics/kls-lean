module

public import FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import Lean
meta import Lean

@[expose] public section

open Set
open FunctionalInequalities.Analysis

namespace SubgradientFoundationsAudit

/-- Basic domain images require neither finite dimension nor a measure. -/
theorem image_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E → ℝ) (D : Set E) {A B : Set E} (h : A ⊆ B) :
    subgradientImageOn u D A ⊆ subgradientImageOn u D B :=
  subgradientImageOn_mono u D h

run_cmd do
  let env ← Lean.getEnv
  for name in #[`FunctionalInequalities.Analysis.exists_uniform_subgradient_bound_on_compact,
      `FunctionalInequalities.Analysis.exists_c1_of_unique_supports,
      `FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen,
      `FunctionalInequalities.Analysis.eventually_mem_subgradientImageOn_of_unique_contact] do
    if (env.find? name).isSome then
      throwError "Subgradient foundations imported a higher layer: {name}"

#print axioms image_mono
end SubgradientFoundationsAudit

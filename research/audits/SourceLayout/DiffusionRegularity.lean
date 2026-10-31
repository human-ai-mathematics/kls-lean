module

public import FunctionalInequalities.Probability.Diffusion.Generator

/-! Continuous coefficients and C2 data suffice without finite dimension or completeness. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FunctionalInequalities.Probability.Diffusion

namespace SourceLayout

theorem diffusion_regularity {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} {b : V → V} {σ : V → Fin d → V} {F : V → ℝ}
    (hb : Continuous b) (hσ : ∀ k, Continuous (fun x => σ x k))
    (hF : ContDiff ℝ 2 F) : Continuous (diffusionGenerator b σ F) :=
  continuous_diffusionGenerator hb hσ hF

#print axioms SourceLayout.diffusion_regularity

end SourceLayout

module

public import FunctionalInequalities.Probability.Diffusion.VectorGenerator

/-! Narrow scalar client and axiom reports for the vector-valued diffusion generator.
These reports belong to verification rather than production-module elaboration.
-/

@[expose] public section

set_option autoImplicit false
open FunctionalInequalities.Probability.Diffusion

namespace SourceLayout.VectorGenerator

theorem scalar {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) :
    diffusionGenerator b σ F x = vectorGenerator b σ F x :=
  diffusionGenerator_eq_vectorGenerator b σ F x

#print axioms FunctionalInequalities.Probability.Diffusion.vectorGenerator
#print axioms FunctionalInequalities.Probability.Diffusion.diffusionGenerator_eq_vectorGenerator
#print axioms FunctionalInequalities.Probability.Diffusion.fderiv_clm_comp_apply_vec
#print axioms FunctionalInequalities.Probability.Diffusion.vectorGenerator_clm_comp
#print axioms FunctionalInequalities.Probability.Diffusion.vectorGenerator_prodMk
#print axioms FunctionalInequalities.Probability.Diffusion.vectorGenerator_pi
#print axioms FunctionalInequalities.Probability.Diffusion.fderiv_prodMk_apply_vec
#print axioms FunctionalInequalities.Probability.Diffusion.fderiv_pi_apply_vec
#print axioms scalar

end SourceLayout.VectorGenerator

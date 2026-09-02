import FunctionalInequalities.ProductGeometry
import FunctionalInequalities.ProductVariance

/-!
# Almost-everywhere admissibility of Hilbert-product sections

Draft statements awaiting human review and a separate proof phase.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {f : WithLp 2 (E × F) → ℝ}

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem Admissible.memLp_uncurry (hf : Admissible (prodMeasure μ ν) f) :
    MemLp (fun p : E × F ↦ f (WithLp.toLp 2 p)) 2 (μ.prod ν) := sorry

omit [SecondCountableTopology E] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem Admissible.integrable_gradient_fst (hf : Admissible (prodMeasure μ ν) f) :
    Integrable (fun p : E × F ↦ ‖(gradient f (WithLp.toLp 2 p)).fst‖ ^ 2) (μ.prod ν) := sorry

omit [SecondCountableTopology E] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem Admissible.integrable_gradient_snd (hf : Admissible (prodMeasure μ ν) f) :
    Integrable (fun p : E × F ↦ ‖(gradient f (WithLp.toLp 2 p)).snd‖ ^ 2) (μ.prod ν) := sorry

theorem Admissible.section_left_ae (hf : Admissible (prodMeasure μ ν) f) :
    ∀ᵐ y ∂ν, Admissible μ (fun x ↦ f (WithLp.toLp 2 (x, y))) := sorry

theorem Admissible.section_right_ae (hf : Admissible (prodMeasure μ ν) f) :
    ∀ᵐ x ∂μ, Admissible ν (fun y ↦ f (WithLp.toLp 2 (x, y))) := sorry

theorem energy_prod_eq (hf : Admissible (prodMeasure μ ν) f) :
    energy (prodMeasure μ ν) f =
      (∫ p : E × F, ‖(gradient f (WithLp.toLp 2 p)).fst‖ ^ 2 ∂μ.prod ν) +
      (∫ p : E × F, ‖(gradient f (WithLp.toLp 2 p)).snd‖ ^ 2 ∂μ.prod ν) := sorry

end FunctionalInequalities.Poincare

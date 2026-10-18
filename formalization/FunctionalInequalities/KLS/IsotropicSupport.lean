import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.Probability.Covariance.Positivity

/-!
# Full affine support of isotropic laws

An isotropic law has identity covariance, hence an injective covariance operator and full affine
support. Light owner of this fact (the Section 2 reduction module restates it with heavier imports).
-/

open MeasureTheory

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An isotropic law has full affine support. -/
theorem Isotropic.affineSupport_eq_top {μ : ProbabilityMeasure E} (hiso : KLS.Isotropic μ) :
    Probability.affineSupport μ = ⊤ := by
  apply Probability.affineSupport_eq_top_of_covariance_injective μ hiso.memLp_two
  rw [hiso.covariance_identity]
  exact fun _ _ h => h

end FunctionalInequalities.KLS

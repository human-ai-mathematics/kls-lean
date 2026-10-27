import FunctionalInequalities.Probability.Transport
import FunctionalInequalities.KLS.LogConcave.Transport

/-! Narrow-import clients for the transport owners. No isotropic or Poincaré assembly is imported. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory FunctionalInequalities

namespace SourceLayout

/-- Second-moment translation needs no scalar action, inner product, completeness or dimension. -/
theorem translated_second_moment {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (ν : ProbabilityMeasure E) (c : E)
    (h : MemLp id 2 (ν : Measure E)) :
    MemLp id 2 (Probability.translateLaw ν c : Measure E) :=
  Probability.memLp_id_two_translateLaw ν c h

/-- Linear transport of compact-set log-concavity is independent of finite dimension and completeness. -/
theorem logConcave_pullback {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) (ν : ProbabilityMeasure F)
    (T : F ≃L[ℝ] E) (hmap : Measure.map T (ν : Measure F) = (μ : Measure E)) :
    KLS.LogConcave ν :=
  hμ.of_continuousLinearEquiv_map ν T hmap

#print axioms SourceLayout.translated_second_moment
#print axioms SourceLayout.logConcave_pullback

end SourceLayout

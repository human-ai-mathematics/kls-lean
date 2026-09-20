import FunctionalInequalities.Energy.Cheeger.Basic
import FunctionalInequalities.KLS.LogConcave.Density.AbsoluteContinuity

/-!
# Cheeger energy identification for log-concave laws

The intrinsic absolute-continuity theorem supplies the input to the generic comparison.
The public statement and namespace are preserved. For the stronger arbitrary-law identity,
see `Energy/Cheeger/Identification.lean`; this module adds no finiteness or Poincaré estimate.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS.LogConcave

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- Restricted scope with certified input: for a log-concave law the intrinsic law is absolutely
continuous with respect to Haar measure (`intrinsic_absolutelyContinuous`), so the selected
canonical energy is twice the transported Cheeger energy.  This covers every law in the KLS
routes, including ambient singular laws. -/
theorem intrinsicSmooth_energy_eq_two_mul_cheeger {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (f : Lp ℝ 2 (μ : Measure E)) :
    Energy.SmoothGradient.Intrinsic.energy μ f = 2 * Energy.Cheeger.Intrinsic.energy μ f :=
  Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous μ
    Measure.addHaar (hμ.intrinsic_absolutelyContinuous Measure.addHaar) f

end FunctionalInequalities.KLS.LogConcave

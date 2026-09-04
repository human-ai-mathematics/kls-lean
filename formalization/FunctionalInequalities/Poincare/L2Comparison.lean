import FunctionalInequalities.Energy.Comparison
import FunctionalInequalities.Poincare.Comparison
import FunctionalInequalities.Poincare.L2Energy

/-!
# Comparing Poincaré constants of `L²` energies

For the same probability measure, increasing an energy shrinks its finite domain and enlarges
the denominator on the remaining tests. Consequently its optimal Poincaré constant can only
decrease. The proof is an explicit Rayleigh map, so zero-energy tests and infinite optimal
constants require no separate assumptions.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare

universe u

variable {α : Type u} [MeasurableSpace α]

/-- Pointwise energy comparison induces a Rayleigh map in the contravariant direction. -/
def l2EnergyRayleighMap (μ : ProbabilityMeasure α)
    {lower upper : Energy.Functional (Lp ℝ 2 (μ : Measure α))}
    (h : lower.PointwiseLE upper) :
    TestFamily.RayleighMap (TestFamily.ofL2Energy μ upper)
      (TestFamily.ofL2Energy μ lower) where
  toFun f := Energy.Functional.domainMap h f
  variance_le _ := le_rfl
  energy_le f := Energy.Functional.finiteValue_domainMap_le h f

/-- Increasing an extended `L²` energy can only decrease its optimal Poincaré constant. -/
theorem constantOfL2Energy_anti_mono (μ : ProbabilityMeasure α)
    {lower upper : Energy.Functional (Lp ℝ 2 (μ : Measure α))}
    (h : lower.PointwiseLE upper) :
    constantOfL2Energy μ upper ≤ constantOfL2Energy μ lower :=
  (l2EnergyRayleighMap μ h).constant_le

end FunctionalInequalities.Poincare

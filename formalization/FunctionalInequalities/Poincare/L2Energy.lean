import FunctionalInequalities.Energy.Functional
import FunctionalInequalities.L2.MeanVariance
import FunctionalInequalities.Poincare.Optimal

/-!
# Poincaré constants for extended energies on real `L²`

This module connects the analytic carrier to the order-theoretic Poincaré optimizer.
For an extended energy on real `L²(μ)`, the tests are exactly the elements where the
energy is finite. Variance and finite energy then form a `Poincare.TestFamily`.

No closedness, quadraticity, or Markov property is assumed here.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare

universe u

variable {α : Type u} [MeasurableSpace α]

namespace TestFamily

/-- The finite-energy domain of an extended functional on real `L²(μ)`, equipped with
intrinsic `L²` variance and the functional's finite value. -/
def ofL2Energy (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) : TestFamily where
  Test := energy.domain
  variance f := L2.variance μ f.1
  energy f := energy.finiteValue f

/-- Variance in the induced test family is intrinsic `L²` variance. -/
@[simp]
theorem ofL2Energy_variance (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (f : energy.domain) :
    (ofL2Energy μ energy).variance f = L2.variance μ f.1 :=
  rfl

/-- Energy in the induced test family is the finite value certified by the domain subtype. -/
@[simp]
theorem ofL2Energy_energy (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (f : energy.domain) :
    (ofL2Energy μ energy).energy f = energy.finiteValue f :=
  rfl

end TestFamily

/-- The optimal extended Poincaré constant of an energy on real `L²(μ)`. -/
def constantOfL2Energy (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) : ENNReal :=
  (TestFamily.ofL2Energy μ energy).constant

/-- A finite Poincaré constant is valid on every finite-energy `L²` test. -/
def HoldsL2Energy (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) : Prop :=
  (TestFamily.ofL2Energy μ energy).Holds C

/-- Unfolding validity gives the Poincaré inequality on the finite-energy domain. -/
theorem holdsL2Energy_iff (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    HoldsL2Energy μ energy C ↔
      ∀ f : energy.domain, L2.variance μ f.1 ≤ C * energy.finiteValue f :=
  Iff.rfl

/-- A finite `L²` Poincaré constant is valid exactly when it bounds the optimal one. -/
theorem holdsL2Energy_iff_constant_le (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    HoldsL2Energy μ energy C ↔ constantOfL2Energy μ energy ≤ (C : ENNReal) := by
  simpa [HoldsL2Energy, constantOfL2Energy] using
    TestFamily.holds_iff_constant_le (TestFamily.ofL2Energy μ energy) C

end FunctionalInequalities.Poincare

import FunctionalInequalities.Tensorization
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Certificate for two-factor Poincaré tensorization

This module packages the fixed-constant and extended-optimal-constant conclusions of ledger
node `lem:poincare-tensorization`. The product law is carried by `WithLp 2 (E × F)`, and all
constants refer to the smooth L² finite-gradient-energy tests in `Poincare.Admissible`.

The Euclidean specializations allow arbitrary natural-number dimensions, including zero.
No moment, density, finite-optimal-constant, or attainment assumption is added.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Project.PoincareTensorization

section Hilbert

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- The fixed-constant product inequality; probability and nonnegativity are carried by
the two `Holds` assumptions. -/
theorem fixed_constant {μ : Measure E} {ν : Measure F} {C C' : ℝ}
    (hμ : Poincare.Holds μ C) (hν : Poincare.Holds ν C') :
    Poincare.Holds (Poincare.prodMeasure μ ν) (max C C') :=
  hμ.prod hν

/-- The optimal product constant is bounded by the maximum of the two extended constants. -/
theorem optimal_constant (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Poincare.constant (Poincare.prodMeasure μ ν) ≤
      max (Poincare.constant μ) (Poincare.constant ν) :=
  Poincare.constant_prod_le

/-- Both conclusions of the tensorization node on real separable Hilbert spaces. -/
theorem certificate (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ ⦃C C' : ℝ⦄, Poincare.Holds μ C → Poincare.Holds ν C' →
      Poincare.Holds (Poincare.prodMeasure μ ν) (max C C')) ∧
      Poincare.constant (Poincare.prodMeasure μ ν) ≤
        max (Poincare.constant μ) (Poincare.constant ν) := by
  constructor
  · intro C C' hμ hν
    exact fixed_constant hμ hν
  · exact optimal_constant μ ν

end Hilbert

/-- Fixed-constant tensorization for Euclidean factors of dimensions `m, n : ℕ`, including
zero-dimensional factors, with their product equipped with the Hilbert norm. -/
theorem euclidean_fixed_constant {m n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin m))}
    {ν : Measure (EuclideanSpace ℝ (Fin n))} {C C' : ℝ}
    (hμ : Poincare.Holds μ C) (hν : Poincare.Holds ν C') :
    Poincare.Holds (Poincare.prodMeasure μ ν) (max C C') :=
  fixed_constant hμ hν

/-- Extended-optimal-constant tensorization for arbitrary Euclidean dimensions, including
zero, without any finiteness assumption on the constants. -/
theorem euclidean_optimal_constant {m n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Poincare.constant (Poincare.prodMeasure μ ν) ≤
      max (Poincare.constant μ) (Poincare.constant ν) :=
  optimal_constant μ ν

/-- Both tensorization conclusions specialized to Euclidean factors of arbitrary dimensions. -/
theorem euclidean_certificate {m n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ ⦃C C' : ℝ⦄, Poincare.Holds μ C → Poincare.Holds ν C' →
      Poincare.Holds (Poincare.prodMeasure μ ν) (max C C')) ∧
      Poincare.constant (Poincare.prodMeasure μ ν) ≤
        max (Poincare.constant μ) (Poincare.constant ν) :=
  certificate μ ν

end FunctionalInequalities.Project.PoincareTensorization

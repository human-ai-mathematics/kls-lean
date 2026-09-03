import FunctionalInequalities.Project.PoincareTensorization

/-!
# Lean certificate for `lem:poincare-tensorization`

This node-specific artifact certifies both the fixed-constant product inequality and the
extended-optimal-constant bound for the repository's smooth L² finite-gradient-energy tests.
The reusable certificate and its Euclidean specializations live in
`FunctionalInequalities.Project.PoincareTensorization`. The Hilbert product uses `WithLp 2`;
zero-dimensional Euclidean factors and infinite optimal constants are included.
-/

noncomputable section

open MeasureTheory
open FunctionalInequalities

namespace Solutions.LemPoincareTensorization

/-- Machine certificate covering both public tensorization conclusions in the ledger node. -/
theorem certificate {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ ⦃C C' : ℝ⦄, Poincare.Holds μ C → Poincare.Holds ν C' →
      Poincare.Holds (Poincare.prodMeasure μ ν) (max C C')) ∧
      Poincare.constant (Poincare.prodMeasure μ ν) ≤
        max (Poincare.constant μ) (Poincare.constant ν) :=
  Project.PoincareTensorization.certificate μ ν

/-- Concrete certificate for any two Euclidean dimensions `m, n : ℕ`, including zero. -/
theorem euclidean_certificate {m n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ ⦃C C' : ℝ⦄, Poincare.Holds μ C → Poincare.Holds ν C' →
      Poincare.Holds (Poincare.prodMeasure μ ν) (max C C')) ∧
      Poincare.constant (Poincare.prodMeasure μ ν) ≤
        max (Poincare.constant μ) (Poincare.constant ν) :=
  Project.PoincareTensorization.euclidean_certificate μ ν

end Solutions.LemPoincareTensorization

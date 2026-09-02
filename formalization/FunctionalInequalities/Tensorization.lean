import FunctionalInequalities.ProductAdmissible

/-!
# Poincaré tensorization: candidate statements

Node: `lem:poincare-tensorization`. Status: drafted; human review must precede freezing.
The product law lives on `WithLp 2 (E × F)` and uses the manuscript normalization
`Var(f) ≤ C ∫ ‖gradient f‖²`. These declarations do not certify a proof.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- Candidate fixed-constant tensorization inequality on the Hilbert product.
The assumptions `Holds μ C` and `Holds ν C'` include probability and nonnegativity. -/
theorem Holds.prod
    {μ : Measure E} {ν : Measure F} {C C' : ℝ}
    (hμ : Holds μ C) (hν : Holds ν C') :
    Holds (prodMeasure μ ν) (max C C') := sorry

/-- Candidate bound for the extended optimal constants, including infinite constants. -/
theorem constant_prod_le
    {μ : Measure E} {ν : Measure F}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    constant (prodMeasure μ ν) ≤ max (constant μ) (constant ν) := sorry

end FunctionalInequalities.Poincare

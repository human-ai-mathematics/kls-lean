import FunctionalInequalities.Poincare.Product.Tensorization
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Lean certificate for `lem:poincare-tensorization`

Source: Bakry, Gentil and Ledoux, *Analysis and Geometry of Markov Diffusion Operators*
(2014), §4.3, Proposition 4.3.1, pp. 185–187:
https://www.hse.ru/data/2016/11/24/1113029204/bok%253A978-3-319-00227-9.pdf#page=201
The proposition gives the fixed-constant upper bound `max C C'` for a product of Markov triples.

This certificate combines `Poincare.Holds.prod`, a local realization of that upper bound for
the repository's smooth L² finite-gradient-energy tests, with `Poincare.constant_prod_le`, its
local infimum consequence in `ENNReal`. Each factor is explicitly a probability measure on a
complete, second-countable real Hilbert space with its Borel structure, and the product uses
`WithLp 2`. Equivalence with the book's Dirichlet-form domain is not asserted. Zero-dimensional
Euclidean factors and infinite optimal constants are included by the local definitions.
-/

noncomputable section

open MeasureTheory
open FunctionalInequalities

namespace Solutions.LemPoincareTensorization

/-- Source: BGL Proposition 4.3.1 for the fixed-constant upper bound; the optimal-constant upper
bound is the local infimum consequence `Poincare.constant_prod_le`. This certificate combines
both results for the repository's test domain, with separate probability assumptions on the
two factors. See the module comment for the source's Markov-triple scope. -/
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
        max (Poincare.constant μ) (Poincare.constant ν) := by
  constructor
  · intro C C' hμ hν
    exact hμ.prod hν
  · exact Poincare.constant_prod_le

section EuclideanChecks

variable {m n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

-- Local specialization of this certificate to arbitrary Euclidean dimensions, including zero.
#check (certificate μ ν :
  (∀ ⦃C C' : ℝ⦄, Poincare.Holds μ C → Poincare.Holds ν C' →
    Poincare.Holds (Poincare.prodMeasure μ ν) (max C C')) ∧
    Poincare.constant (Poincare.prodMeasure μ ν) ≤
      max (Poincare.constant μ) (Poincare.constant ν))

end EuclideanChecks

end Solutions.LemPoincareTensorization

/--
info: 'Solutions.LemPoincareTensorization.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemPoincareTensorization.certificate

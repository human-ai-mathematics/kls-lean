import FunctionalInequalities.Probability.AffineSupport
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Order.LiminfLimsup

/-!
# Isoperimetric boundary content and inverse scale on the affine support

Source: Blueprint `def:isoperimetric-cheeger-scale`. Read `carrierMeasure`,
`boundaryContent`, `constant`, then `inverseScale`. The metric is the induced metric on
the actual affine carrier; it does not thicken sets in ambient normal directions.

All quantities are extended nonnegative numbers. The zero-dimensional carrier has
constant infinity and inverse scale zero. These definitions do not identify BV perimeter,
the density frontend, a Poincare constant, or a metric energy.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace FunctionalInequalities.KLS.Isoperimetry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The law on its affine carrier, equipped with the distance inherited from the ambient space. -/
def carrierMeasure (μ : ProbabilityMeasure E) : ProbabilityMeasure (Probability.affineSupport μ) :=
  μ.map (Probability.measurable_retraction μ).aemeasurable

/-- Outer Minkowski boundary content, with the limit taken through strictly positive radii.
For positive radii, the original set is contained in its thickening, so ENNReal subtraction
represents the nonnegative mass increment. Empty sets have empty thickenings. -/
def boundaryContent (μ : ProbabilityMeasure E) (B : Set (Probability.affineSupport μ)) : ENNReal :=
  liminf (fun r : ℝ ↦
    (((carrierMeasure μ : Measure (Probability.affineSupport μ)) (Metric.thickening r B)) -
      (carrierMeasure μ : Measure (Probability.affineSupport μ)) B) / ENNReal.ofReal r) (𝓝[>] 0)

/-- The isoperimetric constant `h_μ`; an empty admissible family gives infinity. -/
def constant (μ : ProbabilityMeasure E) : ENNReal := by
  classical
  exact if Module.finrank ℝ (Probability.affineSupport μ).direction = 0 then ⊤ else
    ⨅ (B : Set (Probability.affineSupport μ)) (_ : MeasurableSet B)
      (_ : 0 < (carrierMeasure μ : Measure (Probability.affineSupport μ)) B)
      (_ : (carrierMeasure μ : Measure (Probability.affineSupport μ)) B < 1),
      boundaryContent μ B /
        min ((carrierMeasure μ : Measure (Probability.affineSupport μ)) B)
          (1 - (carrierMeasure μ : Measure (Probability.affineSupport μ)) B)

/-- The inverse isoperimetric scale `Ψ_KLS`: ENNReal gives `0⁻¹ = ⊤` and `⊤⁻¹ = 0`. -/
def inverseScale (μ : ProbabilityMeasure E) : ENNReal := (constant μ)⁻¹

end FunctionalInequalities.KLS.Isoperimetry

module

public import FunctionalInequalities.Energy.SmoothGradient.Density
public import FunctionalInequalities.Energy.SmoothGradient.Quadratic
public import FunctionalInequalities.Energy.Relaxation.Quadratic

/-!
# Closed quadratic structure of the smooth-gradient relaxation

On a finite-dimensional real Borel Hilbert space, compactly supported `C∞` functions give a
dense realization in real `L²`. Their finite gradient energy is quadratic. The generic
sequential-relaxation theorem therefore packages the relaxed functional as a densely defined
closed quadratic energy.

This conclusion does not say that relaxation agrees with the raw ambient-gradient energy on
every concrete test. It also does not provide the normal-contraction estimate required for a
Dirichlet form, or identify the relaxation with `2 Ch`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Energy.SmoothGradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The sequential relaxation of the `C∞` gradient pre-energy is a densely defined closed
quadratic functional on real `L²(μ)`. -/
theorem relaxation_closedQuadratic (μ : ProbabilityMeasure E) :
    ClosedQuadratic (relaxation μ) :=
  (preEnergy_quadratic μ).closedQuadratic_sequentialRelaxation
    (preEnergy_denseRealization μ)

end FunctionalInequalities.Energy.SmoothGradient

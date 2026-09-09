import FunctionalInequalities.Poincare.Foundation
import FunctionalInequalities.Poincare.Gaussian.Real

/-!
# Using the Poincaré foundation

Read these examples from top to bottom: intrinsic variance, comparison of energies, the selected
Euclidean frontend, and boundary cases. Each `example` is checked by the default `lake build`;
none introduces a duplicate public theorem or a new ledger certificate.

The general examples use arbitrary probability laws. The Gaussian examples use the accepted
smooth-test frontend. They do not identify its constant with the selected relaxed constant.
For the definitions, normalization and sources, see
`formalization/FunctionalInequalities/Poincare/README.md` from the repository root.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Examples.PoincareFoundation

section Probability

variable {α : Type*} [MeasurableSpace α] (μ : ProbabilityMeasure α)

/-- A constant function represents a zero-variance `L²` class for every probability law. -/
example (c : ℝ) : L2.variance μ (L2.const μ c) = 0 :=
  L2.variance_const μ c

/-- Increasing energy decreases the optimal constant; infinite optima are allowed. -/
example (lower upper : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (h : lower.PointwiseLE upper) :
    Poincare.L2Energy.constant μ upper ≤ Poincare.L2Energy.constant μ lower :=
  Poincare.L2Energy.constant_antitone μ h

end Probability

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)

/-- Closedness applies without a density, log-concavity, or a nondegenerate covariance. -/
example : Energy.ClosedQuadratic (FunctionalInequalities.Energy.SmoothGradient.Intrinsic.energy μ) :=
  FunctionalInequalities.Energy.SmoothGradient.Intrinsic.closedQuadratic μ

/-- Turn a finite bound for the selected optimum into the inequality on its finite domain. -/
example (C : NNReal)
    (h : FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.constant μ ≤ (C : ENNReal)) :
    FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.Holds μ C :=
  (FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.holds_iff_constant_le μ C).mpr h

end Euclidean

/-- The selected closed energy also exists on the zero-dimensional Euclidean space. -/
example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    Energy.ClosedQuadratic (FunctionalInequalities.Energy.SmoothGradient.Intrinsic.energy μ) :=
  FunctionalInequalities.Energy.SmoothGradient.Intrinsic.closedQuadratic μ

/-! ## A singular law: raw energy depends on the representative -/

/-- The functions `0` and `id` are equal almost everywhere for the Dirac law at zero. -/
example : (fun _ : ℝ ↦ (0 : ℝ)) =ᵐ[Measure.dirac 0] id := by
  change ∀ᵐ x ∂(Measure.dirac (0 : ℝ)), (0 : ℝ) = id x
  simp

/-- The raw energy of the zero function is zero. -/
example : FunctionalInequalities.Poincare.SmoothTest.energy (Measure.dirac (0 : ℝ)) (fun _ ↦ 0) = 0 := by
  rw [FunctionalInequalities.Poincare.SmoothTest.energy_eq_fderiv]
  simp

/-- The raw energy of `id` is one, despite representing the same Dirac `L²` class. -/
example : FunctionalInequalities.Poincare.SmoothTest.energy (Measure.dirac (0 : ℝ)) id = 1 := by
  rw [FunctionalInequalities.Poincare.SmoothTest.energy_eq_fderiv]
  simp

/-! ## An empty test class: infinite relaxation does not supply a recovery sequence -/

private def emptyPreEnergy : Energy.PreEnergy ℝ where
  Test := Empty
  toAmbient := Empty.elim
  energy := Empty.elim

example (x : ℝ) : emptyPreEnergy.sequentialRelaxation x = ⊤ := by
  apply top_unique
  rw [Energy.PreEnergy.sequentialRelaxation_apply]
  exact le_iInf fun approximation ↦ (approximation.1 0).elim

example (x : ℝ) :
    ¬ emptyPreEnergy.HasRecoverySequenceAt emptyPreEnergy.sequentialRelaxation x := by
  rintro ⟨approximation, _⟩
  exact (approximation.1 0).elim

/-! ## Certified Gaussian values in the smooth-test frontend -/

/-- The second parameter is variance, so mean `3` and variance `4` give constant `4`. -/
example : FunctionalInequalities.Poincare.SmoothTest.constant (ProbabilityTheory.gaussianReal 3 4) = (4 : ENNReal) :=
  FunctionalInequalities.Poincare.SmoothTest.constant_gaussianReal 3 4

/-- Zero variance gives a Dirac law and constant zero, with no positive-variance assumption. -/
example (m : ℝ) : FunctionalInequalities.Poincare.SmoothTest.constant (ProbabilityTheory.gaussianReal m 0) = 0 :=
  FunctionalInequalities.Poincare.SmoothTest.constant_gaussianReal m 0

end Examples.PoincareFoundation

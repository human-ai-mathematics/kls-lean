import FunctionalInequalities.Poincare.Euclidean.LegacyComparison
import FunctionalInequalities.Poincare.Gaussian.Real

/-!
# Lean certificate: legacy tests and relaxed Poincaré constants

Ledger node: `lem:legacy-relaxed-poincare-comparison`.
Status: proved / checked_by: lean. The named certificate packages the complete node.
The public comparison signatures are unchanged from the reviewed statement batch.
Typed applications include zero dimension, singular laws and infinite optimal constants.

Sources, assumptions and reading order: `Poincare/Euclidean/README.md` in the library.
-/

open MeasureTheory FunctionalInequalities

namespace Solutions.LemLegacyRelaxedPoincareComparison

/-- Arbitrary pre-energy comparison and its complete legacy-to-intrinsic specialization. -/
theorem certificate {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (ν : ProbabilityMeasure α) (P : Energy.PreEnergy (Lp ℝ 2 (ν : Measure α)))
    (μ : ProbabilityMeasure E) :
    (∀ C : NNReal, (Poincare.TestFamily.ofPreEnergy ν P).Holds C ↔
      Poincare.L2Energy.Holds ν P.sequentialRelaxation C) ∧
    (Poincare.TestFamily.ofPreEnergy ν P).constant =
      Poincare.L2Energy.constant ν P.sequentialRelaxation ∧
    (∀ C : NNReal, Poincare.Holds (μ : Measure E) (C : ℝ) ↔
      (Poincare.TestFamily.ofPreEnergy μ (Energy.Euclidean.smoothGradientPreEnergy μ)).Holds C) ∧
    (∀ C : NNReal, Poincare.Holds (μ : Measure E) (C : ℝ) ↔
      Poincare.Ambient.Holds μ C) ∧
    Poincare.constant (μ : Measure E) = Poincare.Ambient.constant μ ∧
    (∀ C : NNReal, Poincare.Holds (μ : Measure E) (C : ℝ) ↔
      Poincare.Canonical.Holds μ C) ∧
    Poincare.constant (μ : Measure E) =
      Poincare.Canonical.constant μ :=
  ⟨Poincare.TestFamily.holds_ofPreEnergy_iff ν P,
    Poincare.TestFamily.constant_ofPreEnergy_eq ν P,
    Poincare.Euclidean.holds_iff_preEnergy μ,
    Poincare.Euclidean.holds_iff_ambient μ,
    Poincare.Euclidean.constant_eq_ambient μ,
    Poincare.Euclidean.holds_iff_canonical μ,
    Poincare.Euclidean.constant_eq_canonical μ⟩

end Solutions.LemLegacyRelaxedPoincareComparison

#check @Poincare.TestFamily.ofPreEnergy
#check @Poincare.TestFamily.holds_ofPreEnergy_iff
#check @Poincare.TestFamily.constant_ofPreEnergy_eq
#check @Poincare.Euclidean.holds_iff_preEnergy
#check @Poincare.Euclidean.holds_iff_ambient
#check @Poincare.Euclidean.constant_eq_ambient
#check @Poincare.Euclidean.holds_iff_canonical
#check @Poincare.Euclidean.constant_eq_canonical

-- Arbitrary measurable probabilities and concrete pre-energies, without density or quadraticity.
#check (fun {α : Type*} [MeasurableSpace α] (μ : ProbabilityMeasure α)
    (P : Energy.PreEnergy (Lp ℝ 2 (μ : Measure α))) (C : NNReal) ↦
  Poincare.TestFamily.holds_ofPreEnergy_iff μ P C)

-- No nonempty test type is required. This private object only checks the domain.
private def emptyPreEnergy (μ : ProbabilityMeasure ℝ) :
    Energy.PreEnergy (Lp ℝ 2 (μ : Measure ℝ)) where
  Test := Empty
  toAmbient := Empty.elim
  energy := Empty.elim

#check (fun (μ : ProbabilityMeasure ℝ) ↦
  Poincare.TestFamily.holds_ofPreEnergy_iff μ (emptyPreEnergy μ) 0)

-- Proper affine supports and dimension zero require no density or second-moment premise.
#check (fun (d : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) (C : NNReal) ↦
  Poincare.Euclidean.holds_iff_canonical μ C)
#check (fun (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) ↦
  Poincare.Euclidean.constant_eq_canonical μ)

-- Transfer the accepted Gaussian inequality through the proved bridge.
#check (fun (m : ℝ) (v : NNReal) ↦
  (Poincare.Euclidean.holds_iff_canonical
    (Probability.ofMeasure (ProbabilityTheory.gaussianReal m v)) v).mp
      (Poincare.holds_gaussianReal m v))

-- Sharp values transfer by equality, including the zero-variance Dirac case.
#check (fun (m : ℝ) (v : NNReal) ↦
  (Poincare.Euclidean.constant_eq_canonical
    (Probability.ofMeasure (ProbabilityTheory.gaussianReal m v))).symm.trans
      (Poincare.constant_gaussianReal m v))
#check (fun (m : ℝ) ↦
  (Poincare.Euclidean.constant_eq_canonical
    (Probability.ofMeasure (ProbabilityTheory.gaussianReal m 0))).symm.trans
      (Poincare.constant_gaussianReal m 0))

-- Infinite values remain extended values throughout the comparison.
#check (fun (μ : ProbabilityMeasure ℝ) (h : Poincare.constant (μ : Measure ℝ) = ⊤) ↦
  (Poincare.Euclidean.constant_eq_canonical μ).symm.trans h)

/--
info: 'Solutions.LemLegacyRelaxedPoincareComparison.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemLegacyRelaxedPoincareComparison.certificate

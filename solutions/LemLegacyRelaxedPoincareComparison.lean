module

public import FunctionalInequalities.Poincare.SmoothTest.Comparison
public import FunctionalInequalities.Poincare.Gaussian.Real

/-!
# Lean certificate: legacy tests and relaxed Poincaré constants

Ledger node: `lem:legacy-relaxed-poincare-comparison`.
Status: proved / checked_by: lean. The named certificate packages the complete node.
Typed applications include zero dimension, singular laws and infinite optimal constants.

Sources, assumptions and reading order: `Poincare/Euclidean/README.md` in the library.
-/

@[expose] public section

open MeasureTheory FunctionalInequalities

namespace Solutions.LemLegacyRelaxedPoincareComparison

/-- Arbitrary pre-energy comparison and its complete legacy-to-intrinsic specialization. -/
theorem certificate {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [FiniteDimensional ℝ E] (ν : ProbabilityMeasure α)
    (P : Energy.PreEnergy (Lp ℝ 2 (ν : Measure α))) (μ : ProbabilityMeasure E) :
    (∀ C : NNReal,
        (Poincare.TestFamily.ofPreEnergy ν P).Holds C ↔
          Poincare.L2Energy.Holds ν P.sequentialRelaxation C) ∧
      (Poincare.TestFamily.ofPreEnergy ν P).constant =
          Poincare.L2Energy.constant ν P.sequentialRelaxation ∧
        (∀ C : NNReal,
            FunctionalInequalities.Poincare.SmoothTest.Holds (μ : Measure E) (C : ℝ) ↔
              (Poincare.TestFamily.ofPreEnergy μ
                    (FunctionalInequalities.Energy.SmoothGradient.preEnergy μ)).Holds
                C) ∧
          (∀ C : NNReal,
              FunctionalInequalities.Poincare.SmoothTest.Holds (μ : Measure E) (C : ℝ) ↔
                FunctionalInequalities.Poincare.SmoothGradient.Ambient.Holds μ C) ∧
            FunctionalInequalities.Poincare.SmoothTest.constant (μ : Measure E) =
                FunctionalInequalities.Poincare.SmoothGradient.Ambient.constant μ ∧
              (∀ C : NNReal,
                  FunctionalInequalities.Poincare.SmoothTest.Holds (μ : Measure E) (C : ℝ) ↔
                    FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.Holds μ C) ∧
                FunctionalInequalities.Poincare.SmoothTest.constant (μ : Measure E) =
                  FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.constant μ :=
  ⟨Poincare.TestFamily.holds_ofPreEnergy_iff ν P,
    Poincare.TestFamily.constant_ofPreEnergy_eq ν P,
    FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy μ,
    FunctionalInequalities.Poincare.SmoothTest.holds_iff_ambient μ,
    FunctionalInequalities.Poincare.SmoothTest.constant_eq_ambient μ,
    FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsic μ,
    FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsic μ⟩

end Solutions.LemLegacyRelaxedPoincareComparison

#check @Poincare.TestFamily.ofPreEnergy
#check @Poincare.TestFamily.holds_ofPreEnergy_iff
#check @Poincare.TestFamily.constant_ofPreEnergy_eq
#check @FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy
#check @FunctionalInequalities.Poincare.SmoothTest.holds_iff_ambient
#check @FunctionalInequalities.Poincare.SmoothTest.constant_eq_ambient
#check @FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsic
#check @FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsic

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
  FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsic μ C)
#check (fun (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) ↦
  FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsic μ)

-- Transfer the accepted Gaussian inequality through the proved bridge.
#check (fun (m : ℝ) (v : NNReal) ↦
  (FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsic
    (Probability.ofMeasure (ProbabilityTheory.gaussianReal m v)) v).mp
      (FunctionalInequalities.Poincare.SmoothTest.holds_gaussianReal m v))

-- Sharp values transfer by equality, including the zero-variance Dirac case.
#check (fun (m : ℝ) (v : NNReal) ↦
  (FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsic
    (Probability.ofMeasure (ProbabilityTheory.gaussianReal m v))).symm.trans
      (FunctionalInequalities.Poincare.SmoothTest.constant_gaussianReal m v))
#check (fun (m : ℝ) ↦
  (FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsic
    (Probability.ofMeasure (ProbabilityTheory.gaussianReal m 0))).symm.trans
      (FunctionalInequalities.Poincare.SmoothTest.constant_gaussianReal m 0))

-- Infinite values remain extended values throughout the comparison.
#check
  (fun (μ : ProbabilityMeasure ℝ)
      (h : FunctionalInequalities.Poincare.SmoothTest.constant (μ : Measure ℝ) = ⊤) ↦
    (FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsic μ).symm.trans h)

/--
info: 'Solutions.LemLegacyRelaxedPoincareComparison.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemLegacyRelaxedPoincareComparison.certificate

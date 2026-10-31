module

public import FunctionalInequalities.Poincare.SmoothGradient.Comparison
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: ambient and intrinsic-affine comparison

Ledger node: `lem:ambient-intrinsic-poincare-comparison`.
Status: proved / checked_by: lean. The named certificate packages the complete node.
Typed applications include zero dimension, singular laws and infinite optimal constants.

Sources, assumptions and reading order: `Poincare/Euclidean/README.md` in the library.
-/

@[expose] public section

open MeasureTheory FunctionalInequalities

namespace Solutions.LemAmbientIntrinsicPoincareComparison

/-- The affine comparison, including concrete restriction and extension and both optimizers. -/
theorem certificate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E) :
    (∀ f : FunctionalInequalities.Energy.SmoothGradient.Test μ,
      ∃ g : FunctionalInequalities.Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ),
        (∀ v, g v = f (Probability.reconstruct μ v)) ∧
        g.toL2 = Energy.Euclidean.toIntrinsicL2 μ f.toL2 ∧ g.energy ≤ f.energy) ∧
    (∀ g : FunctionalInequalities.Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ),
      ∃ f : FunctionalInequalities.Energy.SmoothGradient.Test μ,
        (∀ v, f (Probability.reconstruct μ v) = g v) ∧
        Energy.Euclidean.toIntrinsicL2 μ f.toL2 = g.toL2 ∧ f.energy = g.energy) ∧
    FunctionalInequalities.Energy.SmoothGradient.relaxation μ =
      FunctionalInequalities.Energy.SmoothGradient.Intrinsic.energy μ ∧
    (∀ C : NNReal, FunctionalInequalities.Poincare.SmoothGradient.Ambient.Holds μ C ↔
      FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.Holds μ C) ∧
    FunctionalInequalities.Poincare.SmoothGradient.Ambient.constant μ =
      FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.constant μ :=
  ⟨FunctionalInequalities.Energy.SmoothGradient.Test.exists_intrinsic_restriction μ,
    FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension μ,
    FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy μ,
    FunctionalInequalities.Poincare.SmoothGradient.Ambient.holds_iff_intrinsic μ,
    FunctionalInequalities.Poincare.SmoothGradient.Ambient.constant_eq_intrinsic μ⟩

end Solutions.LemAmbientIntrinsicPoincareComparison

#check @FunctionalInequalities.Energy.SmoothGradient.Test.exists_intrinsic_restriction
#check @FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension
#check @FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy
#check @FunctionalInequalities.Poincare.SmoothGradient.Ambient.holds_iff_intrinsic
#check @FunctionalInequalities.Poincare.SmoothGradient.Ambient.constant_eq_intrinsic

-- Every dimension is permitted; no positivity hypothesis is hidden in the carrier.
#check (fun (d : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) ↦
  FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy μ)

-- The intrinsic carrier can collapse to a point.
#check (fun (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) ↦
  FunctionalInequalities.Poincare.SmoothGradient.Ambient.holds_iff_intrinsic μ 0)

-- A Dirac law still fits the raw test restriction/extension statements.
#check (fun (g : FunctionalInequalities.Energy.SmoothGradient.Test
    (Probability.intrinsicMeasure (Probability.ofMeasure (Measure.dirac (0 : ℝ))))) ↦
  FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension
    (Probability.ofMeasure (Measure.dirac (0 : ℝ))) g)

-- Equality transports the infinite value without converting it to a real constant.
#check (fun (μ : ProbabilityMeasure ℝ)
    (h : FunctionalInequalities.Poincare.SmoothGradient.Ambient.constant μ = ⊤) ↦
  (FunctionalInequalities.Poincare.SmoothGradient.Ambient.constant_eq_intrinsic μ).symm.trans h)

/--
info: 'Solutions.LemAmbientIntrinsicPoincareComparison.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemAmbientIntrinsicPoincareComparison.certificate

import FunctionalInequalities.Poincare.Euclidean.AffineComparison

/-!
# Lean certificate: ambient and intrinsic-affine comparison

Ledger node: `lem:ambient-intrinsic-poincare-comparison`.
Status: proved / checked_by: lean. The named certificate packages the complete node.
The public comparison signatures are unchanged from the reviewed statement batch.
Typed applications include zero dimension, singular laws and infinite optimal constants.

Sources, assumptions and reading order: `Poincare/Euclidean/README.md` in the library.
-/

open MeasureTheory FunctionalInequalities

namespace Solutions.LemAmbientIntrinsicPoincareComparison

/-- The affine comparison, including concrete restriction and extension and both optimizers. -/
theorem certificate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E) :
    (∀ f : Energy.Euclidean.SmoothGradientTest μ,
      ∃ g : Energy.Euclidean.SmoothGradientTest (Probability.intrinsicMeasure μ),
        (∀ v, g v = f (Probability.reconstruct μ v)) ∧
        g.toL2 = Energy.Euclidean.toIntrinsicL2 μ f.toL2 ∧ g.gradientEnergy ≤ f.gradientEnergy) ∧
    (∀ g : Energy.Euclidean.SmoothGradientTest (Probability.intrinsicMeasure μ),
      ∃ f : Energy.Euclidean.SmoothGradientTest μ,
        (∀ v, f (Probability.reconstruct μ v) = g v) ∧
        Energy.Euclidean.toIntrinsicL2 μ f.toL2 = g.toL2 ∧ f.gradientEnergy = g.gradientEnergy) ∧
    Energy.Euclidean.smoothGradientRelaxation μ =
      Energy.Canonical.energy μ ∧
    (∀ C : NNReal, Poincare.Ambient.Holds μ C ↔
      Poincare.Canonical.Holds μ C) ∧
    Poincare.Ambient.constant μ =
      Poincare.Canonical.constant μ :=
  ⟨Energy.Euclidean.SmoothGradientTest.exists_intrinsic_restriction μ,
    Energy.Euclidean.SmoothGradientTest.exists_ambient_extension μ,
    Energy.Euclidean.smoothGradientRelaxation_eq_canonical μ,
    Poincare.Ambient.holds_iff_canonical μ,
    Poincare.Ambient.constant_eq_canonical μ⟩

end Solutions.LemAmbientIntrinsicPoincareComparison

#check @Energy.Euclidean.SmoothGradientTest.exists_intrinsic_restriction
#check @Energy.Euclidean.SmoothGradientTest.exists_ambient_extension
#check @Energy.Euclidean.smoothGradientRelaxation_eq_canonical
#check @Poincare.Ambient.holds_iff_canonical
#check @Poincare.Ambient.constant_eq_canonical

-- Every dimension is permitted; no positivity hypothesis is hidden in the carrier.
#check (fun (d : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) ↦
  Energy.Euclidean.smoothGradientRelaxation_eq_canonical μ)

-- The intrinsic carrier can collapse to a point.
#check (fun (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) ↦
  Poincare.Ambient.holds_iff_canonical μ 0)

-- A Dirac law still fits the raw test restriction/extension statements.
#check (fun (g : Energy.Euclidean.SmoothGradientTest
    (Probability.intrinsicMeasure (Probability.ofMeasure (Measure.dirac (0 : ℝ))))) ↦
  Energy.Euclidean.SmoothGradientTest.exists_ambient_extension
    (Probability.ofMeasure (Measure.dirac (0 : ℝ))) g)

-- Equality transports the infinite value without converting it to a real constant.
#check (fun (μ : ProbabilityMeasure ℝ)
    (h : Poincare.Ambient.constant μ = ⊤) ↦
  (Poincare.Ambient.constant_eq_canonical μ).symm.trans h)

/--
info: 'Solutions.LemAmbientIntrinsicPoincareComparison.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemAmbientIntrinsicPoincareComparison.certificate

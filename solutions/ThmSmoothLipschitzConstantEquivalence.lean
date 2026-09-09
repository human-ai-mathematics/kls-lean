import FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison

/-!
# Lean certificate: `thm:smooth-lipschitz-constant-equivalence`

Status: proved / checked_by: lean. The sole certificate packages all eight public interfaces,
with their own quantifiers: pointwise slope, a.e. slope, energy, domain, finite bounds, coordinate
infima, ambient/intrinsic comparison, and the selected/literature corollary under intrinsic
absolute continuity. It does not supply the separate Borell input or a KLS proof.
Proof acceptance: `research/decisions/2026-09-06-smooth-literature-proofs.md`.
-/

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities
open FunctionalInequalities.Poincare
open scoped ContDiff

namespace Solutions.ThmSmoothLipschitzConstantEquivalence

universe u

/-- All eight contracts, without strengthening assumptions to package the individual components. -/
theorem certificate :
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (f : E → ℝ) (x : E) (_ : DifferentiableAt ℝ f x),
    Energy.LocalSlope.apply f x = ENNReal.ofReal ‖gradient f x‖) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E) [Measure.IsAddHaarMeasure m]
      (_ : (ν : Measure E) ≪ m)
    (f : E → ℝ) (_ : LocallyLipschitz f),
    (fun x ↦ Energy.LocalSlope.apply f x) =ᵐ[(ν : Measure E)]
      (fun x ↦ ENNReal.ofReal ‖gradient f x‖)) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E) [Measure.IsAddHaarMeasure m]
      (_ : (ν : Measure E) ≪ m)
    (f : E → ℝ) (_ : LocallyLipschitz f),
    Energy.LocalSlope.energy ν f = ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E)) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E) [Measure.IsAddHaarMeasure m]
      (_ : (ν : Measure E) ≪ m) (f : E → ℝ),
    Energy.LocalSlope.Admissible ν f ↔
      LocallyLipschitz f ∧ MemLp f 2 (ν : Measure E) ∧ MemLp (gradient f) 2 (ν : Measure E)) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (_ : (ν : Measure E) ≪ m) (C : NNReal),
    Poincare.SmoothTest.Holds (ν : Measure E) (C : ℝ) ↔ Poincare.LocalSlope.Holds ν C) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (_ : (ν : Measure E) ≪ m),
    Poincare.SmoothTest.constant (ν : Measure E) =
      ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C}, (C.1 : ENNReal)) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (_ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m),
    Poincare.SmoothTest.constant (μ : Measure E) =
        Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.constant μ) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
    [Measure.IsAddHaarMeasure m]
    (_ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m),
    Poincare.SmoothGradient.Intrinsic.constant μ =
      Poincare.LocalSlope.Intrinsic.constant μ) :=
  ⟨@Energy.LocalSlope.apply_eq_norm_gradient,
    @Energy.LocalSlope.apply_ae_eq_norm_gradient,
    @Energy.LocalSlope.energy_eq_lintegral_gradient,
    @Energy.LocalSlope.admissible_iff_memLp_gradient,
    @Poincare.SmoothTest.holds_iff_localSlope,
    @Poincare.SmoothTest.constant_eq_localSlope_infimum,
    @Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope,
    @Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope⟩

end Solutions.ThmSmoothLipschitzConstantEquivalence

#check @Energy.LocalSlope.apply_eq_norm_gradient
#check @Energy.LocalSlope.apply_ae_eq_norm_gradient
#check @Energy.LocalSlope.energy_eq_lintegral_gradient
#check @Energy.LocalSlope.admissible_iff_memLp_gradient
#check @Poincare.SmoothTest.holds_iff_localSlope
#check @Poincare.SmoothTest.constant_eq_localSlope_infimum
#check @Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope
#check @Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope

/--
info: 'Solutions.ThmSmoothLipschitzConstantEquivalence.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmSmoothLipschitzConstantEquivalence.certificate

/--
info: 'FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Energy.LocalSlope.apply_eq_norm_gradient

/--
info: 'FunctionalInequalities.Energy.LocalSlope.apply_ae_eq_norm_gradient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Energy.LocalSlope.apply_ae_eq_norm_gradient

/--
info: 'FunctionalInequalities.Energy.LocalSlope.energy_eq_lintegral_gradient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Energy.LocalSlope.energy_eq_lintegral_gradient

/--
info: 'FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Energy.LocalSlope.admissible_iff_memLp_gradient

/--
info: 'FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Poincare.SmoothTest.holds_iff_localSlope

/--
info: 'FunctionalInequalities.Poincare.SmoothTest.constant_eq_localSlope_infimum'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Poincare.SmoothTest.constant_eq_localSlope_infimum

/--
info: 'FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope

/--
info: 'FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope

import FunctionalInequalities.Poincare.Euclidean.LiteratureComparison

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
open FunctionalInequalities.KLS FunctionalInequalities.Poincare
open scoped ContDiff

namespace Solutions.ThmSmoothLipschitzConstantEquivalence

universe u

/-- All eight contracts, without strengthening assumptions to package the individual components. -/
theorem certificate :
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (f : E → ℝ) (x : E) (_ : DifferentiableAt ℝ f x),
    localSlope f x = ENNReal.ofReal ‖gradient f x‖) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E) [Measure.IsAddHaarMeasure m]
      (_ : (ν : Measure E) ≪ m)
    (f : E → ℝ) (_ : LocallyLipschitz f),
    (fun x ↦ localSlope f x) =ᵐ[(ν : Measure E)]
      (fun x ↦ ENNReal.ofReal ‖gradient f x‖)) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E) [Measure.IsAddHaarMeasure m]
      (_ : (ν : Measure E) ≪ m)
    (f : E → ℝ) (_ : LocallyLipschitz f),
    literatureEnergy ν f = ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E)) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E) [Measure.IsAddHaarMeasure m]
      (_ : (ν : Measure E) ≪ m) (f : E → ℝ),
    LiteratureAdmissible ν f ↔
      LocallyLipschitz f ∧ MemLp f 2 (ν : Measure E) ∧ MemLp (gradient f) 2 (ν : Measure E)) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (_ : (ν : Measure E) ≪ m) (C : NNReal),
    Holds (ν : Measure E) (C : ℝ) ↔ KLS.LiteratureHolds ν C) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (_ : (ν : Measure E) ≪ m),
    constant (ν : Measure E) =
      ⨅ C : {C : NNReal // KLS.LiteratureHolds ν C}, (C.1 : ENNReal)) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (_ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m),
    constant (μ : Measure E) =
        constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        KLS.literatureConstant μ) ∧
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
    [Measure.IsAddHaarMeasure m]
    (_ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m),
    Poincare.Canonical.constant μ =
      KLS.literatureConstant μ) :=
  ⟨@KLS.localSlope_eq_norm_gradient_of_differentiableAt,
    @KLS.localSlope_ae_eq_norm_gradient,
    @KLS.literatureEnergy_eq_lintegral_gradient,
    @KLS.literatureAdmissible_iff_memLp_gradient,
    @Poincare.Euclidean.holds_iff_literatureHolds,
    @Poincare.Euclidean.constant_eq_literatureInfimum,
    @Poincare.Euclidean.constant_eq_intrinsic_and_literature,
    @Poincare.Canonical.eq_literature_of_ac⟩

end Solutions.ThmSmoothLipschitzConstantEquivalence

#check @KLS.localSlope_eq_norm_gradient_of_differentiableAt
#check @KLS.localSlope_ae_eq_norm_gradient
#check @KLS.literatureEnergy_eq_lintegral_gradient
#check @KLS.literatureAdmissible_iff_memLp_gradient
#check @Poincare.Euclidean.holds_iff_literatureHolds
#check @Poincare.Euclidean.constant_eq_literatureInfimum
#check @Poincare.Euclidean.constant_eq_intrinsic_and_literature
#check @Poincare.Canonical.eq_literature_of_ac

/--
info: 'Solutions.ThmSmoothLipschitzConstantEquivalence.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmSmoothLipschitzConstantEquivalence.certificate

/--
info: 'FunctionalInequalities.KLS.localSlope_eq_norm_gradient_of_differentiableAt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.localSlope_eq_norm_gradient_of_differentiableAt

/--
info: 'FunctionalInequalities.KLS.localSlope_ae_eq_norm_gradient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.localSlope_ae_eq_norm_gradient

/--
info: 'FunctionalInequalities.KLS.literatureEnergy_eq_lintegral_gradient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.literatureEnergy_eq_lintegral_gradient

/--
info: 'FunctionalInequalities.KLS.literatureAdmissible_iff_memLp_gradient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.literatureAdmissible_iff_memLp_gradient

/--
info: 'FunctionalInequalities.Poincare.Euclidean.holds_iff_literatureHolds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.holds_iff_literatureHolds

/--
info: 'FunctionalInequalities.Poincare.Euclidean.constant_eq_literatureInfimum'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.constant_eq_literatureInfimum

/--
info: 'FunctionalInequalities.Poincare.Euclidean.constant_eq_intrinsic_and_literature'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Euclidean.constant_eq_intrinsic_and_literature

/--
info: 'FunctionalInequalities.Poincare.Canonical.eq_literature_of_ac'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.Canonical.eq_literature_of_ac

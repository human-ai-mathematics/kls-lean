import FunctionalInequalities.Energy.Cheeger
import FunctionalInequalities.KLS.Definitions

/-!
# Lean certificate: `cor:absolutely-continuous-relaxation-two-cheeger`

For every finite-dimensional real inner-product space and every Borel probability law `μ` whose
intrinsic law is absolutely continuous with respect to an additive Haar measure on the direction
space of its affine support, the sole `certificate` packages the absolutely continuous scope of
the Blueprint's Cheeger identification: the smooth-gradient relaxation of the intrinsic law is the
relaxed squared local slope, and therefore the selected canonical energy is twice the transported
metric Cheeger energy, `𝓔^can_μ = 2 Ch_μ`, on ambient real `L²(μ)`.

The Cheeger energy is the Blueprint's own local-slope convention, one half of the sequential
`L²`-relaxation of the squared local slope over the literature test class; the
asymptotic-Lipschitz convention is a separate definition and is never identified with it here.
Every compact-set log-concave law satisfies the hypothesis through the certified
`lem:logconcave-intrinsic-absolute-continuity`, so the identification is available throughout the
KLS routes. The singular case `thm:smooth-gradient-relaxation-two-cheeger` remains open and is not
claimed: no Poincaré inequality, no finiteness of any constant and no Cheeger--Buser comparison
follows from this certificate.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- The complete statement of the Blueprint corollary: under absolute continuity of the intrinsic
law the two relaxations of the intrinsic law agree, and the selected canonical energy is twice the
transported metric Cheeger energy on every ambient `L²(μ)` class. -/
theorem certificate (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (hac : (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) ≪ m) :
    Energy.SmoothGradient.relaxation (Probability.intrinsicMeasure μ) =
        Energy.LocalSlope.relaxation (Probability.intrinsicMeasure μ) ∧
      ∀ f : Lp ℝ 2 (μ : Measure E),
        Energy.SmoothGradient.Intrinsic.energy μ f = 2 * Energy.Cheeger.Intrinsic.energy μ f :=
  ⟨Energy.SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous _ m hac,
    fun f ↦ Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous
      μ m hac f⟩

/-- Every compact-set log-concave law satisfies the hypothesis: its intrinsic law is absolutely
continuous with respect to the canonical Haar measure of the direction space. -/
example {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) (f : Lp ℝ 2 (μ : Measure E)) :
    Energy.SmoothGradient.Intrinsic.energy μ f = 2 * Energy.Cheeger.Intrinsic.energy μ f :=
  (certificate μ Measure.addHaar (hμ.intrinsic_absolutelyContinuous Measure.addHaar)).2 f

/-- The selected Cheeger energy is the local-slope convention, one half of the relaxed squared
local slope; the asymptotic-Lipschitz convention is a separate definition. -/
example (ν : ProbabilityMeasure E) (f : Lp ℝ 2 (ν : Measure E)) :
    2 * Energy.Cheeger.energy ν f = Energy.LocalSlope.relaxation ν f :=
  Energy.Cheeger.two_mul_energy ν f

/-- The unconditional half of the identification needs no hypothesis: a globally smooth test is an
admissible local-slope test with the same energy. -/
example (ν : ProbabilityMeasure E) (f : Lp ℝ 2 (ν : Measure E)) :
    Energy.LocalSlope.relaxation ν f ≤ Energy.SmoothGradient.relaxation ν f :=
  Energy.SmoothGradient.localSlope_relaxation_le ν f

/-- Dimension zero: on a one-point coordinate space the Cheeger energy vanishes identically, so
the identification reads `0 = 2 * 0`. -/
example [Subsingleton E] (ν : ProbabilityMeasure E) (f : Lp ℝ 2 (ν : Measure E)) :
    Energy.Cheeger.energy ν f = 0 :=
  Energy.Cheeger.energy_eq_zero_of_subsingleton ν f

/-- Typed application on the Euclidean family in every dimension, with Lebesgue measure as the
Haar reference on the direction space. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hac : (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) ≪ Measure.addHaar)
    (f : Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    Energy.SmoothGradient.Intrinsic.energy μ f = 2 * Energy.Cheeger.Intrinsic.energy μ f :=
  (certificate μ Measure.addHaar hac).2 f

/--
info: 'Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger.certificate

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  FunctionalInequalities.Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger

end Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger

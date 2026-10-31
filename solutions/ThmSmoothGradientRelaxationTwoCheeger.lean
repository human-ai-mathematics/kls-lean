module

public import FunctionalInequalities.Energy.Cheeger.Identification
public import FunctionalInequalities.Probability.LogConcave

/-!
# Lean certificate: `thm:smooth-gradient-relaxation-two-cheeger`

For every finite-dimensional real inner-product space and **every** Borel probability law `μ` on it
— no absolute continuity, no density, no positive dimension, no log-concavity — the sole
`certificate` packages the Blueprint's Cheeger identification: the smooth-gradient relaxation of the
intrinsic law is the relaxed squared local slope, and therefore the selected canonical energy is
twice the transported metric Cheeger energy, `𝓔^can_μ = 2 Ch_μ`, on ambient real `L²(μ)`, with the
value `⊤` allowed on both sides and a one-point affine support giving `0 = 2 · 0`.

The Cheeger energy is the Blueprint's local-slope convention, one half of the sequential
`L²`-relaxation of the squared local slope over the literature test class. The asymptotic-Lipschitz
convention is a separate definition; `conventions_agree` records that it relaxes to the same
functional and gives the same Cheeger energy — a consequence of the identification, not an
identification by definition. The certified absolutely continuous scope
`cor:absolutely-continuous-relaxation-two-cheeger` is a special case. No Poincaré inequality, no
finiteness of any constant and no Cheeger–Buser comparison follows from this certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.ThmSmoothGradientRelaxationTwoCheeger

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The complete statement of the Blueprint theorem, for every Borel probability law: the two
relaxations of the intrinsic law agree, and the selected canonical energy is twice the transported
metric Cheeger energy on every ambient `L²(μ)` class. -/
theorem certificate (μ : ProbabilityMeasure E) :
    Energy.SmoothGradient.relaxation (Probability.intrinsicMeasure μ) =
        Energy.LocalSlope.relaxation (Probability.intrinsicMeasure μ) ∧
      ∀ f : Lp ℝ 2 (μ : Measure E),
        Energy.SmoothGradient.Intrinsic.energy μ f = 2 * Energy.Cheeger.Intrinsic.energy μ f :=
  ⟨Energy.SmoothGradient.relaxation_eq_localSlope _,
    fun f ↦ Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger μ f⟩

/-- The two Cheeger conventions agree on the coordinate space, for every Borel probability law:
the relaxed squared local slope is the relaxed squared asymptotic Lipschitz constant, and the two
Cheeger energies coincide. -/
theorem conventions_agree (ν : ProbabilityMeasure E) :
    Energy.LocalSlope.relaxation ν = Energy.AsymptoticLipschitz.relaxation ν ∧
      Energy.Cheeger.energy ν = Energy.Cheeger.ofAsymptoticLipschitz ν :=
  ⟨Energy.LocalSlope.relaxation_eq_asymptoticLipschitz ν,
    Energy.Cheeger.energy_eq_ofAsymptoticLipschitz ν⟩

/-- The absolutely continuous scope is recovered without its hypothesis. -/
example (μ : ProbabilityMeasure E) (f : Lp ℝ 2 (μ : Measure E)) :
    Energy.SmoothGradient.Intrinsic.energy μ f = 2 * Energy.Cheeger.Intrinsic.energy μ f :=
  (certificate μ).2 f

/-- Coordinate form: the smooth-gradient relaxation is twice the selected Cheeger energy. -/
example (ν : ProbabilityMeasure E) (f : Lp ℝ 2 (ν : Measure E)) :
    Energy.SmoothGradient.relaxation ν f = 2 * Energy.Cheeger.energy ν f :=
  Energy.SmoothGradient.relaxation_eq_two_mul_cheeger ν f

/-- Dimension zero: a one-point space, where every relaxed energy vanishes. -/
example [Subsingleton E] (ν : ProbabilityMeasure E) (f : Lp ℝ 2 (ν : Measure E)) :
    Energy.SmoothGradient.relaxation ν f = 2 * Energy.Cheeger.energy ν f :=
  Energy.SmoothGradient.relaxation_eq_two_mul_cheeger ν f

/-- Typed application on the Euclidean family in every dimension. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (f : Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    Energy.SmoothGradient.Intrinsic.energy μ f = 2 * Energy.Cheeger.Intrinsic.energy μ f :=
  (certificate μ).2 f

/--
info: 'Solutions.ThmSmoothGradientRelaxationTwoCheeger.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmSmoothGradientRelaxationTwoCheeger.certificate

/--
info: 'Solutions.ThmSmoothGradientRelaxationTwoCheeger.conventions_agree'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmSmoothGradientRelaxationTwoCheeger.conventions_agree

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_localSlope'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_localSlope

/--
info: 'FunctionalInequalities.Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger

end Solutions.ThmSmoothGradientRelaxationTwoCheeger

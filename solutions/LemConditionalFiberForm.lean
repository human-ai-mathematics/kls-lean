import FunctionalInequalities.KLS.ConditionalFiber.Closed
import FunctionalInequalities.KLS.Definitions
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `lem:conditional-fiber-form`

For every Borel probability law `μ` on a finite-dimensional real inner-product space and every
probability law `ρ` on its unit sphere, the conditional-fiber form of `def:conditional-fiber-form`,
packaged as the extended functional `KLS.ConditionalFiber.functional μ ρ` on `L²(μ)`, is a
Dirichlet energy: densely defined, closed (lower semicontinuous), quadratic and Markovian. On every
nondegenerate fiber it is the squared jump integral against the symmetric two-point measure
`μ_{θ,z} ⊗ μ_{θ,z}`, divided by twice the fiber variance; the two-point measure is invariant under
the exchange of its coordinates (reversibility). Every globally `L`-Lipschitz test has energy at
most `d L²`, which is the quantitative form of the density argument.

The Blueprint states the lemma for full-dimensional log-concave laws with a density, finite second
moment and an admissible frame; the Lean theorem needs none of these hypotheses. No comparison with
a gradient energy, no fiber Poincaré input, no frame bound and no Poincaré inequality is claimed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory FunctionalInequalities

namespace Solutions.LemConditionalFiberForm

open KLS.ConditionalFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The complete statement of the Blueprint: the conditional-fiber form is a Dirichlet energy on
`L²(μ)` (densely defined, closed, quadratic, Markovian); on nondegenerate fibers it is the
symmetric two-point jump form; the two-point measure is reversible; and globally Lipschitz tests
have energy at most `d L²`. -/
theorem certificate (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) :
    Energy.Dirichlet (μ : Measure E) (functional μ ρ) ∧
    (∀ (κ : Kernel (Direction E × E) ℝ) [IsMarkovKernel κ] (b : Direction E × E) (f : E → ℝ),
      Measurable f → Nondegenerate κ b →
        energyAt κ b f = jump κ b f / (2 * evariance id (κ b))) ∧
    (∀ (κ : Kernel (Direction E × E) ℝ) [IsMarkovKernel κ] (b : Direction E × E),
      (twoPointMeasure κ b).map Prod.swap = twoPointMeasure κ b) ∧
    (∀ (g : E → ℝ) (L : NNReal), LipschitzWith L g →
      energy μ ρ g ≤ (Module.finrank ℝ E : ENNReal) * (L : ENNReal) ^ 2) :=
  ⟨dirichlet μ ρ, fun κ _ b _ hf hb ↦ energyAt_eq_jump_div κ b hf hb,
    fun κ _ b ↦ twoPointMeasure_swap κ b, fun _ _ hg ↦ energy_le_of_lipschitzWith μ ρ hg⟩

/-- The Blueprint scope: a compact-set log-concave law with finite second moment and an admissible
frame. The certified theorem uses none of these hypotheses; they are recorded only to display the
stated scope. -/
example (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (_hμ : KLS.LogConcave μ) (_hmoment : MemLp id 2 (μ : Measure E)) (_hρ : Admissible μ ρ) :
    Energy.Dirichlet (μ : Measure E) (functional μ ρ) :=
  (certificate μ ρ).1

/-- Typed application on the Euclidean family in every positive dimension: dense finite domain and
lower semicontinuity of the form on `L²(μ)`. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin (n + 1))))
    (ρ : ProbabilityMeasure (Direction (EuclideanSpace ℝ (Fin (n + 1))))) :
    Dense (functional μ ρ).domain ∧
      LowerSemicontinuous fun f : Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ↦
        form μ ρ f :=
  ⟨(certificate μ ρ).1.closedQuadratic.dense_domain,
    (certificate μ ρ).1.closedQuadratic.lowerSemicontinuous⟩

/-- The Markov inequality on the Euclidean family: normal contractions do not increase the form. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin (n + 1))))
    (ρ : ProbabilityMeasure (Direction (EuclideanSpace ℝ (Fin (n + 1)))))
    (φ : Energy.NormalContraction)
    (f : Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin (n + 1))))) :
    form μ ρ (φ.compL2 (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) f) ≤ form μ ρ f :=
  (certificate μ ρ).1.markovian φ f

/-- Smooth compactly supported classes lie in the finite domain on the Euclidean family. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin (n + 1))))
    (ρ : ProbabilityMeasure (Direction (EuclideanSpace ℝ (Fin (n + 1))))) :
    (Energy.WeightedGradient.smoothCore μ :
      Set (Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))))) ⊆ domain μ ρ :=
  smoothCore_subset_domain μ ρ

/-- Dimension zero: the unit sphere is empty, so no direction law exists and the lemma is vacuous
there, matching the Blueprint's restriction to `d ≥ 1`. -/
example : IsEmpty (ProbabilityMeasure (Direction (EuclideanSpace ℝ (Fin 0)))) := by
  refine ⟨fun ρ ↦ ?_⟩
  have huniv : (ρ : Measure (Direction (EuclideanSpace ℝ (Fin 0)))) Set.univ = 1 := measure_univ
  have hempty : (Set.univ : Set (Direction (EuclideanSpace ℝ (Fin 0)))) = ∅ := by
    ext θ
    have hθ := θ.2
    rw [Subsingleton.elim θ.1 0, norm_zero] at hθ
    exact absurd hθ zero_ne_one
  rw [hempty, measure_empty] at huniv
  exact zero_ne_one huniv

/--
info: 'Solutions.LemConditionalFiberForm.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemConditionalFiberForm.certificate

/--
info: 'FunctionalInequalities.Probability.two_mul_evariance_eq_lintegral_prod'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Probability.two_mul_evariance_eq_lintegral_prod

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.energyAt_eq_jump_div'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.energyAt_eq_jump_div

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.twoPointMeasure_swap'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.twoPointMeasure_swap

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.energy_le_of_lipschitzWith'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.energy_le_of_lipschitzWith

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.dense_domain'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.dense_domain

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.form_parallelogram'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.form_parallelogram

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.energy_le_liminf'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.energy_le_liminf

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.lowerSemicontinuous_form'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.lowerSemicontinuous_form

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.markovian'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.markovian

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.closedQuadratic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.closedQuadratic

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.dirichlet'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.dirichlet

end Solutions.LemConditionalFiberForm

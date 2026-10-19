import FunctionalInequalities.KLS.LogConcave.ConditionalFiber
import FunctionalInequalities.Probability.LogConcave

/-!
# Lean certificate: `cor:conditional-fiber-twelve-bound`

For every finite-dimensional real inner-product space, every compact-set log-concave probability
law `μ` absolutely continuous with respect to a Haar measure and every admissible frame `ρ`, the
sole `certificate` packages the four steps of the Blueprint corollary: base-law almost every
conditional fiber of the joint law is a log-concave law on the line; the sharp one-dimensional
bound turns this into the fiber hypothesis `FiberBound μ ρ 4`; the comparison lemma then gives
`D_{μ,ρ}(f) ≤ 4 ∫‖∇f‖² dμ < ∞` on the literature test domain; and a finite form-gap bound `C`
gives `C_P^lit(μ) ≤ 4 C`.

The Blueprint corollary is stated with the constant `4`, which is what the sharp one-dimensional
input `thm:one-dimensional-logconcave-poincare` supplies. The literature's `12` is the immediate
weakening and is recorded below as an `example`. "Full-dimensional" is read as absolute continuity
with respect to a Haar measure, as in the comparison lemma; the finite second moment is a field of
the admissible frame. No frame bound, no Poincaré inequality for `μ` and no KLS statement is
claimed: `q:conditional-fiber-frame` remains open.
-/

noncomputable section

open MeasureTheory ProbabilityTheory FunctionalInequalities

namespace Solutions.CorConditionalFiberTwelveBound

open KLS.ConditionalFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The complete statement of the Blueprint corollary: almost every conditional fiber of a
full-dimensional log-concave law is log-concave on the line, hence the fiber hypothesis holds with
`κ = 4`, the conditional-fiber energy of every literature test is at most `4` times its finite
gradient energy, and a finite form-gap bound `C` gives `C_P^lit(μ) ≤ 4 C`. -/
theorem certificate (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hμ : KLS.LogConcave μ) (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) :
    (∀ᵐ b ∂baseLaw μ ρ,
      KLS.LogConcave (⟨kernel μ ρ b, inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    FiberBound μ ρ 4 ∧
    (∀ f : E → ℝ, Energy.LocalSlope.Admissible μ f →
      energy μ ρ f ≤ 4 * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤) ∧
    (∀ C : NNReal,
      (∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) →
        Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * (C : ENNReal)) :=
  ⟨hμ.ae_conditionalFiber_logConcave hρ m hac,
    hμ.conditionalFiber_fiberBound_four hρ m hac,
    fun _ hf ↦ hμ.conditionalFiber_energy_le_four_mul hρ m hac hf,
    fun _ hform ↦ hμ.conditionalFiber_literatureConstant_le_four_mul hρ m hac hform⟩

/-- The displayed inequality in its gradient form `D_{μ,ρ}(f) ≤ 4 ∫‖∇f‖² dμ`: under absolute
continuity the local-slope energy is the extended integral of the squared gradient norm. -/
example (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hμ : KLS.LogConcave μ) (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) {f : E → ℝ} (hf : Energy.LocalSlope.Admissible μ f) :
    energy μ ρ f ≤ 4 * ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(μ : Measure E) := by
  rw [← Energy.LocalSlope.energy_eq_lintegral_gradient μ m hac f hf.locallyLipschitz]
  exact ((certificate μ ρ hμ hρ m hac).2.2.1 f hf).1

/-- The literature's `12`, the immediate weakening of the certified `4`. -/
example (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hμ : KLS.LogConcave μ) (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) {f : E → ℝ} (hf : Energy.LocalSlope.Admissible μ f) {C : NNReal}
    (hform : ∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) :
    (energy μ ρ f ≤ 12 * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤) ∧
      Poincare.LocalSlope.Intrinsic.constant μ ≤ 12 * (C : ENNReal) :=
  ⟨hμ.conditionalFiber_energy_le_twelve_mul_of_four hρ m hac hf,
    hμ.conditionalFiber_literatureConstant_le_twelve_mul_of_four hρ m hac hform⟩

/-- Finite gradient energy puts the literature test in the maximal finite form domain. -/
example (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hμ : KLS.LogConcave μ) (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) {f : E → ℝ} (hf : Energy.LocalSlope.Admissible μ f) :
    hf.memLp_two.toLp f ∈ domain μ ρ := by
  show form μ ρ _ ≠ ⊤
  rw [form_toLp μ ρ f hf.locallyLipschitz.continuous.measurable hf.memLp_two]
  exact ((certificate μ ρ hμ hρ m hac).2.2.1 f hf).2

/-- The corollary is an instance of the parameterized comparison: the certified fiber hypothesis
with `κ = 4` is exactly what `lem:conditional-fiber-energy-comparison` consumes. -/
example (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hμ : KLS.LogConcave μ) (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) {C : NNReal}
    (hform : ∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * (C : ENNReal) :=
  literatureConstant_le_of_fiberBound μ ρ hρ m hac (certificate μ ρ hμ hρ m hac).2.1 hform

/-- Typed application on the Euclidean family in every positive dimension, with Lebesgue measure
as the Haar reference: this is the Blueprint's full-dimensional `μ` on `ℝ^d`. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin (n + 1))))
    (ρ : ProbabilityMeasure (Direction (EuclideanSpace ℝ (Fin (n + 1)))))
    (hμ : KLS.LogConcave μ) (hρ : Admissible μ ρ)
    (hac : (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≪ volume) {C : NNReal}
    (hform : ∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * (C : ENNReal) :=
  (certificate μ ρ hμ hρ volume hac).2.2.2 C hform

/-- Dimension zero: the unit sphere is empty, so no admissible frame exists and the corollary is
vacuous there, matching the Blueprint's restriction to `d ≥ 1`. -/
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
info: 'Solutions.CorConditionalFiberTwelveBound.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.CorConditionalFiberTwelveBound.certificate

/--
info: 'FunctionalInequalities.KLS.LogConcave.ae_conditionalFiber_logConcave'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.ae_conditionalFiber_logConcave

/--
info: 'FunctionalInequalities.KLS.LogConcave.conditionalFiber_literatureConstant_le_four_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.conditionalFiber_literatureConstant_le_four_mul

end Solutions.CorConditionalFiberTwelveBound

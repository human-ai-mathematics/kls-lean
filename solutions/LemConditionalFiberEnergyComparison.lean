import FunctionalInequalities.KLS.ConditionalFiber.EnergyComparison
import FunctionalInequalities.Probability.LogConcave

/-!
# Lean certificate: `lem:conditional-fiber-energy-comparison`

For every finite-dimensional real inner-product space, every probability law `μ` absolutely
continuous with respect to a Haar measure, every admissible frame `ρ` and every finite `κ ≥ 0`
satisfying the fiber hypothesis `FiberBound μ ρ κ` (the literature Poincaré constant of almost
every nondegenerate conditional fiber is at most `κ` times the fiber variance), the sole
`certificate` packages the two conclusions of the Blueprint lemma: every locally Lipschitz,
square-integrable test with finite local-slope energy satisfies
`D_{μ,ρ}(f) ≤ κ · ∫‖∇f‖² dμ < ∞`, and every finite form-gap bound `Var_μ ≤ C · D_{μ,ρ}` on the
maximal finite form domain gives `C_P^lit(μ) ≤ κ C`.

The Blueprint states the lemma for `ℝ^d` with Lebesgue measure and a finite second moment; the
Lean theorem uses a general Haar reference measure, and the second moment is part of the admissible
frame. No value of `κ`, no log-concavity, no fiber Poincaré input and no KLS statement is claimed:
the corollary `cor:conditional-fiber-twelve-bound` is a separate node.
-/

noncomputable section

open MeasureTheory ProbabilityTheory FunctionalInequalities

namespace Solutions.LemConditionalFiberEnergyComparison

open KLS.ConditionalFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The complete statement of the Blueprint: under the fiber hypothesis with input `κ`, the
conditional-fiber energy of every literature test is at most `κ` times its finite local-slope
(gradient) energy, and a finite form-gap bound `C` on the maximal finite form domain gives
`C_P^lit(μ) ≤ κ C`. -/
theorem certificate (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) {κ : NNReal} (hfiber : FiberBound μ ρ κ) :
    (∀ f : E → ℝ, Energy.LocalSlope.Admissible μ f →
      energy μ ρ f ≤ (κ : ENNReal) * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤) ∧
    (∀ C : NNReal,
      (∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) →
        Poincare.LocalSlope.Intrinsic.constant μ ≤ (κ : ENNReal) * (C : ENNReal)) :=
  ⟨fun _ hf ↦ energy_le_of_fiberBound μ ρ hρ m hac hfiber hf,
    fun _ hform ↦ literatureConstant_le_of_fiberBound μ ρ hρ m hac hfiber hform⟩

/-- The Blueprint scope: a compact-set log-concave law with finite second moment. The certified
theorem uses neither hypothesis (the second moment is a field of the admissible frame); they are
recorded only to display the stated scope. -/
example (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (_hμ : KLS.LogConcave μ) (_hmoment : MemLp id 2 (μ : Measure E)) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m)
    {κ : NNReal} (hfiber : FiberBound μ ρ κ) {C : NNReal}
    (hform : ∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (κ : ENNReal) * (C : ENNReal) :=
  (certificate μ ρ hρ m hac hfiber).2 C hform

/-- The displayed inequality in its gradient form `D_{μ,ρ}(f) ≤ κ ∫‖∇f‖² dμ`: the local-slope
energy of a locally Lipschitz test is the extended integral of the squared gradient norm. -/
example (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) {κ : NNReal} (hfiber : FiberBound μ ρ κ)
    {f : E → ℝ} (hf : Energy.LocalSlope.Admissible μ f) :
    energy μ ρ f ≤
      (κ : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(μ : Measure E) := by
  rw [← Energy.LocalSlope.energy_eq_lintegral_gradient μ m hac f hf.locallyLipschitz]
  exact ((certificate μ ρ hρ m hac hfiber).1 f hf).1

/-- Finite gradient energy puts the literature test in the maximal finite form domain. -/
example (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) {κ : NNReal} (hfiber : FiberBound μ ρ κ)
    {f : E → ℝ} (hf : Energy.LocalSlope.Admissible μ f) :
    hf.memLp_two.toLp f ∈ domain μ ρ := by
  show form μ ρ _ ≠ ⊤
  rw [form_toLp μ ρ f hf.locallyLipschitz.continuous.measurable hf.memLp_two]
  exact ((certificate μ ρ hρ m hac hfiber).1 f hf).2

/-- Typed application on the Euclidean family in every positive dimension, with Lebesgue measure
as the Haar reference: this is the Blueprint's `μ ≪ Leb_{ℝ^d}`. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin (n + 1))))
    (ρ : ProbabilityMeasure (Direction (EuclideanSpace ℝ (Fin (n + 1)))))
    (hρ : Admissible μ ρ) (hac : (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≪ volume)
    {κ : NNReal} (hfiber : FiberBound μ ρ κ) {C : NNReal}
    (hform : ∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (κ : ENNReal) * (C : ENNReal) :=
  (certificate μ ρ hρ volume hac hfiber).2 C hform

/-- Dimension zero: the unit sphere is empty, so no admissible frame exists and the lemma is
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
info: 'Solutions.LemConditionalFiberEnergyComparison.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemConditionalFiberEnergyComparison.certificate

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.energy_le_of_fiberBound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.energy_le_of_fiberBound

/--
info: 'FunctionalInequalities.KLS.ConditionalFiber.literatureConstant_le_of_fiberBound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.literatureConstant_le_of_fiberBound

end Solutions.LemConditionalFiberEnergyComparison

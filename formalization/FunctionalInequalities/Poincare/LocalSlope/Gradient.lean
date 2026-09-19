import FunctionalInequalities.Energy.LocalSlope.Gradient
import FunctionalInequalities.Poincare.LocalSlope.Basic
import FunctionalInequalities.KLS.LogConcave.Density.AbsoluteContinuity

/-!
# The literature Poincaré constant in gradient form

The literature-Poincaré clause of `thm:klartag-density-frontend-identification`.

`def:literature-poincare-constant` defines `C_P^lit` through the **local metric slope**
`Energy.LocalSlope.apply`. The Klartag frontend states the same constant through the **gradient**:
`C_P^lit(μ)` is the infimum of the finite `C ≥ 0` for which `Var_ν(g) ≤ C ∫ ‖∇g‖² dν` holds for
every locally Lipschitz `g ∈ L²(ν)` of finite gradient energy, where `ν` is the intrinsic law.

No new definition is introduced: the gradient-form validity is written out inline, and the optimal
constant remains `Poincare.LocalSlope.Intrinsic.constant`. The analysis is already done in
`Energy/LocalSlope/Gradient.lean` (Rademacher plus absolute continuity); what is proved here is
only the transport of that identification through the validity predicate and its infimum.

Read `holds_iff_memLp_gradient` first, then `Intrinsic.constant_eq_iInf_gradient` and its
log-concave specialization. Route: `research/decisions/2026-09-19-klartag-literature-poincare-route.md`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace

namespace FunctionalInequalities.Poincare.LocalSlope

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- `Q1`: for an absolutely continuous law the local-slope and gradient descriptions of a valid
finite constant agree. Both directions rewrite the same two proved identifications, so no
inequality is weakened: the admissible class and the energy are transported simultaneously. -/
theorem holds_iff_memLp_gradient (ν : ProbabilityMeasure V) (m : Measure V)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure V) ≪ m) (C : NNReal) :
    Holds ν C ↔
      ∀ g : V → ℝ, LocallyLipschitz g → MemLp g 2 (ν : Measure V) →
        MemLp (gradient g) 2 (ν : Measure V) →
        evariance g (ν : Measure V) ≤
          (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(ν : Measure V) := by
  constructor
  · intro hC g hlip hL2 hgrad
    have hadm : Energy.LocalSlope.Admissible ν g :=
      (Energy.LocalSlope.admissible_iff_memLp_gradient ν m hν g).mpr ⟨hlip, hL2, hgrad⟩
    have := hC g hadm
    rwa [Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν g hlip] at this
  · intro hC g hadm
    obtain ⟨hlip, hL2, hgrad⟩ :=
      (Energy.LocalSlope.admissible_iff_memLp_gradient ν m hν g).mp hadm
    rw [Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν g hlip]
    exact hC g hlip hL2 hgrad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- `Q2`: the literature optimum of an absolutely continuous intrinsic law, in gradient form.
The two infima range over subtypes cut out by equivalent predicates, so each bounds the other. -/
theorem Intrinsic.constant_eq_iInf_gradient (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (hμ : (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) ≪ m) :
    Poincare.LocalSlope.Intrinsic.constant μ =
      ⨅ C : {C : NNReal //
          ∀ g : (Probability.affineSupport μ).direction → ℝ, LocallyLipschitz g →
            MemLp g 2 (Probability.intrinsicMeasure μ :
              Measure (Probability.affineSupport μ).direction) →
            MemLp (gradient g) 2 (Probability.intrinsicMeasure μ :
              Measure (Probability.affineSupport μ).direction) →
            evariance g (Probability.intrinsicMeasure μ :
                Measure (Probability.affineSupport μ).direction) ≤
              (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2
                ∂(Probability.intrinsicMeasure μ :
                  Measure (Probability.affineSupport μ).direction)},
        (C.1 : ENNReal) := by
  have hiff := holds_iff_memLp_gradient (Probability.intrinsicMeasure μ) m hμ
  apply le_antisymm
  · refine le_iInf fun C => ?_
    exact iInf_le_of_le ⟨C.1, (hiff C.1).mpr C.2⟩ le_rfl
  · refine le_iInf fun C => ?_
    exact iInf_le_of_le ⟨C.1, (hiff C.1).mp C.2⟩ le_rfl

omit [CompleteSpace E] in
/-- `Q0`: the literature-Poincaré clause of `thm:klartag-density-frontend-identification`.

Every finite-dimensional log-concave law has an absolutely continuous intrinsic law, so its
literature optimum is the gradient-form optimum. The reference Haar measure is produced here
rather than assumed: the direction of the affine support is a finite-dimensional normed space,
hence weakly locally compact, so it carries an additive Haar measure. The statement therefore
mentions no reference measure, and the constant does not depend on the choice. -/
theorem Intrinsic.constant_eq_iInf_gradient_of_logConcave {μ : ProbabilityMeasure E}
    (hμ : KLS.LogConcave μ) :
    Poincare.LocalSlope.Intrinsic.constant μ =
      ⨅ C : {C : NNReal //
          ∀ g : (Probability.affineSupport μ).direction → ℝ, LocallyLipschitz g →
            MemLp g 2 (Probability.intrinsicMeasure μ :
              Measure (Probability.affineSupport μ).direction) →
            MemLp (gradient g) 2 (Probability.intrinsicMeasure μ :
              Measure (Probability.affineSupport μ).direction) →
            evariance g (Probability.intrinsicMeasure μ :
                Measure (Probability.affineSupport μ).direction) ≤
              (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2
                ∂(Probability.intrinsicMeasure μ :
                  Measure (Probability.affineSupport μ).direction)},
        (C.1 : ENNReal) := by
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (Probability.affineSupport μ).direction) := inferInstance
  have hm : (Measure.addHaarMeasure K₀).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_addHaarMeasure K₀
  exact Intrinsic.constant_eq_iInf_gradient μ (Measure.addHaarMeasure K₀)
    (hμ.intrinsic_absolutelyContinuous _)

end FunctionalInequalities.Poincare.LocalSlope

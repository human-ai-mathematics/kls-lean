module

public import FunctionalInequalities.KLS.LogConcave.Poincare
public import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Scope audit for the literature-Poincaré clause of `thm:klartag-density-frontend-identification`

Every obligation `Q1`, `Q2` and the target `Q0` of
`research/audits/Poincare/KlartagLiteratureRouteStatements.lean` is restated here **verbatim** — the
propositions preserve the route contracts — and discharged through
`Poincare/LocalSlope/Gradient.lean` and `KLS/LogConcave/Poincare.lean`. A renamed binder, a
reordered
hypothesis or a weakened conclusion would fail to elaborate here.

The affine-origin independence `Q3` of `KlartagLiteratureRouteStatements.lean` has no
proposition of its own in this file, and that is the finding, not an omission:
`Probability.intrinsicMeasure` is defined without a choice of affine origin, so the Blueprint
sentence is discharged by the existing definition. `route_Q0` additionally carries no reference
measure in its statement — the Haar measure is constructed inside its proof — so the constant
depends on neither the origin nor the reference.

The Buser half `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` of
`thm:logconcave-cheeger-poincare-comparison` is outside this client's scope; its current source is
`KLS/LogConcave/Density/GaussianSmoothing/Buser.lean`, with client
`research/audits/Density/GaussianBuserPassageAudit.lean`. This client also makes no dimension-free
KLS claim.

Two boundary cases are recorded after the route items: a zero-dimensional direction space, where
both sides collapse to `0`, and the transport of a valid constant through `route_Q1` for a law
that is already absolutely continuous.

The axiom reports at the end cover the gradient/optimal-constant source declarations and every
theorem of
this client.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set FunctionalInequalities
  FunctionalInequalities.KLS
open scoped ENNReal NNReal

namespace KlartagLiteraturePoincareAudit

/-! ### The two descriptions of validity agree -/

/-- `Q1` of `KlartagLiteratureRouteStatements.lean`, restated verbatim and discharged. -/
theorem route_Q1 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) (m : Measure V) [Measure.IsAddHaarMeasure m],
      (ν : Measure V) ≪ m → ∀ C : NNReal,
        Poincare.LocalSlope.Holds ν C ↔
          ∀ g : V → ℝ, LocallyLipschitz g → MemLp g 2 (ν : Measure V) →
            MemLp (gradient g) 2 (ν : Measure V) →
            evariance g (ν : Measure V) ≤
              (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(ν : Measure V) := by
  intro V _ _ _ _ _ _ _ ν m _ hν C
  exact Poincare.LocalSlope.holds_iff_memLp_gradient ν m hν C

/-! ### The optimal constant in gradient form, for any absolutely continuous intrinsic law -/

/-- `Q2` of `KlartagLiteratureRouteStatements.lean`, restated verbatim and discharged. -/
theorem route_Q2 :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
      [Measure.IsAddHaarMeasure m],
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m →
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
  intro E _ _ _ _ _ _ _ μ m _ hμ
  exact Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient μ m hμ

/-! ### The target: the literature-Poincaré clause for log-concave laws -/

/-- `Q0` of `KlartagLiteratureRouteStatements.lean`, restated verbatim and discharged. -/
theorem route_Q0 :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      {μ : ProbabilityMeasure E}, LogConcave μ →
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
  intro E _ _ _ _ _ _ _ μ hμ
  exact Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient_of_logConcave hμ

/-! ### Boundary cases -/

/-- A zero-dimensional direction space: the literature optimum is `0`, so `route_Q0` reads
`0 = ⨅ …` there and the gradient-form infimum is forced to `0` as well. -/
theorem boundary_direction_subsingleton {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [FiniteDimensional ℝ E] {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) [Subsingleton (Probability.affineSupport μ).direction] :
    (⨅ C : {C : NNReal //
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
      (C.1 : ENNReal)) = 0 := by
  rw [← Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient_of_logConcave hμ]
  exact Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_direction_subsingleton μ

/-- Transport of a single valid constant: for an absolutely continuous law, a constant valid in
the local-slope sense bounds the variance of every locally Lipschitz `L²` test of finite gradient
energy. This is the `mp` direction of `route_Q1`, in the form used by its consumers. -/
theorem boundary_transport {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] (ν : ProbabilityMeasure V) (m : Measure V)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure V) ≪ m) {C : NNReal}
    (hC : Poincare.LocalSlope.Holds ν C) {g : V → ℝ} (hlip : LocallyLipschitz g)
    (hL2 : MemLp g 2 (ν : Measure V)) (hgrad : MemLp (gradient g) 2 (ν : Measure V)) :
    evariance g (ν : Measure V) ≤
      (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(ν : Measure V) :=
  (Poincare.LocalSlope.holds_iff_memLp_gradient ν m hν C).mp hC g hlip hL2 hgrad

end KlartagLiteraturePoincareAudit

#print axioms FunctionalInequalities.Poincare.LocalSlope.holds_iff_memLp_gradient
#print axioms FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient
#print axioms
  FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient_of_logConcave

#print axioms KlartagLiteraturePoincareAudit.route_Q1
#print axioms KlartagLiteraturePoincareAudit.route_Q2
#print axioms KlartagLiteraturePoincareAudit.route_Q0
#print axioms KlartagLiteraturePoincareAudit.boundary_direction_subsingleton
#print axioms KlartagLiteraturePoincareAudit.boundary_transport

import FunctionalInequalities.KLS.LogConcave.Poincare

/-!
# Scope audit for the literature-Poincaré clause of `thm:klartag-density-frontend-identification`

Every obligation `Q1`, `Q2` and the target `Q0` of
`research/audits/KlartagLiteraturePoincareRouteStatements.lean` is restated here **verbatim** — the
propositions are copied character for character from that route snapshot — and discharged from the
single new hole-free module `Poincare/LocalSlope/Gradient.lean`. A renamed binder, a reordered
hypothesis or a weakened conclusion would fail to elaborate here.

`Q3` (affine-origin independence) has no proposition of its own in this file, and that is the
finding, not an omission: `Probability.intrinsicMeasure` is defined without a choice of affine
origin, so the Blueprint sentence is discharged by the existing definition. `Q0` additionally
carries no reference measure in its statement — the Haar measure is constructed inside its proof —
so the constant depends on neither the origin nor the reference.

Out of scope, deliberately absent: the Buser half `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` of
`thm:logconcave-cheeger-poincare-comparison`, which stays imported mathematics in dimension
`n ≥ 2`, and the dimension-free KLS bound.

Two boundary cases are recorded after the route items: a zero-dimensional direction space, where
both sides collapse to `0`, and the transport of a valid constant through `Q1` for a law that is
already absolutely continuous.

The axiom reports at the end cover every public declaration of the new module and every theorem of
this client.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set FunctionalInequalities
  FunctionalInequalities.KLS
open scoped ENNReal NNReal

namespace KlartagLiteraturePoincareAudit

/-! ### `Q1` — the two descriptions of validity agree -/

/-- `Q1`, restated verbatim and discharged. -/
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

/-! ### `Q2` — the optimal constant in gradient form, for any absolutely continuous intrinsic law -/

/-- `Q2`, restated verbatim and discharged. -/
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

/-! ### `Q0` — the target: the literature-Poincaré clause for log-concave laws -/

/-- `Q0`, restated verbatim and discharged. -/
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

/-- A zero-dimensional direction space: the literature optimum is `0`, so `Q0` reads `0 = ⨅ …`
there and the gradient-form infimum is forced to `0` as well. -/
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
energy. This is the `mp` direction of `Q1` used as it will be used downstream. -/
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
#print axioms FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient_of_logConcave

#print axioms KlartagLiteraturePoincareAudit.route_Q1
#print axioms KlartagLiteraturePoincareAudit.route_Q2
#print axioms KlartagLiteraturePoincareAudit.route_Q0
#print axioms KlartagLiteraturePoincareAudit.boundary_direction_subsingleton
#print axioms KlartagLiteraturePoincareAudit.boundary_transport

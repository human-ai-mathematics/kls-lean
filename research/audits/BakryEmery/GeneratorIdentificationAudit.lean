import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Basic

/-!
# Scope audit for the generator identification on smooth tests

This client imports the three modules `Analysis/BakryEmery/IntegrationByParts/Basic.lean`,
`Analysis/Semigroup/AdjointClosure.lean` and `KLS/LogConcave/HeatSemigroup/Generator/Basic.lean`
(the last through its imports) and discharges the two route obligations `G0` and `G1` of
`research/audits/BakryEmery/InterfaceRouteStatements.lean`. The propositions are restated
**verbatim** from that file as `route_G0` and `route_G1`; the proofs are one `exact` each, after
weakening `ContDiff ℝ ∞` to the `C¹`/`C²` regularity the library theorems actually use.

Nothing about the carré du champ, the convex Hessian, Bochner or `Γ₂ ≥ 0`, nor about regular
representatives of `P_t f` or gradient estimates, is claimed here. `route_G1` is a statement about
each individual class `[f]`, `f ∈ C_c^∞`: it does **not** say that `C_c^∞` is an operator core of
`T̄†T̄`, nor that the closure of `-ℒ` on `C_c^∞` is `T̄†T̄`.

The boundary section records three consistency uses of `route_G0`: with the constant test `g = 1`
the weighted Laplacian has zero mean (infinitesimal conservation of integrals); with `g = f` the
Dirichlet form of the differential expression is `∫ ‖∇f‖² dν`, matching
`inner_adjointComp_self_eq`; and `ℒ` is symmetric on `C_c^∞`.

The axiom reports at the end cover every public declaration of the three imported modules and every
theorem of this client; each must list only `propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.Semigroup
  FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace BakryEmeryGeneratorAudit

/-! ### Weighted integration by parts on compactly supported smooth tests -/

theorem route_G0 : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (m : Measure E) [m.IsAddHaarMeasure] (U f g : E → ℝ) (μ : ProbabilityMeasure E),
    (μ : Measure E) = m.tilted (-U) → ContDiff ℝ ∞ U →
    ContDiff ℝ ∞ f → HasCompactSupport f →
    ContDiff ℝ ∞ g → HasCompactSupport g →
    (∫ x, inner ℝ (gradient f x) (gradient g x) ∂(μ : Measure E)) =
      ∫ x, (-(Laplacian.laplacian f x - inner ℝ (gradient U x) (gradient f x))) * g x
        ∂(μ : Measure E) := by
  intro E _ _ _ _ _ _ _ m _ U f g μ hμ hU hf hfc hg _
  rw [hμ]
  exact integral_inner_gradient_tilted m (hU.of_le (WithTop.coe_le_coe.mpr le_top))
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc (hg.of_le (WithTop.coe_le_coe.mpr le_top))

/-! ### Identify `A = T̄†T̄` with `-ℒ` on `C_c^∞` -/

theorem route_G1 : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure] (U : E → ℝ)
    (hμ : KLS.LogConcave μ) (hi : (interior (μ : Measure E).support).Nonempty),
    (μ : Measure E) = m.tilted (-U) → ContDiff ℝ ∞ U →
    ∀ (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ∃ hLf : MemLp
          (fun x => -(Laplacian.laplacian f x - inner ℝ (gradient U x) (gradient f x)))
          2 (μ : Measure E),
        ∃ hfA :
            (Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport μ hf hfc).toLp f ∈
              (adjointComp (hμ.closedWeightedOperator m (ContinuousLinearMap.id ℝ E) hi)).domain,
          adjointComp (hμ.closedWeightedOperator m (ContinuousLinearMap.id ℝ E) hi)
              ⟨(Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport μ hf hfc).toLp f,
                hfA⟩ =
            hLf.toLp
              (fun x => -(Laplacian.laplacian f x -
                inner ℝ (gradient U x) (gradient f x))) := by
  intro E _ _ _ _ _ _ _ μ m _ U hμ hi hμU hU f hf hfc
  have hU1 : ContDiff ℝ 1 U := hU.of_le (WithTop.coe_le_coe.mpr le_top)
  exact ⟨KLS.LogConcave.memLp_neg_weightedLaplacian hU1 hf hfc,
    hμ.toLp_mem_adjointComp_domain m hi hμU hU1 hf hfc,
    hμ.adjointComp_toLp_eq m hi hμU hU1 hf hfc⟩

/-! ### Boundary and consistency uses -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)

include hνU hU in
/-- `route_G0` against the constant test `g = 1`: the weighted Laplacian has zero mean. -/
theorem boundary_constant_test {f : V → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, (Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫) ∂(ν : Measure V) = 0 :=
  KLS.LogConcave.integral_weightedLaplacian_eq_zero m hνU hU hf hfc

include hνU hU in
/-- `route_G0` with `g = f`: the Dirichlet form of `-ℒ` on a test is `∫ ‖∇f‖² dν`, the integrand
of the closed energy `‖T̄ f‖²` of `inner_adjointComp_self_eq`. -/
theorem boundary_dirichlet_form {f : V → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, -(Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫) * f x ∂(ν : Measure V) =
      ∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V) := by
  show ∫ x, -weightedLaplacian U f x * f x ∂(ν : Measure V) = _
  rw [← KLS.LogConcave.integral_inner_gradient_eq m hνU hU hf hfc (hf.of_le (by norm_num))]
  congr 1
  funext x
  exact real_inner_self_eq_norm_sq _

include hνU hU in
/-- `ℒ` is symmetric on `C²` compactly supported functions: `∫ (ℒf) g dν = ∫ f (ℒg) dν`. -/
theorem boundary_symmetric {f g : V → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∫ x, (Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫) * g x ∂(ν : Measure V) =
      ∫ x, f x * (Laplacian.laplacian g x - ⟪gradient U x, gradient g x⟫) ∂(ν : Measure V) := by
  have h1 := KLS.LogConcave.integral_inner_gradient_eq m hνU hU hf hfc (hg.of_le (by norm_num))
  have h2 := KLS.LogConcave.integral_inner_gradient_eq m hνU hU hg hgc (hf.of_le (by norm_num))
  have h3 : ∫ x, ⟪gradient f x, gradient g x⟫ ∂(ν : Measure V) =
      ∫ x, ⟪gradient g x, gradient f x⟫ ∂(ν : Measure V) := by
    congr 1
    funext x
    exact real_inner_comm _ _
  have h4 : ∫ x, (Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫) * g x ∂(ν : Measure V) =
      -∫ x, -weightedLaplacian U f x * g x ∂(ν : Measure V) := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [weightedLaplacian_apply]
    ring
  have h5 : ∫ x, f x * (Laplacian.laplacian g x - ⟪gradient U x, gradient g x⟫) ∂(ν : Measure V) =
      -∫ x, -weightedLaplacian U g x * f x ∂(ν : Measure V) := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [weightedLaplacian_apply]
    ring
  rw [h4, h5, ← h1, ← h2, h3]

end BakryEmeryGeneratorAudit

/-! ### Axiom reports -/

#print axioms FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_fderiv
#print axioms FunctionalInequalities.Analysis.BakryEmery.inner_gradient_eq_sum_fderiv_mul_fderiv
#print axioms FunctionalInequalities.Analysis.BakryEmery.continuous_laplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_laplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.continuous_gradient
#print axioms FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient
#print axioms FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_weightedLaplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.inner_gradient_tilted_weight
#print axioms FunctionalInequalities.Analysis.BakryEmery.memLp_weightedLaplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_mul_fderiv_mul_fderiv
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_mul_inner_gradient_eq_neg
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_inner_gradient_tilted
#print axioms FunctionalInequalities.Analysis.Semigroup.inner_eq_inner_closure_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.mem_adjoint_domain_closure_of_forall
#print axioms FunctionalInequalities.Analysis.Semigroup.adjoint_closure_apply_eq_of_forall
#print axioms FunctionalInequalities.KLS.LogConcave.integral_inner_gradient_eq
#print axioms FunctionalInequalities.KLS.LogConcave.integral_weightedLaplacian_eq_zero
#print axioms FunctionalInequalities.KLS.LogConcave.memLp_gradient_of_contDiff_hasCompactSupport
#print axioms FunctionalInequalities.KLS.LogConcave.memLp_neg_weightedLaplacian
#print axioms FunctionalInequalities.KLS.LogConcave.toLp_mem_closedWeightedOperator_domain
#print axioms FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_toLp_eq
#print axioms FunctionalInequalities.KLS.LogConcave.inner_toLp_neg_weightedLaplacian_eq
#print axioms FunctionalInequalities.KLS.LogConcave.toLp_mem_adjointComp_domain
#print axioms FunctionalInequalities.KLS.LogConcave.adjointComp_toLp_eq
#print axioms BakryEmeryGeneratorAudit.route_G0
#print axioms BakryEmeryGeneratorAudit.route_G1
#print axioms BakryEmeryGeneratorAudit.boundary_constant_test
#print axioms BakryEmeryGeneratorAudit.boundary_dirichlet_form
#print axioms BakryEmeryGeneratorAudit.boundary_symmetric

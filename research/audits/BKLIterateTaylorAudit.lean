import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.PoissonIterate.Taylor

/-!
# Audit: Corollary 3.7 and Lemma 3.9 (route form) for the BKL iterates (route `S2`, `J2`)

The propositions `S2` and `J2` of `research/audits/BKLIterateRouteStatements.lean` (operator route
to Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 3.1; decision record
`research/decisions/2026-10-07-bkl-operator-route.md`), restated verbatim with the same `variable`
block and notation, and discharged by the library theorems of
`KLS/LogConcave/HeatSemigroup/PoissonIterate/Taylor.lean`:

* `s2`: Corollary 3.7 (52), `S_{d+1} T_d(∇₀h_{k+2}) = α_{k+2} T_{d+1}(∇₀h_{k+1})` for `d ≥ 1`
  (`symmetrize_taylorField_grad0_iter_succ`);
* `j2`: Lemma 3.9 in the route form,
  `Σ_{k<N} p_{k+1} ≤ ‖L h₁‖² + (β/C) Σ_{k<N-1} |T₁(∇₀h_{k+1})|²` (`sum_meanGradSq_iter_le`).

`s2` holds for every `f ∈ L²(ν)`; `j2` uses `f ∈ D(A)` but neither the centering of `f` nor
`∫ x dν = 0` nor `0 < C`. These are supporting results of the operator route: Lemma 3.8 and
Theorem 3.1 are not proved here.
-/

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.KLS.LogConcave.PoissonIterate
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

namespace BKLIterateTaylorAudit

section HeatModel

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

/-- `S2`, verbatim: Corollary 3.7 (52) along the iterates. -/
theorem s2 :
    ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ (k d : ℕ), 1 ≤ d → ∀ (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)),
      symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
          (taylorField d (grad0 T̄ (iter T̄ f (k + 1)))) (J ∘ Fin.cast (by omega)) =
        scale T̄ (iter T̄ f k) * taylorField (d + 1) (grad0 T̄ (iter T̄ f k)) J) := by
  intro hνU hU hexp C hC f _ _ k d hd J
  exact KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_iter_succ m hν hi hνU
    (hU.1.of_le (WithTop.coe_le_coe.mpr le_top)) hexp hC f k hd J

/-- `J2`, verbatim: Lemma 3.9 in the route form. -/
theorem j2 :
    ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    (∫ x, x ∂(ν : Measure V)) = 0 →
    (∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ {β : ℝ} (N : ℕ), (∀ j, j + 1 < N → scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) →
      ∑ k ∈ Finset.range N, meanGradSq T̄ (iter T̄ f k) ≤
        normSq (genField T̄ (iter T̄ f 0)) +
          β / C * ∑ k ∈ Finset.range (N - 1), ‖taylorField 1 (grad0 T̄ (iter T̄ f k))‖ ^ 2) := by
  intro hνU hU hexp _ hcov C _ hC f hf _ β N hβ
  exact KLS.LogConcave.PoissonIterate.sum_meanGradSq_iter_le m hν hi hνU
    (hU.1.of_le (WithTop.coe_le_coe.mpr le_top)) hexp hC hcov hf N hβ

end HeatModel

end BKLIterateTaylorAudit

#print axioms BKLIterateTaylorAudit.s2
#print axioms BKLIterateTaylorAudit.j2
#print axioms KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_iter_succ
#print axioms KLS.LogConcave.PoissonIterate.sum_meanGradSq_iter_le

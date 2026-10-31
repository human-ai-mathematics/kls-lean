module

public import FunctionalInequalities.KLS.BKL.PoissonIterate.Domain

/-!
# Audit: the BKL iterates in `D(A)`, (30), (33), (46), (35)–(36) and (32)

The propositions `I1`, `I2`, `I3` and `I7` of `research/audits/BKL/IterateRouteStatements.lean`
(operator route to Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 3.1), restated verbatim with
the same `variable`
block and notation, and discharged by the library theorems of
`KLS/BKL/PoissonIterate/Domain.lean`:

* `i1`: every component of `iter T̄ f k` (the source's `h_{k+1}`) lies in `D(A)` and is centered
  (`iter_mem_domain_and_mean_eq_zero`);
* `i2`: the Poisson relation (30), `-L h_{k+2} = α_{k+2} ∇₀ h_{k+1}` (`genField_iter_succ`);
* `i3`: (33) `energy_iter_succ`, (46) `normSq_genField_iter_succ`, (35)
  `energy_sub_energy_iter_succ` and (32) `inv_le_scale_sq`;
* `i7`: the identity (36), `energy_iter_zero_eq`.

The hypotheses on `f` are used only for `i1`; `i2`, `i3` and `i7` hold for every `f ∈ L²(ν)`.
These are supporting results of the operator route: Lemmas 3.2–3.4, Corollary 3.5 and
Theorem 3.1 are not proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.KLS.LogConcave.PoissonIterate
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

namespace BKLIterateDomainAudit

section HeatModel

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

/-- `I1` of `IterateRouteStatements.lean`, verbatim: every component of every iterate lies in
`D(A)` and is centered. -/
theorem i1 :
    ((ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k I, iter T̄ f k I ∈ (adjointComp T̄).domain ∧ L2.mean ν (iter T̄ f k I) = 0) := by
  intro hνU hU C hC f hf hfm k I
  exact KLS.LogConcave.PoissonIterate.iter_mem_domain_and_mean_eq_zero m hν hi hνU hU hC hf hfm k I

/-- `I2` of `IterateRouteStatements.lean`, verbatim: the Poisson relation (30). -/
theorem i2 :
    ((ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, genField T̄ (iter T̄ f (k + 1)) = scale T̄ (iter T̄ f k) • grad0 T̄ (iter T̄ f k)) := by
  intro hνU hU C hC f _ _ k
  exact KLS.LogConcave.PoissonIterate.genField_iter_succ m hν hi hνU hU hC f k

/-- `I3` of `IterateRouteStatements.lean`, verbatim: the normalization (33), (46), the energy
drop (35) and (32). -/
theorem i3 :
    ((ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, energy T̄ (iter T̄ f (k + 1)) = normSq (grad0 T̄ (iter T̄ f k)) ∧
      normSq (genField T̄ (iter T̄ f (k + 1))) =
        scale T̄ (iter T̄ f k) ^ 2 * energy T̄ (iter T̄ f (k + 1)) ∧
      energy T̄ (iter T̄ f k) - energy T̄ (iter T̄ f (k + 1)) = meanGradSq T̄ (iter T̄ f k) ∧
      (0 < scale T̄ (iter T̄ f k) → (C : ℝ)⁻¹ ≤ scale T̄ (iter T̄ f k) ^ 2)) := by
  intro hνU hU C hCpos hC f _ _ k
  exact ⟨KLS.LogConcave.PoissonIterate.energy_iter_succ m hν hi hνU hU hC f k,
    KLS.LogConcave.PoissonIterate.normSq_genField_iter_succ m hν hi hνU hU hC f k,
    KLS.LogConcave.PoissonIterate.energy_sub_energy_iter_succ m hν hi hνU hU hC f k,
    KLS.LogConcave.PoissonIterate.inv_le_scale_sq m hν hi hνU hU hC hCpos f k⟩

/-- `I7` of `IterateRouteStatements.lean`, verbatim: the telescoped identity (36). -/
theorem i7 :
    ((ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ N, energy T̄ (iter T̄ f 0) =
      energy T̄ (iter T̄ f N) + ∑ k ∈ Finset.range N, meanGradSq T̄ (iter T̄ f k)) := by
  intro hνU hU C _ hC f _ _ N
  exact KLS.LogConcave.PoissonIterate.energy_iter_zero_eq m hν hi hνU hU hC f N

end HeatModel

end BKLIterateDomainAudit

#print axioms BKLIterateDomainAudit.i1
#print axioms BKLIterateDomainAudit.i2
#print axioms BKLIterateDomainAudit.i3
#print axioms BKLIterateDomainAudit.i7
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter_mem_domain_and_mean_eq_zero
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField_iter_succ
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_iter_succ
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_genField_iter_succ
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_sub_energy_iter_succ
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_le_scale_sq
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_iter_zero_eq

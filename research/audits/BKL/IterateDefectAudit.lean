module

public import FunctionalInequalities.KLS.BKL.PoissonIterate.Defect

/-!
# Audit: (47), Lemma 3.4, Corollary 3.5 and Lemma 3.2 for the BKL iterates

The propositions `I4`, `I5`, `I6` and `I8` of `research/audits/BKL/IterateRouteStatements.lean`
(operator route to Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 3.1), restated verbatim with
the same `variable`
block and notation, and discharged by the library theorems of
`KLS/BKL/PoissonIterate/Defect.lean`:

* `i4`: the Pythagorean identity (47), `‖∇²h_{k+1}‖² = ‖L h_{k+2}‖² + χ_{k+1}`
  (`normSq_gradField_gradField_iter`);
* `i5`: Lemma 3.4, `‖L h_{k+2}‖² + χ_{k+1} + a ‖∇h_{k+1}‖² ≤ ‖L h_{k+1}‖²`
  (`normSq_genField_iter_succ_add_defect_le`);
* `i6`: Corollary 3.5, `‖∇h_{k+1}‖² → 0` for `a > 0` (`tendsto_energy_iter_zero`), and the summed
  defects `Σ_{k<N} χ_{k+1} ≤ ‖L f‖²` (`sum_defect_iter_le`);
* `i8`: Lemma 3.2 with `λ = 1/C` (`exists_symm_normSq_grad0_iter_succ_sub_le`).

The centering of `f` and the bound `0 < C` are not used for `i4`–`i6`. These are supporting
results of the operator route: Lemma 3.3 and Theorem 3.1 are not proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.KLS.LogConcave.PoissonIterate
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

namespace BKLIterateDefectAudit

section HeatModel

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

/-- `I4` of `IterateRouteStatements.lean`, verbatim: the Pythagorean identity (47). -/
theorem i4 :
    ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, normSq (gradField T̄ (gradField T̄ (iter T̄ f k))) =
      normSq (genField T̄ (iter T̄ f (k + 1))) + defect T̄ (iter T̄ f k)) := by
  intro hνU hUt hexp C _ hC f hf _ k
  exact normSq_gradField_gradField_iter m hν hi hνU hUt hexp hC hf k

/-- `I5` of `IterateRouteStatements.lean`, verbatim: BKL Lemma 3.4. -/
theorem i5 :
    ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {a : ℝ}, (∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, normSq (genField T̄ (iter T̄ f (k + 1))) + defect T̄ (iter T̄ f k) +
        a * energy T̄ (iter T̄ f k) ≤ normSq (genField T̄ (iter T̄ f k))) := by
  intro hνU hUt hexp a ha C _ hC f hf _ k
  exact normSq_genField_iter_succ_add_defect_le m hν hi hνU hUt hexp hC ha hf k

/-- `I6` of `IterateRouteStatements.lean`, verbatim: BKL Corollary 3.5 and the summed defects. -/
theorem i6 :
    ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {a : ℝ}, 0 < a → (∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    Tendsto (fun k => energy T̄ (iter T̄ f k)) atTop (𝓝 0) ∧
      ∀ N, ∑ k ∈ Finset.range N, defect T̄ (iter T̄ f k) ≤ normSq (genField T̄ (iter T̄ f 0))) := by
  intro hνU hUt hexp a ha₀ ha C _ hC f hf _
  exact ⟨tendsto_energy_iter_zero m hν hi hνU hUt hexp hC ha₀ ha hf,
    fun N => sum_defect_iter_le m hν hi hνU hUt hexp hC ha₀.le ha hf N⟩

/-- `I8` of `IterateRouteStatements.lean`, verbatim: BKL Lemma 3.2 with `λ = 1/C`. -/
theorem i8 :
    ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, ∃ S : Field ν (k + 2), (∀ J, S (J ∘ Equiv.swap 0 1) = S J) ∧
      normSq (grad0 T̄ (iter T̄ f (k + 1)) - S) ≤ (C : ℝ) * defect T̄ (iter T̄ f k)) := by
  intro hνU hUt hexp C hCpos hC f hf _ k
  exact exists_symm_normSq_grad0_iter_succ_sub_le m hν hi hνU hUt hexp hC hCpos hf k

end HeatModel

end BKLIterateDefectAudit

#print axioms BKLIterateDefectAudit.i4
#print axioms BKLIterateDefectAudit.i5
#print axioms BKLIterateDefectAudit.i6
#print axioms BKLIterateDefectAudit.i8
#print axioms KLS.LogConcave.PoissonIterate.normSq_gradField_gradField_iter
#print axioms KLS.LogConcave.PoissonIterate.normSq_genField_iter_succ_add_defect_le
#print axioms KLS.LogConcave.PoissonIterate.tendsto_energy_iter_zero
#print axioms KLS.LogConcave.PoissonIterate.sum_defect_iter_le
#print axioms KLS.LogConcave.PoissonIterate.exists_symm_normSq_grad0_iter_succ_sub_le
#print axioms KLS.LogConcave.PoissonIterate.normSq_gradField_gradField_step
#print axioms KLS.LogConcave.PoissonIterate.normSq_genField_step_add_defect_le
#print axioms KLS.LogConcave.PoissonIterate.exists_symm_normSq_grad0_step_sub_le

import FunctionalInequalities.KLS.BKL.PoissonIterate.Symmetry

/-!
# Audit: BKL Lemma 3.3 for the iterates (route `S1`)

The proposition `S1` of `research/audits/BKL/IterateRouteStatements.lean` (operator route to
Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 3.1; decision record
`research/decisions/2026-10-07-bkl-operator-route.md`), restated verbatim with the same `variable`
block and notation, and discharged by the library theorem `normSq_grad0_iter_sub_symField_le` of
`KLS/BKL/PoissonIterate/Symmetry.lean`:

* `s1`: Lemma 3.3 for every `q` with `2 ≤ q ≤ k + 1`, under `0 < α_j² ≤ β/C` on the steps
  `k + 1 - q ≤ j < k`: `‖∇₀h_{k+1} - S_q ∇₀h_{k+1}‖² ≤ 4 q⁴ max(1, β)^q C Σ χ_j`.

The centering of `f` and the positivity of the `α_j` are not used. This is a supporting result of
the operator route: Corollary 3.7, Lemmas 3.8–3.9 and Theorem 3.1 are not proved here.
-/

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.KLS.LogConcave.PoissonIterate
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

namespace BKLIterateSymmetryAudit

section HeatModel

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

/-- `S1`, verbatim: BKL Lemma 3.3 for every `q`. -/
theorem s1 :
    ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ {β : ℝ} (k q : ℕ), 2 ≤ q → q ≤ k + 1 →
      (∀ j, k + 1 - q ≤ j → j < k →
        0 < scale T̄ (iter T̄ f j) ∧ scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) →
      normSq (grad0 T̄ (iter T̄ f k) - symField q (grad0 T̄ (iter T̄ f k))) ≤
        4 * (q : ℝ) ^ 4 * max 1 β ^ q * C *
          ∑ j ∈ Finset.Ico (k + 1 - q) k, defect T̄ (iter T̄ f j)) := by
  intro hνU hUt hexp C hCpos hC f hf _ β k q hq hqk hα
  exact normSq_grad0_iter_sub_symField_le m hν hi hνU hUt hexp hC hCpos hf k q hq hqk hα

end HeatModel

end BKLIterateSymmetryAudit

#print axioms BKLIterateSymmetryAudit.s1

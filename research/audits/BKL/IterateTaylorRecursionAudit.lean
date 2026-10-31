module

public import FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion

/-!
# Audit: Lemma 3.8 for the BKL iterates

The proposition `J1` of `research/audits/BKL/IterateRouteStatements.lean` (operator route to
Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 3.1), restated verbatim with the same `variable`
block and notation, and discharged by the library theorem `norm_taylorField_grad0_iter_sq_le` of
`KLS/BKL/PoissonIterate/TaylorRecursion.lean`:

* `j1`: Lemma 3.8 with hypothesis (29) componentwise and `0 < α_j² ≤ β/C` for all earlier steps,
  `|T_d(∇₀h_{k+1})|² ≤ (c/C)^d |T_{2d}(∇₀h_{k+1-d})|² + c^d R^{2d} C Σ_{k+1-2d ≤ j < k} χ_{j+1}`
  with `c = 2^20 max(1, β)²`.

The proof uses neither `R ≥ 1` nor the centering of `f`. This is a supporting result of the
operator route: Theorem 3.1 is not proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.KLS.LogConcave.PoissonIterate
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

namespace BKLIterateTaylorRecursionAudit

section HeatModel

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

/-- `J1` of `IterateRouteStatements.lean`, verbatim: Lemma 3.8 with the explicit constant
`c = 2^20 max(1, β)²`. -/
theorem j1 :
    ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ {R : ℝ}, 1 ≤ R →
    (∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ {β : ℝ} (k d : ℕ), 1 ≤ d → 2 * d ≤ k + 1 →
      (∀ j < k, 0 < scale T̄ (iter T̄ f j) ∧ scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) →
      ‖taylorField d (grad0 T̄ (iter T̄ f k))‖ ^ 2 ≤
        (2 ^ 20 * max 1 β ^ 2 / C) ^ d *
            ‖taylorField (2 * d) (grad0 T̄ (iter T̄ f (k - d)))‖ ^ 2 +
          (2 ^ 20 * max 1 β ^ 2) ^ d * R ^ (2 * d) * C *
            ∑ j ∈ Finset.Ico (k + 1 - 2 * d) k, defect T̄ (iter T̄ f j)) := by
  intro hνU hUt hexp C hCpos hC R _ h29 f hf _ β k d hd hdk hα
  exact KLS.LogConcave.PoissonIterate.norm_taylorField_grad0_iter_sq_le m hν hi hνU hUt hexp hC
    hCpos h29 hf k d hd hdk hα

end HeatModel

end BKLIterateTaylorRecursionAudit

#print axioms BKLIterateTaylorRecursionAudit.j1
#print axioms KLS.LogConcave.PoissonIterate.norm_taylorField_grad0_iter_sq_le
#print axioms KLS.LogConcave.PoissonIterate.norm_symmetrize_taylorField_grad0_iter_sq_le

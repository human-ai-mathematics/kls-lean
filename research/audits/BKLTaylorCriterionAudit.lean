import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.PoissonIterate.Criterion

/-!
# Audit: BKL Theorem 3.1 for regular laws (route statement `M`)

Operator route to Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Theorem 3.1 (p. 10, proof p. 17);
decision record `research/decisions/2026-10-07-bkl-operator-route.md`; route statements
`research/audits/BKLIterateRouteStatements.lean`. Restated and discharged by the library theorems
of `KLS/LogConcave/HeatSemigroup/PoissonIterate/Criterion.lean`:

* `m`: the route statement `M`, **verbatim**: there is a universal `K` such that every centered
  regular law on `ℝⁿ` with `Cov ≤ Id` satisfying the Taylor bound (29) with `R ≥ 1` has
  `C_P ≤ K R²` (`KLS.RegularPotential.poincare_le_of_taylor`);
* `taylorCriterionConstant_eq`: the constant obtained, `K = 100 (9 · 2^20)²`;
* `taylor_criterion`: the heat-model form `C_P(ν) ≤ K R²` for `ν = m.tilted (-U)`
  (`taylorCriterion`);
* `scalar_final_argument`: the final argument for real sequences (`le_of_iterate_bounds`).

Lemma 3.8 (`J1`) enters through `norm_taylorField_grad0_iter_sq_le`, Lemma 3.9 (`J2`) through
`sum_meanGradSq_iter_le`, and Lemma 3.4 / Corollary 3.5 through `PoissonIterate/Defect.lean`. This
is Theorem 3.1 for regular laws; it is not the KLS bound (Theorem 1.1).
-/

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.KLS.LogConcave.PoissonIterate
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

namespace BKLTaylorCriterionAudit

/-- `M`, verbatim: BKL Theorem 3.1 for regular laws. -/
theorem m : ∃ K : ℝ, ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
    (hV : KLS.RegularPotential V a b),
    (∫ x, x ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n)))) = 0 →
    (∀ v : EuclideanSpace ℝ (Fin n),
      ∫ x, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n))) ≤ ‖v‖ ^ 2) →
    ∀ R : ℝ, 1 ≤ R →
    (∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      MemLp f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n))) → ∀ d : ℕ, 1 ≤ d →
      ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
          (taylorTensor (hV.law : Measure (EuclideanSpace ℝ (Fin n))) f d)‖ ≤
        R ^ d * (eLpNorm f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n)))).toReal) →
    Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (K * R ^ 2) :=
  let ⟨K, _, h⟩ := KLS.RegularPotential.poincare_le_of_taylor
  ⟨K, h⟩

/-- The universal constant: `K = 100 c²` with `c = 2^20 max(1, 3)² = 9 · 2^20`. -/
theorem taylorCriterionConstant_eq : taylorCriterionConstant = 100 * (9 * 2 ^ 20) ^ 2 := by
  norm_num [taylorCriterionConstant]

/-- The final argument of Theorem 3.1 for real sequences (p. 17, operator route). -/
theorem scalar_final_argument {C c R : ℝ} {v p χ L α : ℕ → ℝ} {t : ℕ → ℕ → ℝ}
    (hC : 0 < C) (hc : 1 ≤ c) (hR : 1 ≤ R)
    (hv : ∀ k, 0 ≤ v k) (hv0 : C⁻¹ ≤ v 0) (hvlim : Tendsto v atTop (𝓝 0))
    (h36 : ∀ N, v 0 = v N + ∑ k ∈ range N, p k)
    (hχ : ∀ k, 0 ≤ χ k) (hχsum : ∀ N, ∑ k ∈ range N, χ k ≤ L 0)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2) (hL : ∀ k, L (k + 1) ≤ L k)
    (h46 : ∀ k, L (k + 1) = α k ^ 2 * v (k + 1))
    (hα : ∀ k, 0 ≤ α k) (hα0 : ∀ k, α k = 0 → v (k + 1) = 0)
    (h32 : ∀ k, 0 < α k → C⁻¹ ≤ α k ^ 2)
    (ht : ∀ d k, 0 ≤ t d k)
    (htaylor : ∀ d k, 1 ≤ d → t d k ≤ R ^ (2 * d) * v (k + 1))
    (hJ1 : ∀ k d, 1 ≤ d → 2 * d ≤ k + 1 → (∀ j < k, 0 < α j ∧ α j ^ 2 ≤ 3 / C) →
      t d k ≤ (c / C) ^ d * t (2 * d) (k - d) +
        c ^ d * R ^ (2 * d) * C * ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j)
    (hJ2 : ∀ N, (∀ j, j + 1 < N → α j ^ 2 ≤ 3 / C) →
      ∑ k ∈ range N, p k ≤ L 0 + 3 / C * ∑ k ∈ range (N - 1), t 1 k) :
    C ≤ 100 * c ^ 2 * R ^ 2 :=
  le_of_iterate_bounds hC hc hR hv hv0 hvlim h36 hχ hχsum hL0 hL h46 hα hα0 h32 ht htaylor hJ1 hJ2

section HeatModel

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

include hν hi in
/-- Theorem 3.1 in the heat model `ν = m.tilted (-U)`. -/
theorem taylor_criterion
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    {a : ℝ} (ha : 0 < a) (hUa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {R : ℝ} (hR : 1 ≤ R)
    (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤
      ENNReal.ofReal (taylorCriterionConstant * R ^ 2) :=
  taylorCriterion m hν hi hνU hU hexp ha hUa hcov hR h29

end HeatModel

end BKLTaylorCriterionAudit

#print axioms BKLTaylorCriterionAudit.m
#print axioms BKLTaylorCriterionAudit.taylorCriterionConstant_eq
#print axioms BKLTaylorCriterionAudit.scalar_final_argument
#print axioms BKLTaylorCriterionAudit.taylor_criterion
#print axioms FunctionalInequalities.KLS.RegularPotential.poincare_le_of_taylor
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorCriterion
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.le_of_iterate_bounds
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_sq_le

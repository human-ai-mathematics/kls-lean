import FunctionalInequalities.Analysis.Semigroup.Generated.ApproximateEigenvector
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ApproximateEigenfunction

/-!
# Audit: approximate eigenvectors of `T†T` and approximate first eigenfunctions (BKL route, O1–O2)

The obligations `O1` and `O2` of `research/audits/BKL/OperatorRouteStatements.lean` (operator route
to Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 3.1) are restated **verbatim** and proved from
the library:

* `o1`: for a closed densely defined `T` between real Hilbert spaces with the gap
  `λ ‖y‖² ≤ ‖T y‖²` on `D(T) ∩ (ker T)ᗮ`, a unit `y` there with `‖T y‖² ≤ λ (1 + η)` lies within
  `√(η / 8)` of some `z ∈ D(T†T) ∩ (ker T)ᗮ` with `‖T†T z - λ z‖ ≤ λ √(η / 2)`
  (`Generated.exists_approx_eigenvector_of_gap`; the hypothesis `0 ≤ η` is not used);
* `o2`: in the heat model `ν = m.tilted (-U)`, `U ∈ C²`, with `C_P(ν) = C ∈ (0, ∞)`, every `η > 0`
  admits a centered `f ∈ D(A)`, `‖f‖ = 1`, `‖A f - C⁻¹ f‖ ≤ C⁻¹ η`
  (`exists_centered_approx_eigenfunction`).

Outside this client's scope: the existence of an exact first eigenfunction (19), the weak
Hessian and tilt identities `O3`–`O5`, the iterates and Theorem 3.1 itself.
-/

noncomputable section

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace

namespace BKLApproximateEigenfunctionAudit

/-- `O1`, verbatim. -/
theorem o1 : (∀ {H₀ H₁ : Type} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁), T.IsClosed → Dense (T.domain : Set H₀) →
    ∀ {lam η : ℝ}, 0 < lam → 0 ≤ η →
    (∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      lam * ‖(y : H₀)‖ ^ 2 ≤ ‖T y‖ ^ 2) →
    ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ = 1 → ‖T y‖ ^ 2 ≤ lam * (1 + η) →
    ∃ z : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(z : H₀), (k : H₀)⟫ = 0) ∧
      ‖(y : H₀) - (z : H₀)‖ ≤ Real.sqrt (η / 8) ∧
      ‖adjointComp T z - lam • (z : H₀)‖ ≤ lam * Real.sqrt (η / 2)) := by
  intro H₀ H₁ _ _ _ _ _ _ T hT hd lam η hlam _ hgap y hy hy1 hTy
  exact Generated.exists_approx_eigenvector_of_gap T hT hd hlam hgap y hy hy1 hTy

/-- `O2`, verbatim. -/
theorem o2 : (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν = (C : ENNReal) →
    ∀ {η : ℝ}, 0 < η →
    ∃ f : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      L2.mean ν (f : Lp ℝ 2 (ν : Measure V)) = 0 ∧ ‖(f : Lp ℝ 2 (ν : Measure V))‖ = 1 ∧
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) f -
          (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ ≤ (C : ℝ)⁻¹ * η) := by
  intro V _ _ _ _ _ _ _ ν m _ hν hi U hνU hU C hC hCP η hη
  exact KLS.LogConcave.exists_centered_approx_eigenfunction m hν hi hνU hU hC hCP hη

end BKLApproximateEigenfunctionAudit

#print axioms BKLApproximateEigenfunctionAudit.o1
#print axioms BKLApproximateEigenfunctionAudit.o2
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap
#print axioms FunctionalInequalities.KLS.LogConcave.exists_centered_approx_eigenfunction

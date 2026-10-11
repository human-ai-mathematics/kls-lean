import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local
import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments
import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.KLS.BKL.Suspension.Law

/-!
# BKL Theorem 4.1, the second-cumulant base case

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 18: for an isotropic log-concave law the second cumulant
is `R₂ = Id`, so the universal cumulant bound `CumulantBound 1 1` (the `(d+1) = 2` cumulant bound with
constant `1`) holds unconditionally in every dimension. This is the `m = 2` base of Theorem 4.1 only;
the all-order theorem and the Eldan induction remain open. Proof bodies: Codex route bundle
`Local-Second-Cumulant` (independently accepted); statements and placement: Claude.
-/

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For an isotropic log-concave law `κ₂(u, v) = ⟪u, v⟫` (Borell gives the exponential radius). -/
theorem LogConcave.cumulant_two_eq_inner_of_isotropic (μ : ProbabilityMeasure E) (hLC : KLS.LogConcave μ)
    (hiso : KLS.Isotropic μ) (u v : E) : cumulant (μ : Measure E) 2 ![u, v] = ⟪u, v⟫ := by
  obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff μ).1 hLC).exists_integrable_exp_norm
  rw [Analysis.BakryEmery.cumulant_two_eq_covariance_of_integrable_exp (μ : Measure E) hr hexp, hiso.covariance_identity,
    ContinuousLinearMap.id_apply]

/-- Parseval: `∑_j κ₂(u, b_j)² = ‖u‖²` in any orthonormal basis. -/
theorem LogConcave.sum_sq_cumulant_two_eq_norm_sq_of_isotropic (μ : ProbabilityMeasure E)
    (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ E) (u : E) :
    (∑ j, cumulant (μ : Measure E) 2 ![u, b j] ^ 2) = ‖u‖ ^ 2 := by
  simp_rw [LogConcave.cumulant_two_eq_inner_of_isotropic μ hLC hiso]
  calc
    (∑ j, ⟪u, b j⟫ ^ 2) = ∑ j, ⟪u, b j⟫ * ⟪b j, u⟫ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [real_inner_comm (b j) u, pow_two]
    _ = ⟪u, u⟫ := b.sum_inner_mul_inner u u
    _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u

/-- **BKL Theorem 4.1, base `m = 2`** (`R₂ = Id`, p. 18): `CumulantBound 1 1` holds unconditionally in every
dimension (including `0`), by reindexing the `Fin 1`-coordinate sum and Parseval. The all-order Theorem 4.1
remains open. -/
theorem LogConcave.Suspension.cumulantBound_one_one : CumulantBound 1 1 := by
  classical
  intro n μ hiso hLC u
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let e : (Fin 1 → Fin n) ≃ Fin n :=
    { toFun := fun J => J 0
      invFun := fun j _ => j
      left_inv := by
        intro J
        ext i
        fin_cases i
        rfl
      right_inv := fun _ => rfl }
  have hcoord (J : Fin 1 → Fin n) :
      cumulant (μ : Measure _) 2 (Fin.cons u fun k => b (J k)) =
        cumulant (μ : Measure _) 2 ![u, b (e J)] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  have hs := e.sum_comp (fun j => cumulant (μ : Measure _) 2 ![u, b j] ^ 2)
  change (∑ J : Fin 1 → Fin n, cumulant (μ : Measure _) 2 (Fin.cons u fun k => b (J k)) ^ 2)
    ≤ 1 * ‖u‖ ^ 2
  simp_rw [hcoord]
  rw [hs, LogConcave.sum_sq_cumulant_two_eq_norm_sq_of_isotropic μ hLC hiso b u, one_mul]

end FunctionalInequalities.KLS

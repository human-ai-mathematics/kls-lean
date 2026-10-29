import FunctionalInequalities.Analysis.IteratedDerivative.Bilinear
import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local
import FunctionalInequalities.Probability.Line.AffineProfile
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Audit: raw Leibniz allocations and permutation symmetry of iterated derivatives

Clients of `Analysis/IteratedDerivative/Symmetry.lean` and `Bilinear.lean`. Consumers: every raw
subset allocation of the cubic `y ↦ y² · y` at order 3 sums to the unnormalised derivative `6` (no
factorial); the unit-uniform law on `[0, 1]` is a genuine compact noncentred law with variance
`1/12` whose actual scalar cumulants inherit real `C^∞` permutation symmetry. No (74) drift,
parameter jet or stochastic statement is involved.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery

namespace IndependentIteratedLeibniz

/-- Every raw subset allocation is consumed: the unnormalized cubic derivative is six. -/
theorem actual_cubic_raw_allocations :
    (∑ q : Fin 3 → Bool,
      directional (selected (fun _ : Fin 3 => (1 : ℝ)) q) (fun x : ℝ => x ^ 2) 0 *
      directional (selected (fun _ : Fin 3 => (1 : ℝ)) (fun i => !(q i))) id 0) = 6 := by
  let B := ContinuousLinearMap.mul ℝ ℝ
  have hh := iteratedFDeriv_bilinear B (contDiff_id.pow 2) contDiff_id
    3 (fun _ => (1 : ℝ)) 0
  have he : (fun y : ℝ => B (y ^ 2) y) = (fun y : ℝ => y ^ 3) := by
    funext y
    dsimp [B]
    ring
  simp only [id_eq] at hh
  rw [he] at hh
  have hn : iteratedFDeriv ℝ 3 (fun y : ℝ => y ^ 3) 0 (fun _ => 1) = 6 := by
    change iteratedDeriv 3 (fun y : ℝ => y ^ 3) 0 = 6
    norm_num [iteratedDeriv_pow, Nat.descFactorial]
  rw [hn] at hh
  simpa only [B, ContinuousLinearMap.mul_apply'] using hh.symm

/-- A genuine nondegenerate compact source law, independent of the algebraic cubic client. -/
theorem uniform_source_compact :
    IsCompact FunctionalInequalities.Probability.Line.unitUniform.support := by
  apply isCompact_Icc.of_isClosed_subset Measure.isClosed_support
  intro x hx
  have hs := Measure.support_restrict_subset (μ := (volume : Measure ℝ))
    (s := Set.Icc (0 : ℝ) 1) hx
  simpa only [IsClosed.closure_eq isClosed_Icc] using hs.1

/-- Actual scalar cumulants of the unit-uniform law inherit genuine real C-infinity symmetry. -/
theorem uniform_cumulants_symmetric (m : ℕ) (h : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    cumulant FunctionalInequalities.Probability.Line.unitUniform m (h ∘ σ) =
      cumulant FunctionalInequalities.Probability.Line.unitUniform m h := by
  apply iteratedFDeriv_perm
  exact contDiff_logLaplace _
    (compact_support_integrable_exp _ uniform_source_compact)

/-- The source law is not a degenerate zero-covariance test. -/
theorem uniform_variance_nonzero :
    ProbabilityTheory.variance (id : ℝ → ℝ)
      FunctionalInequalities.Probability.Line.unitUniform = 1 / 12 := by
  exact FunctionalInequalities.Probability.Line.variance_id_unitUniform

#print axioms actual_cubic_raw_allocations
#print axioms uniform_source_compact
#print axioms uniform_cumulants_symmetric
#print axioms uniform_variance_nonzero
#print axioms FunctionalInequalities.Analysis.iteratedFDeriv_perm
#print axioms FunctionalInequalities.Analysis.iteratedFDeriv_bilinear
#print axioms FunctionalInequalities.Analysis.directional_ofFn

end IndependentIteratedLeibniz

import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.PoissonIterate.Permutation

/-!
# Audit: the permutation bound (44) of BKL Lemma 3.3

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 3.3, p. 12–13, (44): for `q ≤ k` and a tensor
field `u` with `k` indices, `‖u - S_q u‖² ≤ q⁴ Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²`, where `S_q` averages over
the permutations of the first `q` index positions and `τ_ℓ` swaps positions `ℓ` and `ℓ + 1`.
The library theorem is `normSq_sub_symField_le` of
`KLS/LogConcave/HeatSemigroup/PoissonIterate/Permutation.lean`; this client restates it and
specializes it to `k = q = 2`, where the only adjacent transposition is `swap 0 1`.

This is a supporting combinatorial lemma; it does not prove Lemma 3.3 or Theorem 3.1.
-/

noncomputable section

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.KLS.LogConcave.PoissonIterate

namespace BKLPermutationAudit

/-- BKL (44): `‖u - S_q u‖² ≤ q⁴ Σ_{ℓ+1<q} ‖u - τ_ℓ u‖²` for every `q ≤ k`. -/
theorem permutation_bound :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
      {ν : ProbabilityMeasure V} (k q : ℕ), q ≤ k → ∀ u : Field ν k,
      normSq (u - symField q u) ≤
        (q : ℝ) ^ 4 * ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin k => ℓ.val + 1 < q),
          normSq (u - permField (Equiv.swap ℓ (finRotate k ℓ)) u) :=
  fun _ _ hq u => normSq_sub_symField_le hq u

/-- The case `k = q = 2`: `‖u - S₂ u‖² ≤ 16 ‖u - u(· ∘ swap 0 1)‖²`. -/
theorem permutation_bound_two {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] {ν : ProbabilityMeasure V} (u : Field ν 2) :
    normSq (u - symField 2 u) ≤ 16 * normSq (u - permField (Equiv.swap 0 1) u) := by
  have h := permutation_bound 2 2 le_rfl u
  have hfilter : Finset.univ.filter (fun ℓ : Fin 2 => ℓ.val + 1 < 2) = {0} := by decide
  have hrot : finRotate 2 0 = 1 := by decide
  rw [hfilter, Finset.sum_singleton, hrot] at h
  norm_num at h
  exact h

end BKLPermutationAudit

#print axioms BKLPermutationAudit.permutation_bound
#print axioms BKLPermutationAudit.permutation_bound_two
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_symField_le
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_permField_le
#print axioms
  FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_sub_permField_le_of_adjacent
#print axioms FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_permField

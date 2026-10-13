import FunctionalInequalities.KLS.BKL.Localization.CutoffInductionStep
import FunctionalInequalities.KLS.BKL.Localization.EnergyGenerator
import FunctionalInequalities.KLS.BKL.CompactReduction
import FunctionalInequalities.KLS.BKL.Reduction

/-!
# BKL Theorem 4.1 and Theorem 1.1, conditional on the compact Letwin bound

Assembly of the cutoff-only localization route (BKL arXiv:2610.05474v1, Sections 4–6): Lemma 5.1 discharges
`Lemma51Bound`, the strong induction gives Theorem 4.1 for compactly supported laws with `K = 153`, truncation extends
it to all isotropic log-concave laws, and `conjecture_of_cumulantBound` gives the dimension-free KLS bound.
The only remaining hypothesis is `LetwinCompactBound` (Letwin arXiv:2607.24164v1, Theorem 1.2, for compactly supported
laws). `KLS.kls` (KLS/Target.lean) is not touched (task S-7e).
-/

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.KLS.BKL.Localization

/-- **Lemma 5.1 discharges its named hypothesis**: `Lemma51Bound` holds, by `generator_cumulantEnergy_ge`. -/
theorem lemma51Bound : Lemma51Bound := by
  unfold Lemma51Bound
  intro n μ hc hiso hLC h8 r hr u q hSym hQ
  exact generator_cumulantEnergy_ge μ hc hiso hLC h8 hr u q hSym hQ

/-- **BKL Theorem 4.1 for compactly supported laws**, conditional only on the compact Letwin bound (Lemma 4.2):
`∃ K ≥ 1, ∀ d ≥ 2, R^ν_{d+1} ≤ (d!)² K^d · Id` for all compactly supported isotropic log-concave `ν`. -/
theorem theorem41Compact (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d : ℕ, 2 ≤ d →
      LogConcave.Suspension.CumulantBoundCompact d ((d.factorial : ℝ) ^ 2 * K ^ d) := by
  refine theorem41Compact_of_letwinCompact hL ?_ ?_
  · intro m hm ih ihb
    exact cutoffEnergyClaim_succ hL lemma51Bound (le_refl 153) hm ih ihb
  · intro d h
    exact cumulantBoundCompact_of_cutoffEnergyClaim (by norm_num : (0 : ℝ) ≤ 153) h

/-- **BKL Theorem 4.1** (all isotropic log-concave laws), conditional only on the compact Letwin bound:
the compact bound extends by the truncation argument of p. 19. -/
theorem theorem41 (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d : ℕ, 2 ≤ d →
      LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d) := by
  obtain ⟨K, hK, hcompact⟩ := theorem41Compact hL
  refine ⟨K, hK, ?_⟩
  intro d hd
  exact LogConcave.Suspension.cumulantBound_of_compact
    (by omega : 1 ≤ d) (hcompact d hd)

/-- **BKL Theorem 1.1 conditional on the compact Letwin bound**: the dimension-free KLS bound `KLS.Conjecture`
follows from Theorem 4.1 through the certified reduction `conjecture_of_cumulantBound`. `KLS.kls` is not touched. -/
theorem conjecture_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) : KLS.Conjecture := by
  exact FunctionalInequalities.KLS.conjecture_of_cumulantBound (hSource := theorem41 hL)

end FunctionalInequalities.KLS.BKL.Localization

import FunctionalInequalities.KLS.Letwin.CompactBound
import FunctionalInequalities.KLS.BKL.CompactReduction
import FunctionalInequalities.Probability.LogConcave
import FunctionalInequalities.KLS.Isotropic

/-!
# Audit: the compact Letwin constant-eight endpoint

Proof clients of `KLS.LogConcave.Suspension.letwinCompactBound`: the source-form compact bound for a given law and operator, and the BKL
compact base consumer `CumulantBoundCompact 2 8`. Audit only; it asserts nothing about Theorem 4.1 or KLS.
-/

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
open FunctionalInequalities FunctionalInequalities.KLS.LogConcave.Suspension

namespace LetwinCompactBoundAudit

theorem actual_compact_letwin_eight_client {n : ℕ} (hn : 0 < n)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : _root_.FunctionalInequalities.KLS.LogConcave μ) (hiso : KLS.Isotropic μ)
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A) :
    (∫ x, (⟪A x,x⟫ - ∫ y, ⟪A y,y⟫ ∂(μ : Measure _))^2 ∂(μ : Measure _)) ≤
      8 * ∑ i, ∑ j, ⟪A (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) i),
        stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) j⟫^2 :=
  letwinCompactBound n hn μ hLC hiso hc A hA

theorem actual_compact_letwin_bkl_base_client : CumulantBoundCompact 2 8 :=
  cumulantBoundCompact_two_of_letwinCompact letwinCompactBound

end LetwinCompactBoundAudit

end

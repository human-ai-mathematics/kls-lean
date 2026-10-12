import FunctionalInequalities.KLS.BKL.LocalThirdCumulant

/-!
# Reduction of BKL Theorem 4.1 to compactly supported laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19: Theorem 4.1 is proved first for compactly supported
isotropic log-concave laws (`CumulantBoundCompact`), whose localization coefficients are smooth and
bounded. `LetwinCompactBound` is Letwin's quadratic-form bound (arXiv:2607.24164v1, Theorem 1.2) for
compactly supported laws: the interface between the Letwin stream and the Theorem 4.1 stream. It gives
the base case `CumulantBoundCompact 2 8` (BKL Lemma 4.2). Both names are hypotheses; neither Letwin's
theorem nor Theorem 4.1 is proved here. Proof bodies: GPT (BKL Claude-controller goal, task S8a);
statements and placement: Claude.
-/

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/-- `CumulantBound d b` restricted to compactly supported laws: `R^ν_{d+1} ≤ b Id` for every compactly
supported isotropic log-concave probability measure in every dimension (BKL arXiv:2610.05474v1, p. 19:
Theorem 4.1 is proved for compactly supported laws first). This names the hypothesis. -/
def CumulantBoundCompact (d : ℕ) (b : ℝ) : Prop :=
  ∀ (m : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))),
    KLS.Isotropic ν → _root_.FunctionalInequalities.KLS.LogConcave ν →
      IsCompact (ν : Measure (EuclideanSpace ℝ (Fin m))).support →
      ∀ u : EuclideanSpace ℝ (Fin m),
      ∑ J : Fin d → Fin m, cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2

/-- Letwin's quadratic-form bound (arXiv:2607.24164v1, Theorem 1.2) for compactly supported isotropic
log-concave laws in positive dimension: the input of BKL Lemma 4.2 used by the localization argument.
This names the hypothesis; it is the interface between the Letwin and the Theorem 4.1 streams. -/
def LetwinCompactBound : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
    _root_.FunctionalInequalities.KLS.LogConcave μ → KLS.Isotropic μ →
      IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support →
      LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))

/-- **Base case of the compact induction** (BKL Lemma 4.2 for compactly supported laws): the compact
Letwin bound gives `CumulantBoundCompact 2 8`. -/
theorem cumulantBoundCompact_two_of_letwinCompact (h : LetwinCompactBound) :
    CumulantBoundCompact 2 8 := by
  classical
  intro n μ hiso hLC hcompact u
  cases n with
  | zero =>
    have hs : (∑ J : Fin 2 → Fin 0, cumulant (μ : Measure _) 3
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin 0) ℝ (J k)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro J _hJ
      exact Fin.elim0 (J 0)
    rw [hs]
    positivity
  | succ n =>
    let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
    have hbound := LogConcave.sum_sq_cumulant_three_le_of_letwin μ hLC hiso
      (h (n + 1) (Nat.succ_pos _) μ hLC hiso hcompact) b u
    have heq : (∑ J : Fin 2 → Fin (n + 1), cumulant (μ : Measure _) 3
        (Fin.cons u fun k => b (J k)) ^ 2) =
        ∑ j, ∑ k, cumulant (μ : Measure _) 3 ![u, b j, b k] ^ 2 := by
      have hreindex := (finTwoArrowEquiv (Fin (n + 1))).symm.sum_comp
        (fun J => cumulant (μ : Measure _) 3 (Fin.cons u fun k => b (J k)) ^ 2)
      calc
        _ = ∑ q : Fin (n + 1) × Fin (n + 1), cumulant (μ : Measure _) 3
            (Fin.cons u fun k => b (((finTwoArrowEquiv (Fin (n + 1))).symm q) k)) ^ 2 :=
          hreindex.symm
        _ = ∑ q : Fin (n + 1) × Fin (n + 1), cumulant (μ : Measure _) 3
            ![u, b q.1, b q.2] ^ 2 := by
          apply Finset.sum_congr rfl
          intro q _hq
          congr 2
          ext i
          fin_cases i <;> rfl
        _ = _ := Fintype.sum_prod_type _
    change (∑ J : Fin 2 → Fin (n + 1), cumulant (μ : Measure _) 3
      (Fin.cons u fun k => b (J k)) ^ 2) ≤ _
    rw [heq]
    exact hbound

/-- A bound for all laws restricts to compactly supported ones. -/
theorem CumulantBound.compact {d : ℕ} {b : ℝ} (h : CumulantBound d b) : CumulantBoundCompact d b := by
  exact fun m ν hiso hLC _ u => h m ν hiso hLC u

end FunctionalInequalities.KLS.LogConcave.Suspension

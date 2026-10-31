module

public import FunctionalInequalities.KLS.Letwin.IsoperimetricBound

/-!
# Lean paper-target certificate: `thm:letwin-log-quarter`

Letwin, *The KLS constant is O(log^(1/4) n)*, arXiv:2607.24164v1, Theorem 1.1,
PDF SHA-256 `5dd9194cf36d91e2e4929a48564fe99d8d163a0a5ec7b31d80dc1f58a41778f1`:
one universal `C > 0` satisfies `ψₙ ≤ C (log n)^(1/4)` for every `n ≥ 2`.
The supremum ranges over all isotropic log-concave probability laws on `ℝⁿ`, with the
literature inverse Cheeger normalization and no compactness or regularity premise.

The proof uses the stronger BKL dimension-free bound and the π Cheeger–Buser comparison.
This certifies the source conclusion through an alternative route. The original third-moment
argument and traced Klartag estimate remain unformalized. Proposition 2.8 is formalized only
for full-dimensional laws; this certificate does not claim all-statement or original-route coverage.
The separate compact Letwin certificate remains the input to the BKL proof.
-/

@[expose] public section

open MeasureTheory

namespace Solutions.ThmLetwinIsoperimetricBound

/-- Letwin Theorem 1.1, with one constant before every dimension and law. -/
theorem certificate :
    ∃ C : ℝ,
      0 < C ∧
        ∀ n : ℕ,
          2 ≤ n →
            (⨆ (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (_ :
                FunctionalInequalities.KLS.LogConcave μ) (_ :
                FunctionalInequalities.KLS.Isotropic μ),
                FunctionalInequalities.KLS.Isoperimetry.inverseScale μ) ≤
              ENNReal.ofReal (C * (Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) :=
  FunctionalInequalities.KLS.LogConcave.exists_logQuarter_isoperimetricBound

/--
info: 'Solutions.ThmLetwinIsoperimetricBound.certificate' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Solutions.ThmLetwinIsoperimetricBound.certificate

end Solutions.ThmLetwinIsoperimetricBound

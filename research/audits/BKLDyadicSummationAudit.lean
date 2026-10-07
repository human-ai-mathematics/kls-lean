import FunctionalInequalities.Analysis.DyadicSummation

/-!
# Audit: the dyadic summation in the proof of BKL Theorem 3.1

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Theorem 3.1, p. 17: the recursion (63),
multiplied by `(cλ)^(d-1)`, is summed along the dyadic degrees `d = 2^j`. The library theorem
`FunctionalInequalities.Analysis.le_of_dyadic_recursion`
(`formalization/FunctionalInequalities/Analysis/DyadicSummation.lean`) is restated here and
instantiated with the source's parameters `x = cλ`, `y = c²λR²`:

* `dyadic_recursion`: the library statement, restated;
* `dyadic_recursion_source_parameters`: the consumer shape, with `100 c²λR² ≤ 1`.

This is a supporting result of the BKL route; it does not prove (63) or Theorem 3.1.
-/

open FunctionalInequalities.Analysis

namespace BKLDyadicSummationAudit

/-- The dyadic summation, restated. -/
theorem dyadic_recursion {S : ℕ → ℝ} {x y A : ℝ} {N : ℕ}
    (hN : ∀ d, N ≤ d → S d = 0) (hA : 0 ≤ A) (hy : 0 ≤ y) (hy1 : 100 * y ≤ 1)
    (hrec : ∀ d, 1 ≤ d → x ^ (d - 1) * S d ≤ x ^ (2 * d - 1) * S (2 * d) + A * d * y ^ d) :
    S 1 ≤ A / 90 :=
  le_of_dyadic_recursion hN hA hy hy1 hrec

/-- The consumer shape: `x = cλ`, `y = c²λR²`. -/
theorem dyadic_recursion_source_parameters {S : ℕ → ℝ} {c lam R A : ℝ} {N : ℕ}
    (hN : ∀ d, N ≤ d → S d = 0) (hlam : 0 ≤ lam) (hA : 0 ≤ A)
    (hsmall : 100 * (c ^ 2 * lam * R ^ 2) ≤ 1)
    (hrec : ∀ d, 1 ≤ d → (c * lam) ^ (d - 1) * S d ≤
      (c * lam) ^ (2 * d - 1) * S (2 * d) + A * d * (c ^ 2 * lam * R ^ 2) ^ d) :
    S 1 ≤ A / 90 :=
  le_of_dyadic_recursion hN hA (by positivity) hsmall hrec

end BKLDyadicSummationAudit

#print axioms BKLDyadicSummationAudit.dyadic_recursion
#print axioms BKLDyadicSummationAudit.dyadic_recursion_source_parameters
#print axioms FunctionalInequalities.Analysis.le_of_dyadic_recursion

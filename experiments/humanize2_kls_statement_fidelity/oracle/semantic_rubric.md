# Semantic-review rubric

This file is for the reviewer, not the statement actor. Reference hashes are fixed in
`reference.sha256`.

The candidate passes only if all of the following hold:

1. It quantifies over every `D : ℕ`, without a `Nontrivial` or positive-dimension assumption.
2. Its ambient space is `EuclideanSpace ℝ (Fin D)`.
3. Its measure is a `Measure` with an `IsProbabilityMeasure` instance.
4. It retains the finite-second-moment hypothesis as `MemLp id 2 μ`.
5. Its value is a conjunction, not merely the covariance lower bound.
6. The first conjunct quantifies over every admissible real-valued test and asserts
   `poincareRayleighQuotient μ f ≤ optimalPoincareConstant μ`.
7. The second conjunct asserts
   `lambdaMaxCovariance μ ≤ optimalPoincareConstant μ`.
8. It uses the existing API rather than redefining admissibility, quotient conventions,
   covariance, or the optimal constant.
9. It adds no density, smooth-potential, log-concavity, finite-constant, positive-energy,
   positive-variance, or nonzero-vector restriction.
10. It is only a `Prop` definition. This phase contains no proof and claims no certification.

Compare against all of:

- `formalization/FunctionalInequalities/Project/LinearTestLower.lean`;
- `solutions/LemLinearTestLower.lean`;
- `research/reviews/2026-08-29-lean-linear-test-semantic-followup.md`; and
- `research/knowledge/lemmas.md`.

A compiling candidate that misses any item is `done: false`. Review notes should name the exact
semantic mismatch for the actor to repair without pasting a complete reference declaration.

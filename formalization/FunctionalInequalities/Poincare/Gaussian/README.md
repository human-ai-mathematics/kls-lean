# One-dimensional Gaussian Poincaré inequality

**Stage: proved, human-reviewed and Lean-certified.** All 20 library declarations are
proof-complete. The ledger node `lem:poincare-gaussian-one-dimensional` has `status: proved` and
`checked_by: lean`; its sole node certificate is
`Solutions.LemPoincareGaussianOneDimensional.certificate`.

The [statement freeze](../../../../research/decisions/2026-09-04-gaussian-poincare-freeze.md)
records the approved contract. The
[proof-closeout and acceptance record](../../../../research/explorations/2026-09-04-gaussian-poincare-acceptance.md)
records the final architecture and validation evidence.

Start with the two public conclusions in [Real.lean](Real.lean). The earlier
[candidate review package](../../../../research/decisions/2026-09-04-gaussian-poincare-candidate.md)
is an append-only snapshot of the statement-review stage, not a description of the current
proof status.

## What the theorem says

Let γ be the real Gaussian law with mean m and variance v. The proved result is

$$
\operatorname{Var}_\gamma(f)\le v\int_{\mathbb R}|f'(x)|^2\,d\gamma(x),
\qquad C_P(\gamma)=v.
$$

The first claim says that v works for every admissible test function. The second says that
no smaller constant works for all those tests. In Lean, for every `m : ℝ` and `v : NNReal`:

```lean
Poincare.SmoothTest.holds_gaussianReal m v :
  Poincare.SmoothTest.Holds (ProbabilityTheory.gaussianReal m v) (v : ℝ)

Poincare.SmoothTest.constant_gaussianReal m v :
  Poincare.SmoothTest.constant (ProbabilityTheory.gaussianReal m v) = (v : ENNReal)
```

Here `Poincare` abbreviates the namespace `FunctionalInequalities.Poincare`. The fixed constant
is real-valued; the optimal constant lives in `ENNReal`, following the existing library. The
parameter v is the **variance**, so variance 4 gives constant 4 rather than 2.

An admissible test is globally smooth, square-integrable under γ, and has integrable squared
canonical gradient. On ℝ that gradient equals f′. These are the existing conditions in
[Basic.lean](../SmoothTest/Basic.lean); no alternative test class is introduced.

| Parameters | Proved specialization |
| --- | --- |
| m = 0, v = 1 | The standard Gaussian has constant 1. |
| m = 3, v = 4 | Translation leaves the constant at the variance, 4. |
| Arbitrary m, v = 0 | The law is the point mass at m; all test variances and the optimal constant are zero. |

The [certificate entry point](../../../../solutions/LemPoincareGaussianOneDimensional.lean)
checks these applications at explicit types and packages both main conclusions in one named
certificate.

## Files and proof flow

```text
Gaussian/
├── README.md       # Mathematical meaning, sources, validation and file map
├── Density.lean    # 7 density derivative, tail and integrability interfaces
├── Hardy.lean      # 9 FTC/Cauchy, Tonelli and Gaussian energy interfaces
└── Real.lean       # 4 fixed-constant, lower-bound and optimal-equality interfaces
```

The 7 + 9 + 4 interfaces give the 20 proved declarations. The dependency chain is
`Density → Hardy → Real`. `Density.lean` builds directly on Mathlib's
Gaussian density API. `Hardy.lean` isolates the reusable real-line analytic argument. `Real.lean`
combines those estimates with the existing Poincaré and linear-test library. The solution entry
point imports `Real.lean` directly, while the root `FunctionalInequalities.lean` aggregate exports
the accepted result.

The mathematical proof proceeds as follows:

1. Variance is bounded by the squared distance to the fixed center `f m`.
2. Finite-interval FTC and Cauchy–Schwarz bound `(f x - f m)²` by a weighted integral of `f′²`.
3. Nonnegative Tonelli exchanges the two integrations on each half-line.
4. The Gaussian first-moment tail identities replace the weights by v times the density; the
   left and right estimates add without an extra factor.
5. The positive-variance density result gives `Holds`; the zero-variance case is handled
   separately through `gaussianReal m 0 = Measure.dirac m`.
6. The identity test has variance v and energy one, so every valid finite constant is at least v;
   combining this with the upper bound gives the sharp optimal equality.

Every real integral used in the density argument carries explicit integrability evidence. The
proof assumes neither global Lebesgue L² integrability of f′ nor test-function decay nor
attainment of the infimum defining `Poincare.SmoothTest.constant`.

As a final API cleanup, the two Gaussian first-moment tail identities quantify over every
endpoint `t`. Their old endpoint-order premises were unused; the right/left half-line callers
already obtain the needed order facts from their integration regions. This generalization does
not alter the ledger claim or any constant.

## Sources and precise scope

The manuscript's
[Gaussian covariance family](https://github.com/numina-functional-inequalities/kls-exploration/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L10-L37)
gives the Poincaré constant of a centered Gaussian with positive-definite covariance. Its
one-dimensional Poincaré component supplies the source claim. The numerical normalization is
from [Definition 2.1](https://github.com/numina-functional-inequalities/kls-exploration/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25).

Arbitrary means, zero variance and the exact smooth finite-energy domain are explicit local
specifications. The direct density route and its analytic helpers are local proof choices; the
manuscript obtains its upper bound through Bakry–Émery and LSI. Each Lean declaration identifies
whether it is a source specialization, a local extension/helper, or a Mathlib bridge. The
[source and API audit](../../../../research/explorations/2026-09-04-gaussian-poincare-design.md)
maps these categories to fixed source revisions and the declarations that use them.

Human semantic and mathematical review confirmed that v is the variance, that the factor and
inequality direction match the manuscript normalization, that the positive and zero-variance
cases are complete, and that no hidden boundary or integrability hypothesis is missing. The
theorem concerns only the existing globally smooth Gaussian-L² finite-energy test class. It does
not identify that class with a closed Sobolev/Dirichlet domain and does not assert a multivariate,
log-Sobolev or transport-entropy theorem.

## Validate the certificate

From the repository root:

```sh
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization
lake build
lake env lean ../solutions/LemPoincareGaussianOneDimensional.lean
```

The default `Solutions` target compiles this certificate together with the three earlier node
certificates and `solutions/GaussianAxiomAudit.lean`. That guarded audit fixes the certificate's
transitive axiom set to `propext`, `Classical.choice`, and `Quot.sound`, so any change fails the
default build. The Gaussian implementation and its local import closure contain no proof
placeholders or forbidden proof escapes. Lean compilation checks the terms; the ledger checker
checks certification structure and provenance; the completed human review supplies the separate
semantic check. The earlier
[validation record](../../../../research/explorations/2026-09-04-gaussian-poincare-validation.md)
is retained as evidence from the candidate-interface stage and must not be read as the current
proof status.

Lean and Mathlib remain pinned to v4.33.0.

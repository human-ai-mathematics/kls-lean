# Issue draft for review: sharp one-dimensional Gaussian Poincaré constant

This file is for user review only; no GitHub issue has been published and no ledger node, Lean skeleton, or proof has been added.
The user will decide whether to start the project, which implementation route to adopt, and how to proceed after reviewing it.

**Proposed title:** Lean: certify the one-dimensional Gaussian Poincaré inequality with the sharp constant

**Proposed parent:** [Issue #1](https://github.com/human-ai-mathematics/kls-lean/issues/1)

**Repository baseline:** `10e4c707491830ebe9d07f7bfc5e65efeddc7e2e` on `main`.

The proposed issue body follows the structure of
[Issue #2](https://github.com/human-ai-mathematics/kls-lean/issues/2).

---

## Objective

Formalize the classical one-dimensional Gaussian Poincaré inequality with its sharp constant:

$$
\operatorname{Var}_{\gamma_{m,v}}(f)
\le v\int_{\mathbb R}|f'(x)|^2\,d\gamma_{m,v}(x),
\qquad C_P(\gamma_{m,v})=v,
$$

where `γₘ,ᵥ = ProbabilityTheory.gaussianReal m v`, `m : ℝ`, and `v : NNReal` is the
**variance**, including `v = 0`.

The proposed ledger node is `lem:poincare-gaussian-one-dimensional`. This is the Gaussian
follow-up identified in Issue #2. The existing linear-test lower bound and binary/finite
tensorization nodes from #2, #6, and #7 remain accepted.

All constants refer to the repository's existing `Poincare.Admissible` class: globally smooth
real-valued L² functions with integrable squared canonical gradient. The inequality above uses
the identification of the real-line canonical gradient with the ordinary derivative.

## Proposed layout

```text
formalization/FunctionalInequalities/Poincare/
└── Gaussian/
    └── Real.lean

solutions/
└── LemPoincareGaussianOneDimensional.lean
```

The division should be:

- `Poincare/Gaussian/Real.lean`: reusable real-Gaussian Poincaré results and the required
  density/calculus helpers;
- `solutions/LemPoincareGaussianOneDimensional.lean`: one thin node-specific certificate
  combining the fixed-constant inequality and optimal-constant equality.

Reuse `Poincare.Basic` and `Poincare.LinearTest`. Keep the current subject-based layout and
direct solution-to-library imports. If a genuinely reusable real-line analytic helper warrants
its own module, record that decision during statement preparation. Precise helper names and
module boundaries remain subject to review.

## Scope

### 1. Audit the source, normalization, and existing Mathlib APIs

The manuscript's
[Gaussian covariance family](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L10-L37)
states `C_P(N(0, Σ)) = λ_max(Σ)` for positive-definite covariance. This issue targets its
one-dimensional Poincaré component. Arbitrary means and the zero-variance Dirac case are explicit
extensions in the proposed local statement. The same source's LSI and transport-entropy
equalities are separate results.

Preserve the normalization from
[Definition 2.1](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25)
and the existing `Admissible`, `energy`, `Holds`, and `constant` definitions. The smooth
finite-energy formulation does not claim an equivalence with a closed Sobolev, Dirichlet, or
spectral-gap domain.

Use the pinned Lean/Mathlib `v4.33.0` project. The initial API audit has identified:

- [`gaussianReal`, `gaussianReal_zero_var`, and its probability instance](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Gaussian/Real.lean#L222-L233);
- [`variance_id_gaussianReal` and `memLp_id_gaussianReal`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Gaussian/Real.lean#L575-L581);
- [`gradient_eq_deriv'`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Gradient/Basic.lean#L224).

The variance parameter contributes the constant `v`, with no additional square or factor of 2.
Gaussian moments and probability normalization should be supplied by these APIs, rather than
added as assumptions to the public results.

### 2. Prepare and review the exact statements

Proposed public declarations in namespace `FunctionalInequalities.Poincare`
(statement types only; names remain reviewable):

```lean
theorem holds_gaussianReal (m : ℝ) (v : NNReal) :
    Holds (ProbabilityTheory.gaussianReal m v) (v : ℝ)

theorem constant_gaussianReal (m : ℝ) (v : NNReal) :
    constant (ProbabilityTheory.gaussianReal m v) = (v : ENNReal)
```

The public statements cover every real mean and every nonnegative variance. A positive-variance
assumption may be used inside the density argument, but must not restrict the delivered results.
Do not add boundedness, compact support, a second-derivative integrability condition, or decay of
the test function at infinity to the public test class.

After approval of this work package, prepare compilable candidate statements, identify all
supporting obligations, print complete public signatures, and write the matching ledger claim.
Keep the candidate `drafted` / `checked_by: null` until human statement review. Record the exact
approved signatures and ledger statement before the separate proof stage. This issue proposal
itself does not freeze those statements or determine who carries out the proof.

### 3. Prove the sharp upper bound on the complete test class

The preferred route to assess is a direct one-dimensional density argument for arbitrary
`m` and `v > 0`. With `p` the Gaussian density, first establish

$$
\operatorname{Var}_{\gamma_{m,v}}(f)
\le \int (f(x)-f(m))^2\,d\gamma_{m,v}(x)
\le v\int |f'(x)|^2\,d\gamma_{m,v}(x).
$$

The first inequality is variance minimization over constant centers; it requires no identity
between `f(m)` and the expectation of `f`. For the second, use the fundamental theorem of
calculus and Cauchy–Schwarz on the intervals between `m` and `x`, then integrate separately over
the two half-lines. The Gaussian tail identities supply the sharp weight:

$$
\int_t^\infty (x-m)p(x)\,dx=vp(t)\quad(t\ge m),
\qquad
\int_{-\infty}^t (m-x)p(x)\,dx=vp(t)\quad(t\le m).
$$

Record the required density derivative, tail-integral, interval-integral, and interchange
lemmas during the API audit. Use nonnegative Tonelli where finiteness has not yet been proved;
retain explicit integrability whenever using real-valued integral identities. The existing
smoothness, L², and finite-gradient-energy assumptions must suffice for the final argument.
Any alternative proof initially restricted to controlled tests must include its extension to
the full `Admissible` class.

This is a candidate proof route, not a claim that its Lean implementation already exists.
A general affine transport framework is not required if the direct `m, v` argument succeeds.

For `v = 0`, use `gaussianReal m 0 = Measure.dirac m` and zero variance under a Dirac law.
The ambient space is still `ℝ`; the earlier theorem for a subsingleton ambient Hilbert space
does not supply this case. Positive-variance density identities must not be used here.

### 4. Prove sharpness and the optimal-constant equality

Use the identity function, equivalently `Poincare.linearTest (1 : ℝ)`, to obtain

$$
\operatorname{Var}_{\gamma_{m,v}}(\mathrm{id})=v,
\qquad
\operatorname{energy}_{\gamma_{m,v}}(\mathrm{id})=1.
$$

Establish admissibility using the existing Gaussian L² result and linear-test API. Deduce that
every finite valid Poincaré constant is at least `v`, then obtain the lower bound on
`Poincare.constant` using its existing `ENNReal` infimum definition. Combine this with the
fixed upper bound to prove equality. No infimum-attainment witness is an assumption.

Check the standard Gaussian, arbitrary mean and variance, and `v = 0` through typed applications
of the general results. A multivariate covariance theorem is not needed for this one-dimensional
sharpness argument.

### 5. Connect the result to certification and validate it

- Add the proposed ledger node only as part of the subsequently approved statement work;
  preserve all three existing proved nodes and their accepted contracts.
- After proof completion, add one named certificate covering both public conclusions and put
  its solution entry point in the default Lake target.
- Compare the delivered public signatures, definitions, and ledger statement with the approved
  snapshots; review the proof's transitive axioms and local imports.
- Set `proved` / `checked_by: lean` only after the complete mathematical claim is accepted.
- Add append-only source/design/API-gap and verification records, and update the current
  source map and design documentation when implementation takes place.
- Run the established checks:

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

Validate a clean checkout and CI for the eventual final published commit, after publication
has been authorized. The present review draft is local and uncommitted.

## Acceptance criteria

- [ ] Source correspondence and the variance/gradient normalization are documented precisely.
- [ ] Complete public signatures and the matching ledger statement receive human approval.
- [ ] The fixed-constant Gaussian inequality is proved for the complete existing `Admissible` class.
- [ ] The linear test proves sharpness, and the optimal constant equals `(v : ENNReal)`.
- [ ] Arbitrary means, all positive variances, and the zero-variance Dirac case are included.
- [ ] All calculus, tail-integral, and real-integral uses retain their required hypotheses.
- [ ] A single node-specific certificate covers both conclusions in the default Lake build.
- [ ] Semantic and transitive-axiom review passes, with no proof placeholders or unapproved axioms.
- [ ] The existing three proved nodes, semantic definitions, and frozen interfaces remain valid.
- [ ] The ledger checker and its regression tests pass; the default Lean build succeeds from a clean checkout.
- [ ] The design decisions and remaining Mathlib gaps are recorded without rewriting historical records.
- [ ] After authorized publication, CI succeeds for the exact final commit and the evidence is recorded.

## Follow-up issues

Once this one-dimensional result is accepted, separate follow-ups may address:

1. diagonal and multivariate Gaussian Poincaré constants, combining the finite-product result
   from #7 with the necessary coordinate and affine transport results;
2. reusable affine pushforward/scaling bounds;
3. log-Sobolev vocabulary and Gaussian LSI;
4. strong convexity/Bakry–Émery.

General one-dimensional log-concave estimates, Cheeger comparisons, full Sobolev/spectral-gap
equivalences, optimal transport, Otto–Villani, Γ₂ calculus, and the KLS stochastic/GMT backbone
remain outside this issue's scope.

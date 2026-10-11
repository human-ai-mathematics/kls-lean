# Formalization priorities for BKL Song and Zhang and Letwin

Reviewed 2026-10-07 against local source at
`ca59365726bca899f26cdd889dcc62850089eb09` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

Keep Bizeul–Klartag–Lehec (BKL) as the main formalization route, with its
Theorem 3.1 as the next complete source theorem to pursue. Select Letwin
Theorem 1.2 as a separate prerequisite target shared by both full KLS routes.
Defer a full Song–Zhang implementation: it requires additional spectral and
polynomial iteration machinery beyond the shared missing foundations.

This is a comparison of scope, dependencies and current library fit. It does
not certify the mathematical correctness of any complete paper, change a
proof or certificate status, or estimate a completion date. The
dimension-free KLS statement remains open in this repository.

## Pinned sources

The PDFs and `manifest.json` are in the adjacent local directory
`/Users/lyuyuwei/Documents/ChatGPT/KLS-paper-sources/2026-10-07/`.
All three PDF hashes were checked in this review. Letwin was downloaded from
the versioned arXiv PDF endpoint and added to that manifest.

| Paper | Version and source | PDF pages | Main result in the pinned text |
| --- | --- | --- | --- |
| Letwin | [2607.24164v1](https://arxiv.org/abs/2607.24164v1) | 21 | Theorem 1.1: the inverse Cheeger constant is `O((log n)^(1/4))`, `n >= 2`; Theorem 1.2: the sharp quadratic-form variance inequality |
| Bizeul–Klartag–Lehec | [2610.05474v1](https://arxiv.org/abs/2610.05474v1) | 32 | Theorem 1.1: a universal Poincare bound for isotropic log-concave laws in every positive dimension |
| Song–Zhang | [2610.01447v2](https://arxiv.org/abs/2610.01447v2) | 140 | Theorem 9.1: universal Poincare and inverse Cheeger bounds; finite-energy locally Lipschitz tests also belong to `L²` |

SHA-256 values:

- Letwin: `5dd9194cf36d91e2e4929a48564fe99d8d163a0a5ec7b31d80dc1f58a41778f1`.
- BKL: `86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
- Song–Zhang: `fad3f750a121cd99f09213ea237fc71b66e97ad1699ecca1d07f74c2fd69d771`.

Song–Zhang v2 claims a universal bound; the iterated-log main conclusion of
v1 must not be substituted for it. Page count alone does not measure Lean
effort, because quoted external theorems also need proofs in the dependency
closure.

## Comparison with the current library

| Target | Existing support | Substantial remaining work | Recommended role |
| --- | --- | --- | --- |
| BKL Theorem 3.1 and then Theorem 1.1 | Lemma 2.2 in the source form; Lemma 3.6 and Corollary 3.7 in reviewed stronger forms; regular laws; centered inverse on the operator domain; supplied-iterate energy identities | Smooth representatives with temperate derivatives for the inverse; first eigenfunction and compact resolvent; construction of the iterates; higher partial symmetrization and the final summation. The full main theorem additionally needs Letwin, Eldan localization, suspension and approximation | Best fit for continuing current proof work |
| Letwin Theorem 1.2 | Isotropy, log-concavity, finite-dimensional matrix tools, integration by parts and parts of Gaussian smoothing; an existing conditional consumer in BKL | Moment-measure existence and regularity, Monge–Ampere calculus, the Hessian metric and Brascamp–Lieb inequality, Stein kernels, the `H⁻¹` variance inequality and approximation | A focused shared prerequisite, with a substantial new analytic foundation |
| Song–Zhang Theorem 9.1 | Shared BGL, generator, Bochner, isotropy, tilt and tensor foundations | Shared Letwin and localization obligations; spectral `H^(±1/2)` and domains; Appell polynomial estimates; repeated height reduction and control of repetition costs | A later alternative route and reference for shared infrastructure |

The BKL assessments above follow the current
[handoff](../../HANDOFF.md),
[literature register](../progress/LITERATURE.md), and the declarations in
`Analysis/Tensor/`, `Analysis/BakryEmery/`,
`Analysis/Semigroup/Generated/Inverse.lean`, and
`KLS/LogConcave/{Regular.lean,HeatSemigroup/}` under
`formalization/FunctionalInequalities/`. Supplied iterates and conditional
inputs remain hypotheses; those declarations do not construct the source
iterates or prove the main theorem.

The earlier [two-paper comparison](../../build/reviews/2026-10-07-new-kls-papers/REPORT.md)
predates the BKL proof blocks and the family-directory migration. Its
coverage counts and old module paths are historical. Its identification of
external obligations is useful, but the current source and handoff determine
the present coverage.

## Letwin prerequisites and scope

Letwin Theorem 1.2 (PDF p. 3) states, for an isotropic log-concave law and
every symmetric matrix `M`,

`Var(<MX,X>) <= 2 E|grad <MX,X>|² = 8 ||M||²_HS`.

Its proof is deterministic. It does not itself require implementing Eldan's
localization process. However, its dependency closure includes quoted
moment-measure existence (Lemma 2.1), smoothness and a diffeomorphism with a
Monge–Ampere identity (Lemma 2.2), Fathi's Stein-kernel construction (Lemma
2.7), and Barthe–Klartag's `H⁻¹` variance inequality (Proposition 2.8).
The new Hessian estimate of Theorem 2.5 and Appendix A then connect these to
the quadratic-form result (PDF pp. 5–18). These are not currently supplied
by local Lean declarations.

The moment-map operator is
`L f = (Hess phi)^(-1) : Hess f - <grad V(grad phi), grad f>`.
Its diffusion coefficient depends on the point. The current
`BakryEmery.weightedLaplacian` is the Euclidean expression
`Delta f - <grad U, grad f>`; the two expressions cannot be identified by
renaming a potential. Similarly, the Brascamp–Lieb energy with inverse
Hessian is not the constant-curvature BGL estimate already certified here.
The regular class of Letwin is supported on a bounded convex set, whereas
`KLS.RegularPotential` describes a globally strongly convex smooth potential
on the whole space. These two uses of "regular" require different adapters.

The current
[`LetwinQuadraticBound`](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant.lean)
is a proposition naming the variance bound, not a theorem deriving it from
log-concavity. `sum_sq_cumulant_three_le_of_letwin` takes that proposition as
a premise and also assumes all exponential moments. Proving Letwin 1.2
would discharge the variance premise for isotropic log-concave laws; extending
the current cumulant consumer to every such law still needs its moment or
approximation bridge. Regular BKL laws already provide all exponential
moments.

Covering the whole Letwin paper also requires its title theorem, Theorem
1.1. The proof on PDF p. 3 invokes a bound obtained by tracing Klartag 2023,
`C_P <= C kappa_n sqrt(log n)`. This external conversion remains a separate
formalization obligation. A proof of Theorem 1.2 alone would not cover the
paper under this repository's coverage rule.

## The next complete source theorem

BKL Theorem 3.1 (PDF p. 10) is the most suitable next target given the
current interfaces. For a centered regular log-concave law with covariance
at most the identity and `R >= 1`, it assumes
`||T_d f||_HS <= R^d ||f||_L²` for every `d >= 1` and `f in L²`, and
concludes `C_P <= C R²` for a universal constant `C`.

BKL Section 3 supplies a proof of this criterion. That proof uses neither
Letwin Theorem 1.2 nor the stochastic cumulant bound. The source attribution
to Song–Zhang therefore does not require formalizing all 140 pages first.
The existing tensor and tilt results directly support this target.

The remaining sequence follows the current handoff:

1. Complete the regularity part of BKL Lemma 2.1 and the first-eigenfunction
   facts in Section 2. An inverse in `L²` is insufficient: the iteration
   needs smooth representatives whose derivatives have polynomial growth.
2. Construct the normalized iterates required by the existing energy lemmas.
3. Complete Lemma 3.3 for `q >= 3`, Lemma 3.8 and the summation in Lemma 3.9,
   then prove the criterion with its source hypotheses and constants.
4. Treat Letwin Theorem 1.2 as the shared prerequisite target for the full
   main theorem. Prove its external inputs or reuse verified proofs; keeping
   them as assumptions yields only conditional counterparts.

The stochastic block remains substantial for both full KLS routes. BKL
uses Eldan's original process with covariance-dependent diffusion
`A_t^(-1/2)` (PDF p. 19), as does Song–Zhang Lemma 4.2 (PDF pp. 19–20).
Brownian-motion definitions do not supply the stochastic integral, Itô
formula or SDE well-posedness needed here. Song–Zhang additionally requires
operator square roots (Lemma 3.4, PDF p. 18), polynomial coefficient
profiles and the iteration in Sections 8–9. It may inform individual
shared proofs without becoming the main route.

## Local validation

The downloaded PDF's author metadata, exact arXiv version, 21-page count
and content were checked before installation. Each of the three manifest
entries was checked against the file's byte count and SHA-256. Text from
all three PDFs was extracted locally; the Letwin main theorem and moment-map
pages and the Song–Zhang spectral lemma were also inspected as rendered
pages. The comparison does not constitute an independent line-by-line
correctness review of all three proofs.

No Lean source, certificate, canonical progress record, Git index, commit,
remote ref or CI run was changed. This documentation-only comparison needs
no Lean rebuild. The local extraction and page images are in
`build/reviews/2026-10-07-three-paper-comparison/`.

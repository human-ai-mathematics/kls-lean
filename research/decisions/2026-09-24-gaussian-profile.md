# Gaussian profile: scalar construction and differential identity

## Placement and scope

`Probability/Line/GaussianProfile.lean` owns the one-dimensional standard Gaussian
CDF, its inverse on `(0,1)`, and the density expressed in quantile coordinates.
It imports the existing probability CDF interface and Mathlib calculus, with no
Poincare, log-concavity or heat-semigroup dependency. No existing API is changed.

The source constructs an open partial homeomorphism from the strictly increasing CDF,
whose range is proved to be exactly `(0,1)`. The resulting profile is the actual
standard Gaussian density evaluated at the inverse CDF. It is extended by zero outside
`(0,1)`; the inverse itself has unspecified values outside this interval.

## Proved statements

- The CDF and its quantile are inverse on their stated domains.
- `profile (distribution x) = gaussianPDFReal 0 1 x`.
- `I'(p) = -quantile p` and `I''(p) = -1 / I(p)` for `0 < p < 1`.
  In particular `I(p) * I''(p) = -1`, without an assumed ODE.
- `0 <= I(p) <= 1 / sqrt(2*pi)`; the upper bound is attained at `distribution 0`.
- `I(0) = I(1) = 0`, both interior endpoint limits vanish, and `I` is continuous
  and strictly concave on `[0,1]`.

The profile agrees with the definition and equation (29) in
[De Ponti--Mondino, arXiv:1902.03835v2, Section 3](https://arxiv.org/html/1902.03835v2#S3).
The source does not yet identify `distribution 0` with `1/2`, prove reflection symmetry,
or expose an interior `ContDiff` API. Neither endpoint differentiability nor global
concavity of the zero extension is asserted.

## Remaining work

These are scalar prerequisites, not Proposition 3.1 (32)--(33). Next provide the
regularized-profile calculus (interior smoothness, compact-range derivative bounds,
and the shifted profile used in the interpolation), then prove the corresponding
closed-generator chain rule and heat interpolation. Retain all domain, integrability
and endpoint passage obligations. The current heat-gradient bound remains
`M/sqrt(2t)` and the small-time/perimeter coefficient remains `sqrt(2t)`.
The sharp coefficients, general-law passage, full pi Buser assembly and
 dimension-free KLS remain unproved.

## Verification

Strict source compilation and `research/audits/GaussianProfileAudit.lean` check the
actual Gaussian specialization, inverse, ODE, scalar range, attained bound, endpoints,
closed-interval continuity and strict concavity. Eight transitive axiom reports are
required to contain only `propext`, `Classical.choice`, and `Quot.sound`.
The full project verifier, its source snapshot and actual-index preservation are
recorded in `build/audit/gaussian-profile/final-snapshot.json` after validation.
No commit, push or remote CI is part of this round.

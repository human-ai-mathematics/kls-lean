# Poincaré upper stability of the actual Gaussian convolution

Date: 2026-09-25. Local continuation; no commit or push.

## Placement and proved scope

The generic smooth-test product estimate is in
`Poincare/Product/Tensorization.lean`; scalar pushforward is in
`Poincare/SmoothTest/Transport.lean`; the addition-map result is in the new
`Poincare/Convolution.lean`; the finite-dimensional standard Gaussian bound
is in `Poincare/Gaussian/Multivariate.lean`. The specialization of the actual
normalized kernel and convolution is in
`KLS/LogConcave/Density/GaussianPoincare.lean`. Earlier public signatures
are preserved.

The actual normalized Gaussian law is identified, through its characteristic
function and uniqueness, with the image of the standard multivariate Gaussian
under scaling by `1/sqrt(2s)`. This includes dimension zero. The scalar
transport theorem gives it a smooth-test Poincaré constant `1/(2s)`. An
anisotropic product Poincaré estimate, followed by the addition map, proves
the convolution bound at fixed finite constants. Passing to the extended
smooth-test optima does not require their attainment. The log-concave
smooth-test/literature identification gives the final theorem for every
Borell probability density `ρ` of a probability law `ν` and every `s > 0`:

`C_P^lit(smoothedProbabilityLaw ν s) ≤ C_P^lit(ν) + ENNReal.ofReal (1/(2s))`.

The source may have infinite optimum. No source moment, compact support, or
smoothness is assumed. `GaussianPoincareStabilityAudit.lean` contains
independent full-signature clients for the actual Gaussian factor, the actual
convolution optimum, the intrinsic literature optimum, and dimension zero.
Strict compilation reports only `propext`, `Classical.choice`, and
`Quot.sound` as transitive axioms.

## Remaining mathematical gap

The relative-perimeter passage and the assembly of π-Buser for general
positive-dimensional nonsmooth Borell laws remain open. This result does not
prove the full Buser comparison or dimension-free KLS.

## Source evidence

- Product tensorization source SHA-256: `9093e6a2cdf4139637c1ed5f9b723b9aee697eabdc477b05c85b24f3912561f3`.
- Scalar transport source SHA-256: `dfced503130a31a01e17ca81206fcb20b47e1911037bbbc01ab17f07489063f3`.
- Convolution source SHA-256: `24bfb4982155d650237c4491e8453f0aa8fdc285923e0a45eff5eff99f6f6703`.
- Multivariate Gaussian source SHA-256: `09dbc48c3eef2332b3f6943d78d34753288f8e27c87d188f0a0a3a144ae061c9`.
- Actual Gaussian specialization SHA-256: `b320880143ac5c424f9d78bd96f9792c20f68df97f3c8520ae089fcee3f1ce09`.
- Full-signature client SHA-256: `9c2c8c6079a652fb2680dd908caf741d191f7c184b361b1416c7a86ba376777c`.
- Frozen full-verifier receipt: `build/audit/gaussian-poincare-stability/final-snapshot.json`.

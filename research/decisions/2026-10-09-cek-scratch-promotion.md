# CEK scratch promotion: convex duality and Lemma 17 (2026-10-09)

Source: Cordero-Erausquin–Klartag, *Moment measures*, arXiv:1304.0630v1. The root-accepted Lemma 17 scratch bundle
was assembled into an integration candidate, independently accepted by root
(`build/reviews/2026-10-09-moment-map-letwin-parallel/independent-integration-review/ACCEPTANCE.json`), and applied as
the exact 13-file patch (SHA-256 `a81b0e9a…`). The complete declaration and module map is
[`2026-10-09-cek-scratch-promotion-map.json`](../api-migration/2026-10-09-cek-scratch-promotion-map.json).

This is a promotion of scratch declarations, not a migration of an existing production API: the
`KLSConstruction.MomentMap` names never existed in production. The only existing production module touched,
`Probability/ConvexSupport.lean`, is extended; its nine constants keep their types, universes, kinds and values.

Placement:

- `Analysis/Convex/` (namespace `FunctionalInequalities.Analysis`): measure-free extended-real potentials and the
  Legendre transform (`Legendre.lean`), finite affine maxima (`AffineMaximum.lean`), pointwise compactness of convex
  functions and the radial extension.
- `Probability/ConvexSupport.lean`: CEK Lemma 16 for finite measures (finiteness near interior points, the finite-measure
  halfspace bound, the point control).
- `Probability/MomentMeasure/` (namespace `FunctionalInequalities.Probability.MomentMeasure`): exponential-potential
  measure, mass and the CEK functional (`Basic.lean`), conjugate-mass semicontinuity (56b) (`ConjugateMass.lean`),
  and Lemma 17 (56a) with the joint (56) theorem (`Compactness.lean`). `integrable_exp_sub_norm` and (56a) involve no
  moment-measure object and stay in `FunctionalInequalities.Probability`.
- Clients: `research/audits/CEK/` (per-paper audit folder).

Short names are unchanged. Deferred, not promoted: `effectiveDomain`, `potentialGradient`, `HasMomentMeasure`,
`EssentiallyContinuous` (Theorem 2 statement objects without a consumer in this batch). Lemma 17 is promoted in its
geometric form with explicit `0 ∈ interior (convexHull ℝ μ.support)`; the adapter from the Theorem 2 conditions is not
promoted. Proposition 12 attainment, Lemmas 14–15, essential continuity, existence and uniqueness remain open. No paper
coverage or ledger certificate changes.

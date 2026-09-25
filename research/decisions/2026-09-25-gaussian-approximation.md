# Gaussian approximation of a nonsmooth Borell probability law

Date: 2026-09-25. Local continuation; no commit or push.

## Placement and proved scope

`KLS/LogConcave/Density/BorellRepresentation/Basic.lean` now proves
`IsBorellDensity.ae_continuous` relative to any Haar measure on a
finite-dimensional real inner product space. The density is continuous on
the interior of its convex positivity set, locally zero outside its closure,
and the frontier has Haar measure zero. This uses no Gaussian smoothing.

`KLS/LogConcave/Density/GaussianApproximation.lean` owns the distinct
approximation step and imports the normalized construction from
`GaussianSmoothing.lean`. The normalized kernel satisfies the exact scale
identity and the tail hypothesis of Mathlib's peak-function theorem. For a
Borell probability density `ρ`, the actual normalized convolution density
converges to `ρ` at each continuity point and Haar-almost everywhere as its
inverse variance `s → ∞`.

Unit integral of both densities and dominated convergence of their pointwise
minimum give
`∫ |normalizedDensity ρ s - ρ| dvolume → 0`.
Restricted integral comparison then proves convergence of the density
integral on every set. Finally, the actual `withDensity` identities prove
`(smoothedLaw ν s) D → ν D` in `ENNReal` for every measurable `D`.
No existing public signature changed. The independent full-signature clients
`BorellDensityContinuityAudit.lean` and `GaussianApproximationAudit.lean`
report only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

## Remaining mathematical gap

This closes the law mass convergence ingredient of the nonsmooth π-Buser
route. The Gaussian convolution potential has only been proved continuous
and convex, not `C∞`, so the existing smooth-model theorem cannot yet be
applied. The needed upper stability of the intrinsic literature Poincaré
constant and the relative-perimeter passage remain unproved. Setwise law
convergence alone gives neither of those conclusions. The unrestricted
positive-dimensional π-Buser comparison and dimension-free KLS theorem
therefore remain pending.

## Source evidence

- Borell basic source SHA-256: `6d8ee55c8a5efed9db481f0bda14f1b9e7b54ccd02bea9b02daca75010e9bf94`.
- Gaussian approximation source SHA-256: `3606005953f649247e207313e1780f25da7ec37535f6a2cc4b9d67c6d9459116`.
- Borell continuity client SHA-256: `e528a66b300cbb7143ec74e8d681683b139dbef88637e1a2cdab9de16378a0b8`.
- Gaussian approximation client SHA-256: `6eea3b237f2967cace1a0df6051e88ccaa942ae6b92eba616279decbd28e39a3`.
- Frozen full-verifier receipt: `build/audit/gaussian-approximation/final-snapshot.json`.

# Second regularity of the actual Gaussian convolution

Date: 2026-09-25. Local continuation; no commit or push.

## Placement and proved scope

`KLS/LogConcave/Density/GaussianSmoothing.lean` now proves that the normalized
Gaussian convolution density and its negative logarithm are `ContDiff ℝ 2`
for every Borell probability input and every positive inverse variance on a
finite-dimensional real inner product space. This includes dimension zero.

The explicit first Gaussian derivative from the preceding round is
differentiated once more. The norm of that derivative is uniformly bounded by
`6 s / mass s`: the radial estimate follows from
`(s‖z‖²) exp(-s‖z‖²) ≤ 1`. This constant bound is integrable against every
source probability law, so Mathlib's dominated parametric-integral theorem
differentiates the actual first-derivative integral. Dominated continuity of
the second-derivative integral gives `normalizedDensity_contDiff_two`.
Strict positivity and the logarithm chain rule give `potential_contDiff_two`.
The earlier public signatures remain unchanged.

The independent full-signature client `GaussianSecondRegularityAudit.lean`
checks both `C²` statements. Strict compilation reports only `propext`,
`Classical.choice`, and `Quot.sound` as transitive axioms.

## Remaining mathematical gap

The existing smooth-model π-Buser theorem requires `ContDiff ℝ ∞ U`.
`C²` does not meet that hypothesis. Uniform bounds and differentiation for
every derivative order remain necessary. Upper stability of the intrinsic
literature Poincaré constant under convolution and the relative-perimeter
passage are separate, still unproved obligations. The unrestricted
positive-dimensional π-Buser comparison and dimension-free KLS remain open.

## Source evidence

- Gaussian smoothing source SHA-256: `e383d05acb4555d9830002f1ed9651f800ddf18c0ebb552c067ff0592ad4d6c5`.
- Full-signature client SHA-256: `4e2906a2f9d23f1c5bde23268dad57356d2cd8b64e3824a75dc56143d77379c8`.
- Frozen full-verifier receipt: `build/audit/gaussian-second-regularity/final-snapshot.json`.

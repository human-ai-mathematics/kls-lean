# Normalized Gaussian smoothing of an intrinsic Borell law

Date: 2026-09-25. Local continuation; no commit or push.

## Placement and result

`KLS/LogConcave/Density/GaussianSmoothing.lean` remains the owner of the
explicit Gaussian convolution. For `s > 0` on any finite-dimensional real
inner product space, including dimension zero, the unnormalized kernel has
mass `(π/s)^(finrank/2)`. Division by this positive mass gives a probability
density. Convolution with a Borell probability law is a probability law with
an explicitly identified Haar density. The density is measurable, everywhere
positive, finite, continuous, integrable with integral one, and pointwise
log-concave. Its negative logarithm is a continuous convex potential, and
the convolution law is exactly volume tilted by that potential.

`KLS/LogConcave/Density/FromBorell.lean` owns a general finite-dimensional
converse: an actual pointwise log-concave Borell density of a probability
law implies compact-set `LogConcave`. Its proof uses the established
finite-dimensional Prékopa–Leindler theorem and the compact combination
lemma. Applying it to the normalized convolution yields a log-concave
probability law. The older one-dimensional interface and all public
signatures remain unchanged.

The full-signature clients `BorellDensityLogConcavityAudit.lean` and
`GaussianSmoothingAudit.lean` compile independently. Their transitive
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining mathematical gap

Continuity of the potential is weaker than `ContDiff ℝ ∞`, required by the
current smooth-model Buser theorem. Mathlib's general convolution smoothness
interface found in the pinned revision assumes compact support of the smooth
factor; the Gaussian factor used here is not compactly supported. A separate
analytic differentiation argument is needed. Also unproved are convergence of
these smoothed laws to the source law, upper stability of the literature
Poincaré optimum in the required direction, and domain mass/perimeter
convergence with extended-real boundaries. Consequently this record does not
prove the unrestricted positive-dimensional π-Buser comparison or KLS.

## Source evidence

- Finite-dimensional converse SHA-256: `aaf17afe1c48c4e1236ca330567bf7cd300480c977c53620e6000827b9399bf3`.
- Gaussian smoothing SHA-256: `f3fc9f72f0afaa106950905e53be2489aa7f6e38855e411de59854309140e1da`.
- Converse client SHA-256: `4cd9ac039f3c6915d78faab3c0fd7cb618f1e8df5227ccabf3c9f88cf6d0ee43`.
- Smoothing client SHA-256: `f622b380bb07efebda7da2f95111e635e3fb1f384d89e47b9b990ddd710454a4`.
- Frozen full-verifier receipt: `build/audit/gaussian-normalization/final-snapshot.json`.

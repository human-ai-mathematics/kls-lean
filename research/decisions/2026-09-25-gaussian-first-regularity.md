# First regularity of the actual Gaussian convolution

Date: 2026-09-25. Local continuation; no commit or push.

## Placement and proved scope

`KLS/LogConcave/Density/GaussianSmoothing.lean` owns the normalized kernel,
convolution density, and logarithmic potential. It now also proves their
first-order regularity. The Gaussian kernel's Fréchet derivative is computed
explicitly. The radial bound for `r exp(-s r²)` gives an integrable constant
bound on its derivative against every source probability law. Mathlib's
dominated parametric-integral theorem therefore differentiates the actual
convolution integral, with no moment assumption on the source law.

For every finite-dimensional real inner product space, Borell probability
density `ρ`, `s > 0`, and point `x`, `normalizedDensity_hasFDerivAt` identifies
the derivative as the integral of
`(-2 s normalizedKernel s (x-y)) • innerSL ℝ (x-y)` against the source law.
Dominated continuity of that integral proves `normalizedDensity_contDiff_one`.
The density is everywhere positive, so the logarithm chain rule proves
`potential_contDiff_one`. These are `C¹` theorems, including dimension zero.
All earlier public declarations retain their signatures.

`GaussianFirstRegularityAudit.lean` is an independent full-signature client
for the derivative formula and both `C¹` conclusions. Strict Lean compilation
reports only `propext`, `Classical.choice`, and `Quot.sound` as transitive
axioms.

## Remaining mathematical gap

The current smooth-model π-Buser theorem requires `ContDiff ℝ ∞ U`; the new
`C¹` potential does not satisfy that hypothesis. Iterated Gaussian derivative
bounds and iterated dominated differentiation remain to be formalized.
Upper stability of the intrinsic literature Poincaré constant under
convolution and the relative-perimeter passage remain separate. Setwise and
`L¹` law convergence do not imply either. The unrestricted positive-dimensional
π-Buser inequality and dimension-free KLS therefore remain open.

## Source evidence

- Gaussian smoothing source SHA-256: `c283d757b159b23068364e3a4cdbef663f6f2964cda5033490ffa660d2f501d3`.
- Full-signature client SHA-256: `dbe2805ed1dc8855c4da7af63dd75d304e8a282e886599150b729ad493488724`.
- Frozen full-verifier receipt: `build/audit/gaussian-first-regularity/final-snapshot.json`.

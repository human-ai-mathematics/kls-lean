# All-order regularity of the actual Gaussian convolution

Date: 2026-09-25. Local continuation; no commit or push.

## Placement and proved scope

`KLS/LogConcave/Density/GaussianSmoothing.lean` remains the owner of the
normalized kernel, actual convolution density, and logarithmic potential. It
now proves `normalizedDensity_contDiff_infty` and `potential_contDiff_infty`
for every finite-dimensional real inner product space, including dimension
zero, every Borell probability density, and every `s > 0`. Earlier public
declarations retain their signatures.

The proof first bounds `r^n exp(-s r²)` globally for each finite `n` using
Gaussian decay at infinity and continuity. Mathlib's temperate-growth bound
for the squared norm and its iterated composition estimate then bound every
finite Fréchet derivative of the Gaussian kernel by a polynomial times the
same Gaussian. This gives a constant bound for each derivative order. A
separate induction applies dominated parametric differentiation to the
actual integral against the source probability law. Continuity supplies
measurability, and each constant bound is integrable under that law. The
zero-order continuous multilinear map is evaluated back to the scalar
integral. The existing `normalizedDensity_eq_integral` identifies this
smooth integral with the already constructed normalized density. Strict
positivity and the logarithm chain rule give the potential result.

No source moment, compact-support, smooth-density, or conclusion-shaped
regularity hypothesis is used. The independent full-signature client
`GaussianInfiniteRegularityAudit.lean` checks both conclusions and explicit
zero-dimensional specializations. Strict compilation reports only `propext`,
`Classical.choice`, and `Quot.sound` as transitive axioms.

## Remaining mathematical gap

This closes the smooth-potential regularity input only. Upper stability of
the intrinsic literature Poincaré constant under Gaussian convolution,
relative-perimeter transfer, and unrestricted positive-dimensional
nonsmooth π-Buser assembly remain independent obligations. This result
does not prove Buser or dimension-free KLS.

## Source evidence

- Gaussian smoothing source SHA-256: `4c825958029c17c39a09d271a88008b22268bd085d07ca89d3d768bce605f2b8`.
- Full-signature client SHA-256: `1ab3c905f4d11b083d0284129f51c97fcfb7f9e08028615f888384e9955b7181`.
- Frozen full-verifier receipt: `build/audit/gaussian-infinite-regularity/final-snapshot.json`.

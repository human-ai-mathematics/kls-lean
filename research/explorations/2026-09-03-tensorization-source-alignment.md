# Tensorization source correspondence and semantic review

**Date:** 2026-09-03 (Asia/Shanghai).
**Review:** Codex source and mathematical correspondence review for Issue #6.
**Node:** `lem:poincare-tensorization`.

The sources support the selected binary upper-bound result. The repository proves its
concrete smooth-test version independently; it does not identify arbitrary Borel measures
with a Markov triple or identify their smooth-test constants with Sobolev constants. This
record supplies the source-alignment acceptance evidence. Human signature freezing, proof
certification, finite-dimensional compilation checks, and final-commit CI have separate
acceptance records; none is certified by this source review.

## Sources and correspondence

Bakry, Gentil and Ledoux, *Analysis and Geometry of Markov Diffusion Operators* (2014),
§4.3, Proposition 4.3.1, printed pp. 185–187, establishes product stability with constant
`max(C₁, C₂)` for two Markov triples. The product energy is the sum of the integrated
coordinate energies, with normalization `Var(f) ≤ C E(f)`. Its proof uses the Dirichlet
domain and an averaging lemma, Lemma 4.3.2. The bibliography key is
`BakryGentilLedoux2014`.

- [Publisher chapter and DOI](https://link.springer.com/chapter/10.1007/978-3-319-00227-9_4).
- [Full text, printed pp. 185–187 / PDF pp. 201–203](https://www.hse.ru/data/2016/11/24/1113029204/bok%253A978-3-319-00227-9.pdf#page=201).

The numerical correspondence is `C₁ ↦ C`, `C₂ ↦ C'`, and coordinate energy
`↦ ∫ ‖gradient f‖²`. Thus no reciprocal, square, or factor-of-two conversion occurs.
`Poincare.Holds.prod` supplies the fixed-constant conclusion; `constant_prod_le` adds the
repository's extended-infimum formulation. The normalization also preserves the reading
of `KLS.pdf`, Definition 2.1 recorded in `FunctionalInequalities/Basic.lean`.

The function-domain correspondence is deliberately limited. The local `Admissible μ f`
requires a globally `C∞` real-valued function, `MemLp f 2 μ`, and integrable squared
canonical Hilbert gradient. BGL's Dirichlet-domain assumptions are not silently inherited.
For example, on `ℝ` with `μ = δ₀`, the smooth functions `f = 0` and `g(x) = x` are equal
almost everywhere, but their local gradient energies are respectively `0` and `1`.
Consequently this raw smooth-function energy is not automatically a well-defined closed
Dirichlet form on `L²(μ)` equivalence classes. This observation does not obstruct the
smooth-test inequality or its tensorization.

Courtade, *Bounds on the Poincaré constant for convolution measures*, §2.1.2, explicitly
defines a Poincaré constant relative to a chosen class of tests and discusses density when
passing between classes. Its Euclidean Sobolev example assumes a measure with a Lebesgue
density. This supports keeping the domain explicit; it supplies no equivalence for every
Borel probability allowed here. The metric slope discussed there also must not be
silently substituted for the canonical gradient in this API.

- [Courtade, arXiv:1807.00027, §2.1.2, PDF pp. 5–6](https://arxiv.org/pdf/1807.00027#page=5).

## Direct use in the KLS manuscript

At upstream commit `8185e46ffb040e04fea076953e5bcaeb4157d71a`, the proof of
`prop:products` (iii) uses the finite-product identity for Poincaré constants, bounds each
one-dimensional log-concave factor's constant by a universal multiple of its variance,
and applies the log-concave Cheeger–Poincaré comparison. Together these give the stated
Cheeger lower bound in terms of the largest coordinate variance. Parts (i) and (ii)
separately concern preservation of product structure and the scalar variance processes
under stochastic localization.

- [Pinned `prop:products` statement and proof](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/8185e46ffb040e04fea076953e5bcaeb4157d71a/modules/kls/16-model-geometries.tex#L64).

Issue #6 supplies the binary Poincaré upper-bound ingredient. Its finite iteration, the
one-dimensional log-concave estimate, the comparison of the relevant test domains, and
the Cheeger–Poincaré comparison remain necessary downstream steps. The upper-bound
direction suffices for that analytic dependency once those steps are available. This
node alone does not certify `prop:products` or its localization statements.

## Independent justification on the stated Hilbert spaces

The following is the mathematical correspondence of the local proof, not an assertion
that the cited Dirichlet-domain theorem already covers this API.

1. Transport the ordinary product measure by `WithLp.toLp 2` to
   `WithLp 2 (E × F)`. The latter has the Hilbert norm; the ordinary product retains its
   standard maximum norm. Probability, integrals, and L² membership transport through
   this measurable equivalence.
2. Smooth affine coordinate inclusions give smooth sections. Riesz duality and the
   Hilbert product inner product identify their gradients with the two components of
   the full gradient, whose squared norm is the sum of their squared norms.
3. Fubini gives L² sections almost everywhere. Each partial squared gradient is
   nonnegative and dominated by the integrable full squared gradient, so Fubini also
   gives finite-energy sections almost everywhere. Continuity and the Borel,
   second-countable hypotheses supply the needed measurability.
4. For the pulled-back L² function, total variance and Jensen's square inequality give

   \[
   \operatorname{Var}_{\mu\otimes\nu}(f)
   \leq \int\operatorname{Var}_{\mu}(f(\cdot,y))\,d\nu(y)
      + \int\operatorname{Var}_{\nu}(f(x,\cdot))\,d\mu(x).
   \]

   All real-integral manipulations retain their integrability hypotheses. Applying the
   two factor inequalities to the admissible sections yields `C A + C' B`, where
   `A, B ≥ 0` and `A + B` is the product energy. This is at most
   `max(C, C') (A + B)`. No differentiation of an integral or smoothness of an averaged
   function is required.

These steps use Hilbert geometry and probability/Fubini arguments, with no finite basis
or dimension-dependent estimate. They therefore justify the stated real separable
Hilbert generality, including Euclidean factors. No second moment, density, or positive
dimension assumption is needed.

The almost-everywhere qualification cannot be strengthened to every section. For
standard Gaussian `μ` on `ℝ`, `ν = δ₀`, and `f(x,y) = y² exp(x²)`, the function and full
gradient vanish on the product support, so the product test is admissible. A section at
`y ≠ 0` is not in `L²(μ)`.

For the `ENNReal` conclusion, any infinite factor constant makes the upper bound
automatic. More generally, if the product constant were strictly above the maximum of
the two infima, the defining infima would supply finite valid factor constants both
strictly below the product constant. Their maximum is valid by `Holds.prod`, a
contradiction. No attainment assumption is used. Zero-dimensional factors are singletons;
their variances vanish and their optimal constants are zero. The proof uses no division
by dimension or positive energy.

The local correspondence is realized by `ProductGeometry.lean` (transport and gradients),
`ProductVariance.lean` (L² sections and variance), `ProductAdmissible.lean` (a.e.
admissibility and energy), and `Tensorization.lean` (the two public conclusions), under
`formalization/FunctionalInequalities/`. The semantic definitions in `Basic.lean` remain
the reference throughout.

## Scope of this acceptance

The sources, normalization, test class, Hilbert extension, and upstream dependency are
matched for the two public upper-bound statements. This node does not assert the reverse
bound, optimal-constant equality, a finite-family API, a Sobolev or spectral-gap bridge,
or the complete product-case KLS theorem. This entry records source and semantic review
only and makes no claim about a remote CI run for the final published commit.

# Related KLS formalizations

Checked 2026-10-20 against the default-branch source revisions below. This is a source and
documentation comparison of public endpoints. No third-party repository was rebuilt or
independently certified in this review. The root [README](../../README.md#related-formalizations)
keeps the compact table; the [literature register](LITERATURE.md) owns our paper coverage.

## Inspected revisions and endpoints

| Project | Source revision | Public endpoints | Lean pin |
| --- | --- | --- | --- |
| kls-lean | [2639e79](https://github.com/human-ai-mathematics/kls-lean/tree/2639e79bfa2b0070285d357d1a8efd97f71978d8) | [`KLS.kls`](../../formalization/FunctionalInequalities/KLS/Target.lean), [`KLSOpenAI.kls`](../../integrations/openai/KLSOpenAI/Target.lean) | v4.33.0 |
| KLS500 | [c1a5099](https://github.com/HongruZhao/KLS500/tree/c1a50992a81456849996deef2971d4a0b3190bdd) | [`KLS500.poincare500`, `KLS500.cheeger197`, `KLS500.openaiKLS`](https://github.com/HongruZhao/KLS500/blob/c1a50992a81456849996deef2971d4a0b3190bdd/KLS500.lean) | [v4.35.0-rc3](https://github.com/HongruZhao/KLS500/blob/c1a50992a81456849996deef2971d4a0b3190bdd/lean-toolchain) |
| KLS15 | [fe59199](https://github.com/HongruZhao/KLS15/tree/fe59199e9c039a79a436daa939f79662df2596da) | [`KLS15.poincare15`, `KLS15.openaiKLS`](https://github.com/HongruZhao/KLS15/blob/fe59199e9c039a79a436daa939f79662df2596da/KLS15.lean) | [v4.35.0-rc3](https://github.com/HongruZhao/KLS15/blob/fe59199e9c039a79a436daa939f79662df2596da/lean-toolchain) |

## Mathematical statements and sources

Our [target](../../formalization/FunctionalInequalities/KLS/Statement.lean) chooses one finite
nonnegative constant before every dimension and log-concave probability law with finite second
moment. It bounds the intrinsic local-slope Poincaré constant by the operator norm of covariance
times that universal constant. Dimension zero and singular affine supports are included. The
closed BKL proof uses finite-horizon cutoff localization; no numerical final KLS bound is extracted.
The separate [noncompact Letwin theorem](../../formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean)
retains constant 8. It is not an explicit final KLS constant.

KLS500's [README](https://github.com/HongruZhao/KLS500/blob/c1a50992a81456849996deef2971d4a0b3190bdd/README.md)
and public source give the upper bound 500 for locally Lipschitz L² tests under isotropic
log-concave laws in positive dimension. They also give the Cheeger lower bound
`100 / (197 * sqrt 500)`. The development identifies BKL and Song–Zhang as its principal
proof sources. KLS15's [README](https://github.com/HongruZhao/KLS15/blob/fe59199e9c039a79a436daa939f79662df2596da/README.md)
and public source give the upper bound 15 for that test/law class and identify
Balasubramanian–Kasiviswanathan arXiv:2610.07728v2 as the proof source. Its README explicitly
describes KLS15 as continuing KLS500.

Both public law predicates use compact-set log-concavity and explicit moment integrability:
see [KLS500 definitions](https://github.com/HongruZhao/KLS500/blob/c1a50992a81456849996deef2971d4a0b3190bdd/KLS/Definitions.lean)
and [KLS15 definitions](https://github.com/HongruZhao/KLS15/blob/fe59199e9c039a79a436daa939f79662df2596da/KLS/Definitions.lean).
The displayed endpoint parameterizations differ; affine/isotropic reductions relate them.
The table does not rank originality, overall library coverage or proof quality.

All three inspected projects have a theorem with the exact OpenAI `KLSStatement` as its type.
The three copies of the pinned upstream model have the same SHA-256:
`28cddbf3c493afd43b3f7aba78f670952ea0c38909665c86bff883849e7f8dbc`.
Our [source record](../../integrations/openai/UPSTREAM.json) identifies the OpenAI revision.
The common endpoint tests smooth compactly supported functions and keeps one positive constant
before every dimension `n ≥ 1`, density and test.

## Verification and reuse boundaries

Our [Comparator setup](../audits/KLS/Comparator/README.md) has recorded macOS development-mode
acceptance, with source-bound statement/definition matching, standard-axiom checks and Lean
kernel replay. Nicolas [reports both Linux sandbox targets passed at 2639e79](https://github.com/human-ai-mathematics/kls-lean/issues/10#issuecomment-6289895395).
The full receipts and logs await incorporation and have not yet been inspected in this checkout;
the report is kept distinct from a reviewed receipt. The source revision used for this comparison
does not have a new remote CI receipt. See the [verification scope](../verification.md#receipts-and-trust-scope).

The pinned [KLS500 verification notes](https://github.com/HongruZhao/KLS500/blob/c1a50992a81456849996deef2971d4a0b3190bdd/verification/README.md)
and [KLS15 verification notes](https://github.com/HongruZhao/KLS15/blob/fe59199e9c039a79a436daa939f79662df2596da/verification/README.md)
describe source builds and endpoint standard-axiom checks, and explicitly state that Comparator
was not run. That cell does not mean those projects lack verification.

Our stochastic-calculus foundation is external LevyStochCalc and its dependencies. KLS500's
import closure informed the original vendor selection; our source pins, tested overrides and
toolchain adaptations are credited in the [vendor policy](../../formalization/vendor/README.md).
Shared dependencies do not establish authorship of the downstream proofs.

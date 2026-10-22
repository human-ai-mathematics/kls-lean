# Public interfaces and maintainer review

Reviewed 2026-10-20 against the mathematical source at `2639e79`. This document records an agent
interface/source inspection and the maintainer's reported review scope. It is not a human
signoff or a new proof receipt. The [statement review](statement-review.md) owns the 34 certificate
contracts; the [target reviews](target-reviews.md) and [literature register](LITERATURE.md) own
paper correspondence. The follow-up corrects source comments and mathematical reading aids;
declaration types, proof bodies, imports and certificate states are unchanged.

## Review scope already reported

The maintainer reports having reviewed the original important definitions and APIs. They
explicitly report not yet personally reviewing the OpenAI part or the external upstream APIs.
No per-declaration or per-revision human approval is inferred from that general statement.
In particular, a public API is a caller-visible interface; an upstream API belongs to an
external dependency. The generated [API directory](../../formalization/API.md) covers the
project-local library, not the separate OpenAI package or all vendor interfaces.

Nicolas [reports checking the bridge, its pinned model hash, metadata and the Letwin result](https://github.com/human-ai-mathematics/kls-lean/issues/10#issuecomment-6288377384).
This is a recorded limited inspection, not an itemized whole-library semantic approval.
Separate Claude/GPT review passes and compiler/axiom/kernel checks keep their own scopes.

## Source/interface findings

| Entry inspected | What the current statement actually says | Finding |
| --- | --- | --- |
| [`KLS.Conjecture`](../../formalization/FunctionalInequalities/KLS/Statement.lean#L28) and [`KLS.kls`](../../formalization/FunctionalInequalities/KLS/Target.lean#L24) | One finite `NNReal` constant precedes every dimension and law; log-concavity and finite second moment; intrinsic constant times covariance operator norm. The endpoint closes the proposition. | Quantifier order, zero dimension and singular support agree with the README. No numerical final constant is claimed. |
| [`LogConcave`](../../formalization/FunctionalInequalities/Probability/LogConcave.lean#L28), [`Isotropic`](../../formalization/FunctionalInequalities/KLS/Isotropic.lean#L31), [local-slope tests](../../formalization/FunctionalInequalities/Energy/LocalSlope/Basic.lean#L154) and [intrinsic optimum](../../formalization/FunctionalInequalities/Poincare/LocalSlope/Basic.lean#L26) | Compact-set log-concavity; actual second-moment integrability; zero mean and centered covariance identity; locally Lipschitz L² finite-energy tests; no factor `1/2` in energy. | The definitions retain the intended normalization and the integrability premises. Earlier key-definition review is recorded without requesting a blanket repeat. |
| [Closed BKL producer](../../formalization/FunctionalInequalities/KLS/BKL/Poincare.lean#L24) and [proof path](PROOF-PATH.md) | Universal positive bound from the cutoff route and the proved compact Letwin input. `153` is a cumulant witness, not the final KLS constant. | Closed and conditional producers are distinct; the uncut Eldan construction and literal stochastic identities remain separate. |
| [Noncompact Letwin](../../formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean#L42) and [matrix form](../../formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean#L119) | Every `n > 0`, isotropic log-concave probability law and symmetric matrix; `Var(XᵀMX) ≤ 8 tr(M²)`, including singular and indefinite matrices. | No compactness or extra fourth-moment premise. The compact certificate remains compact; the separate theorem is now proved. Earlier review text has been clarified accordingly. |
| [OpenAI model](../../integrations/openai/OAI/Analysis/KLS/Model.lean), [bridge](../../integrations/openai/KLSOpenAI/Bridge.lean) and [closed target](../../integrations/openai/KLSOpenAI/Target.lean) | Exact pinned density statement; measurable log-concavity, explicit coordinate moments, positive universal constant and smooth compactly supported tests. The bridge uses `C + 1` and the target supplies the existing closed proof. | Source copy/hash and the two endpoint types agree. The maintainer has not yet personally reviewed this part. The bridge metadata now says so explicitly. |
| [Application client](../../examples/KlsApplications.lean), [first-use guide](../../examples/FIRST-USE.md) and [smooth-test variance consumer](../../formalization/FunctionalInequalities/Poincare/SmoothTest/Basic.lean#L74) | Consumers preserve L² and finite squared-gradient energy; the Gaussian convolution bound is `C + t`, including `t = 0`. | The demonstrated caller path is present. `Holds.variance_le` lacks a source docstring: a documentation improvement, not a missing hypothesis or a request for new mathematical proof. |

The compiler inventory at the review baseline has 5,783 public declarations across 586 source modules plus
the aggregate root, with no `unsafe` or `partial` flags. It reports 1,245 rows without a
docstring and 228 without a declaration source range; generated names such as `congr_simp`
occur in the latter group. These counts are documentation/navigation findings, not evidence
of mathematical errors. This inspection does not reprove every auxiliary declaration or
claim that every exported name has received individual human review.

The corrected [third-cumulant documentation](../../formalization/FunctionalInequalities/KLS/BKL/LocalThirdCumulant.lean)
keeps its explicit Letwin input while pointing to the separately proved noncompact producer.
The [Cheeger foundation](../../formalization/FunctionalInequalities/Energy/Cheeger/Basic.lean)
now points to the unconditional [identification](../../formalization/FunctionalInequalities/Energy/Cheeger/Identification.lean),
including singular laws. The KLS endpoint's leaf description distinguishes proof modules from
the aggregate export. These are corrections to descriptions of existing results.

The reading aids distinguish the following scopes. `CumulantBound d b` controls order `d + 1`,
so the suspension coefficient is `2 b / (d!)²`. `RegularPotential V a b` requires `a > 0`
and both Hessian bounds; `b > 0` follows in positive dimension, while dimension zero allows any `b`.
The [BKL Poincaré certificate](../../solutions/ThmBklPoincare.lean)
quantifies over `n ≥ 1` on `EuclideanSpace ℝ (Fin n)`; its separate `bound` uses the broader
`KLS.IsotropicBound` interface. Approval of one statement does not imply approval of the other.
The focused compiler observations retain their original scope; these comment corrections are
not a fresh compiler extraction, full proof review or personal signoff.

## Focused maintainer checklist

Record approval, a concrete correction, or an intentional scope choice for each item. Compiler
success does not answer these mathematical and usability questions.

| ID | Reading entry | Human decision still needed | Current status |
| --- | --- | --- | --- |
| OAI-1 | [OpenAI model](../../integrations/openai/OAI/Analysis/KLS/Model.lean#L15) | Accept the exact density/isotropy assumptions and smooth compact-support test class; verify `∃ C > 0` comes before all `n ≥ 1`, densities and tests, and energy is `∫ ‖∇f‖²`. | Maintainer explicitly has not reviewed it. Nicolas reports checking the bridge/model hash. |
| OAI-2 | [`logConcave`](../../integrations/openai/KLSOpenAI/Bridge.lean#L51), [`isotropic`](../../integrations/openai/KLSOpenAI/Bridge.lean#L83), [`of_conjecture`](../../integrations/openai/KLSOpenAI/Bridge.lean#L131), [target](../../integrations/openai/KLSOpenAI/Target.lean#L9) | Read the conversion argument: measurable density to compact-set law, coordinate moments to covariance, admissible tests and variance/energy normalization; confirm `C + 1` stays universal and no extra regularity assumption enters. | Maintainer review pending; mechanical and agent checks already exist. |
| UP-1 | [Vendor policy and changes](../../formalization/vendor/README.md#local-changes), [regularization boundary client](../audits/StochasticCalculus/Regularization.lean), [Levy consumer](../../formalization/vendor/LevyStochCalc/LevyStochCalc/Martingale/CadlagModification.lean#L116) | Check the external contracts we consume: right-continuous filtration, right-continuity in measure for the retained Levy result, fixed-time a.e. equality and a.s. càdlàg paths; expectation continuity is used for a submartingale. Do not silently use the retired stronger interfaces. | External upstream APIs have not received the maintainer's personal review. The selected closure and adaptations have compiled/source/axiom checks. |
| API-1 | [KLS calling example](../../examples/KlsApplications.lean#L32), [first-use guide](../../examples/FIRST-USE.md), [API directory](../../formalization/API.md) | As an intended user, check whether the imports, named hypotheses and distinction between local-slope, smooth-test and relaxed energies are discoverable. Identify any missing public explanation; no rereading of all 5,783 declarations is required by this checklist. | Original important APIs were reviewed. The new caller-facing guide and OpenAI surface need the focused usability pass. |
| LET-1 | [Noncompact theorem](../../formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean#L42) and [matrix form](../../formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean#L119) | Confirm whether the earlier review included this recent noncompact extension. If not, inspect positive dimension, arbitrary symmetric matrix, exact constant 8 and absence of compact support; review its truncation/whitening/moment-limit argument at the desired depth. | Earlier review did not enumerate this result; coverage confirmation is pending. Nicolas reports checking the result. |

The first three items are the clearest remaining personal semantic-review gaps. The last two
are a usability decision and a coverage confirmation. Existing important-definition/API review
is preserved; this document does not reset it or mark every library interface unreviewed.

## Release coordination

Nicolas's linked comment supports Formal Conjectures first, then Mathlib, with Palomar/Zenodo
after freezing the release. He offered the README positioning pass and recommends no numerical
KLS-constant extraction for now. The local fact table supports that pass.

Nicolas [reports both Linux sandboxed Comparator targets passed at `2639e79`](https://github.com/human-ai-mathematics/kls-lean/issues/10#issuecomment-6289895395).
The full receipts and logs await incorporation and have not yet been inspected in this checkout;
the report is kept distinct from a reviewed receipt. Freezing also requires one successful CI
run on the final frozen HEAD. This documentation review launches neither check and adds no
new verification receipt.

The maintainer [accepted the Mathlib PR contact and review discussion role](https://github.com/human-ai-mathematics/kls-lean/issues/10#issuecomment-6288813867),
proposing the two Product-Lp section lemmas first and the integration pair separately, subject
to reviewer feedback. That commitment comes from the maintainer's comment, not from agent checks.

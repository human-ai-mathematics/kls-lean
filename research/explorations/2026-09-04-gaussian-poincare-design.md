# Gaussian Poincaré: statement, source and API design

Date: 2026-09-04 (Asia/Shanghai).
Baseline: `10e4c707491830ebe9d07f7bfc5e65efeddc7e2e` on `main`.
Node: `lem:poincare-gaussian-one-dimensional`, **drafted / checked_by: null**.

The user authorized the proposed file plan and requested statements first, explicit sources,
and a reading experience informed by Formech. This record covers the resulting candidate
interfaces. It does not approve their freeze, start their proofs, or publish an Issue.
The earlier [issue proposal](2026-09-03-gaussian-poincare-issue-draft.md) and
[analytic route review](2026-09-03-gaussian-poincare-route-review.md) are preserved as history.

## 1. Source map

The historical manuscript is pinned to `numina-functional-inequalities/kls-exploration`
commit `cd4a894a0faf40c0180f80b1a31eec1fdb6cb576`. The three source passages below were read
from that commit through the authenticated GitHub CLI during this preparation.

| ID | Exact source | What it supports |
| --- | --- | --- |
| G | [Gaussian covariance family, `fam:gaussian-covariance`, lines 10–37](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L10-L37) | For a centered Gaussian with positive-definite covariance, the Poincaré constant is its largest covariance eigenvalue; the one-dimensional specialization is the variance. |
| D | [Definition 2.1, `def:poincare`, lines 17–25](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25) | The normalization is variance bounded by a constant times the expected squared gradient. |
| L | [Remark 3.8, `rem:rayleigh-lower-only`, lines 108–117](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L108-L117), and G lines 24–28 | Linear tests give lower bounds and attain the Gaussian constant. |

There are four explicit differences between the source and the local candidate:

1. G states the centered, positive-definite result. Every real mean and zero variance are
   included here as local extensions; the latter is a Dirac law, not a density argument.
2. The source normalization is retained, but global `ContDiff ℝ ⊤`, finite gradient energy
   and the `ENNReal` infimum are the existing local encoding. No spectral-gap or closed
   Sobolev-domain equivalence is imported from the source's prose.
3. G proves its upper bound through Bakry–Émery/LSI. The anchored one-dimensional
   FTC–Cauchy/Tonelli route is a locally reviewed proof plan. Its helpers are not attributed
   as named theorems in that manuscript.
4. Only the Poincaré component is proposed. G also discusses LSI and transport-entropy
   constants; neither is part of this node.

## 2. Exact domain and parameters

Both main interfaces quantify over `m : ℝ` and `v : NNReal`, with no positivity premise.
`v` is the variance. `Holds (gaussianReal m v) (v : ℝ)` uses the existing real energy;
`constant (gaussianReal m v) = (v : ENNReal)` uses the existing extended infimum.

`Admissible` is unchanged: globally smooth real-valued tests, L² under the Gaussian, and
integrable squared canonical gradient. The real-line identity `gradient_eq_deriv'` supplies
the derivative interpretation. Density helpers retain `v ≠ 0`; the main interfaces do not.
`Holds.gaussianReal_variance_le` bounds every finite valid real constant, so the final equality
requires no infimum-attainment assumption.

## 3. Declaration-by-declaration provenance

All names below are in `FunctionalInequalities.Poincare`. Every one of these 20 new
mathematical declarations has `by sorry`; no part of the proof is completed in this stage.
Each declaration also has its own source note in Lean.

| File | Candidate declaration | Provenance / intended dependency |
| --- | --- | --- |
| Density | `hasDerivAt_gaussianPDFReal` | Local differentiation of Mathlib's explicit density; ordinary exponential chain rule. |
| Density | `tendsto_gaussianPDFReal_atTop` | Local density limit from the Gaussian formula and exponential limit. |
| Density | `tendsto_gaussianPDFReal_atBot` | Local reflected density limit; concerns the density, not the test. |
| Density | `integrable_centered_gaussianPDFReal` | Mathlib moment/density bridge; signed centered first moment is absolutely integrable. |
| Density | `integral_Ioi_centered_gaussianPDFReal` | Local right-tail consequence of density FTC and its limit. |
| Density | `integral_Iio_centered_gaussianPDFReal` | Local left-tail consequence, with the reflected nonnegative weight. |
| Density | `integrable_gaussianReal_iff` | Specialization of Mathlib's `withDensity` integrability equivalence. |
| Real | `interval_sq_sub_le_integral_sq_deriv` | Local finite-interval FTC–Cauchy helper. |
| Real | `Admissible.variance_le_integral_sq_sub` | Local composition of Mathlib variance shift and second-moment bound. |
| Real | `Admissible.integrable_gaussianPDFReal_mul_sq_sub` | Local L²/constant-shift and density integrability bridge. |
| Real | `Admissible.integrable_gaussianPDFReal_mul_sq_deriv` | Local energy/gradient identification and density integrability bridge. |
| Real | `lintegral_gaussian_right_triangle` | Local nonnegative Tonelli identity on m < t < x, using the right-tail weight. |
| Real | `lintegral_gaussian_left_triangle` | Local nonnegative Tonelli identity on x < t < m, using the left-tail weight. |
| Real | `Admissible.integral_Ioi_sq_sub_gaussian_le` | Local right-half-line estimate from the interval and Tonelli interfaces. |
| Real | `Admissible.integral_Iio_sq_sub_gaussian_le` | Local left-half-line estimate with energy on the same half-line. |
| Real | `Admissible.integral_sq_sub_gaussian_le` | Local assembly of the two half-lines into the anchored bound. |
| Real | `holds_gaussianReal_zero` | Local extension of G to zero variance, via Mathlib's Dirac identities. |
| Real | `holds_gaussianReal` | One-dimensional Poincaré upper bound from G and normalization D; explicit domain/parameter extensions above. |
| Real | `Holds.gaussianReal_variance_le` | Linear-test argument L and G, applied to the identity with variance v and energy one. |
| Real | `constant_gaussianReal` | Sharp one-dimensional Poincaré component of G, using the local extended-infimum encoding. |

The two public main entry points are listed first in the solution's signature output. The
supporting declarations remain visible for human review and reuse. Their precise interfaces
are candidate contracts, not frozen requirements for an unapproved proof stage.

## 4. Existing APIs and remaining obligations

Mathlib is pinned to v4.33.0, commit `db584cd6d46c92f209a44c0f1c829460d327499d`.

| Pinned module | Existing APIs used by the route |
| --- | --- |
| [Gaussian/Real](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Gaussian/Real.lean) | `gaussianReal`, its probability instance, `gaussianReal_zero_var`, the density representation and integral identity, `memLp_id_gaussianReal`, `variance_id_gaussianReal`. |
| [Gradient/Basic](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Gradient/Basic.lean) | `gradient_eq_deriv'`. |
| [Moments/Variance](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Moments/Variance.lean) | `variance_sub_const`, `variance_le_expectation_sq`, `variance_dirac`. |
| [IntervalIntegral/ContDiff](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntervalIntegral/ContDiff.lean) | `intervalIntegral.integral_deriv_of_contDiffOn_Icc`. |
| [Bochner/Basic](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean) | Integral Hölder, used with exponents 2 and 2 on finite intervals. |
| [IntegralEqImproper](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean) | `integral_Ioi_of_hasDerivAt_of_tendsto'`, `integral_Iic_of_hasDerivAt_of_tendsto'`; endpoints differ only by a Lebesgue-null singleton. |
| [L1Space/Integrable](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L807-L850) | `integrable_withDensity_iff_integrable_smul'`, `integrable_withDensity_iff`. |
| [Measure/Prod](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/Prod.lean) | `lintegral_lintegral_swap` for measurable nonnegative kernels. |

Probability normalization, Gaussian identity moments and the gradient/derivative identity are
reused directly. The new declarations expose the local combinations needed for this route;
their presence does not mean Mathlib lacks every component of them.

The upper-bound chain is: finite-interval estimate → nonnegative triangle identities → two
half-line bounds → anchored bound → variance bound. `g : ℝ → ENNReal` in the triangle
identities may take infinity, with no premature finiteness hypothesis. Explicit weighted
integrability permits the later return to real integrals. The two half-line right-hand sides
contain their own half-line energies, so adding them retains coefficient v.

Only density limits are required at infinity. No global Lebesgue L² condition on f′ is
needed; the identity test demonstrates why such a condition would incorrectly narrow the
test class. At v = 0 the source law is a Dirac measure although Mathlib's real density formula
is zero, so that branch uses neither the density representation nor the triangle helpers.

## 5. Files, review experience and Formech reference

The user-provided style reference is [lyw-ops/formech](https://github.com/lyw-ops/formech),
reviewed at commit `d0bb1913acc1f710ba6eadf1244b633abbc75fb9`. Its
[README](https://github.com/lyw-ops/formech/blob/d0bb1913acc1f710ba6eadf1244b633abbc75fb9/README.md)
introduces the mathematical model, current file tree, quantified result, concrete examples,
semantic limits and reproducible build commands in that order. The Gaussian guide adopts
these reader-facing ideas; it does not copy mechanism-design assumptions or introduce a DSL.
Formech is a presentation reference, not a mathematical source for Gaussian Poincaré. Its
current Lean files do not provide the per-theorem literature or statement-freeze convention;
those remain KLS's own source and ownership discipline.

The layout follows `Density → Real → solution`, with `LinearTest → Real`. The two existing
definitions and linear-test modules are not modified. General interval glue remains in
`Real.lean` until a stable independent use justifies extracting it. The guide, source audit,
candidate contracts and exact signature output have separate purposes and link to one another.

The new solution entry point contains typed checks only. Its 7 applications check the
standard law, a translated law with variance 4, zero variance for arbitrary mean, and
Mathlib's Dirac identification. A proposition check spells out the intended future certificate
type. A named certificate is deferred until the proof stage, avoiding another duplicate
statement obligation now. The existing default solution target compiles this entry point;
the proved aggregate and accepted certificates do not import the draft Gaussian modules.

## 6. Review and handoff

The primary review and an independent review examined all 20 statement types, including
tails, nonnegative integration regions, weighted integrability, the full test domain and
zero variance. No missing public hypothesis or incorrect coefficient was found. One docstring
was clarified to attribute the `ENNReal` infimum specifically to the local encoding of the
optimal constant in Definition 2.1. The candidate statements were not changed by that edit.

Read the [candidate package](../decisions/2026-09-04-gaussian-poincare-candidate.md) for the
complete declarations and exact ledger snapshot. The [validation record](2026-09-04-gaussian-poincare-validation.md)
records compilation and existing-contract checks. Human review still determines whether
these candidate signatures should be frozen for the separate proof stage.

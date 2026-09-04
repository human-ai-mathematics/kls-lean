# One-dimensional Gaussian Poincaré: proof-route review

Date: 2026-09-03 (Asia/Shanghai).
Repository baseline: `10e4c707491830ebe9d07f7bfc5e65efeddc7e2e`.
Reviewed proposal: `2026-09-03-gaussian-poincare-issue-draft.md`.
Proposal SHA-256: `c1d644617655c500fa5ebe233e9d5cf31aab7093aea1213a3d3bf0eedc2808de`.

## Verdict and limits

**The proposed mathematical route closes under the existing `Poincare.Admissible`
assumptions. No incorrect constant, missing public hypothesis, or circular dependency was
found. No change to the two proposed public statement types is needed.**

The review checked the complete analytic argument, the zero-variance case, sharpness and
the extended-infimum interface. Two independent reviewers checked the upper-bound argument
and the Gaussian/linear-test/optimal-constant correspondence. The primary reviewer inspected
the pinned source APIs and successfully elaborated a temporary Lean API probe.

This is a proof-route and interface review, not a completed Lean proof or a human statement
freeze. The Gaussian calculus and interchange helpers remain implementation work. The
reviewed proposal is unchanged; no GitHub Issue, ledger node, library theorem, certificate,
commit or publication is created by this review.

## 1. Exact claim and source correspondence

The two target propositions are

```lean
Holds (ProbabilityTheory.gaussianReal m v) (v : ℝ)
constant (ProbabilityTheory.gaussianReal m v) = (v : ENNReal)
```

Here `m : ℝ` and `v : NNReal`; `v` is the variance. They use the existing globally smooth,
L², finite-gradient-energy test class and canonical real-line gradient. The manuscript's
positive-definite Gaussian covariance result specializes to the centered, positive-variance
case. Arbitrary means and `v = 0` are correctly identified in the proposal as local
extensions. Neither LSI nor a Sobolev/spectral-gap equivalence is asserted.

The source links and pinned revisions are recorded in the reviewed proposal. Existing
tensorization and linear-test results remain compatible: the present issue supplies the
one-dimensional upper bound, while the linear test supplies sharpness. Multivariate affine
transport is not a dependency of these two targets.

## 2. Upper bound for positive variance

Fix `v > 0`, an admissible function f, and write

$$
p(x)=\frac{1}{\sqrt{2\pi v}}\exp\!\left(-\frac{(x-m)^2}{2v}\right),
\qquad h(t)=|f'(t)|^2.
$$

Smoothness gives continuous f′ and local integrability of f′ and h on every bounded
interval. Finite gradient energy gives integrability of h under the Gaussian law, because
`gradient_eq_deriv'` identifies the real-line gradient with the ordinary derivative.

First, L² membership and probability normalization justify all terms in

$$
\int(f-f(m))^2\,d\gamma
=\operatorname{Var}_\gamma(f)+(\mathbb E_\gamma f-f(m))^2
\ge\operatorname{Var}_\gamma(f).
$$

No equality between f(m) and the expectation is needed. For the inequality itself,
`variance_sub_const` and `variance_le_expectation_sq` can be composed. Although those
Mathlib interfaces only request measurability, the existing L² evidence also guarantees
that the squared integrals used in this argument are finite.

For x > m, finite-interval FTC and Cauchy–Schwarz give

$$
(f(x)-f(m))^2\le(x-m)\int_m^x h(t)\,dt.
$$

The nonnegative integration region is m < t < x. Tonelli and the right tail identity give

$$
\begin{aligned}
\int_m^\infty(f(x)-f(m))^2p(x)\,dx
&\le\int_m^\infty h(t)
   \left[\int_t^\infty(x-m)p(x)\,dx\right]dt\\
&=v\int_m^\infty h(t)p(t)\,dt.
\end{aligned}
$$

For x < m, apply the same finite-interval estimate on [x,m]. The region is x < t < m:

$$
\begin{aligned}
\int_{-\infty}^m(f(x)-f(m))^2p(x)\,dx
&\le\int_{-\infty}^m h(t)
   \left[\int_{-\infty}^t(m-x)p(x)\,dx\right]dt\\
&=v\int_{-\infty}^m h(t)p(t)\,dt.
\end{aligned}
$$

Both weights follow from p′(x) = −(x−m)p(x)/v and p(±∞) = 0:

$$
\int_t^\infty(x-m)p(x)\,dx=vp(t),\qquad
\int_{-\infty}^t(m-x)p(x)\,dx=vp(t).
$$

The first-moment integrability needed by improper FTC is a Gaussian property. It can be
obtained from Gaussian moments and the density bridge; it imposes no additional condition
on f. Only the density is differentiated at infinity. No decay of f, f′ or fp is used.

Adding the two estimates gives the stronger anchored inequality

$$
\int(f-f(m))^2\,d\gamma\le v\int|f'|^2\,d\gamma.
$$

The two half-lines partition the energy, so there is no factor of 2. Their common endpoint
has zero Lebesgue and positive-variance Gaussian measure; at x = m the anchored difference
is itself zero. Combining this with variance minimization proves the proposed upper bound.

## 3. Integrability and implementation obligations

The following are helper obligations, not additional public assumptions:

| Obligation | Evidence or intended interface |
| --- | --- |
| Finite-interval FTC–Cauchy estimate | Global smoothness supplies local C¹ regularity and restricted L² integrability. Use interval FTC and integral Hölder with exponents 2,2. |
| Density derivative, limits and first-moment tails | Work under `v > 0`; combine Gaussian calculus, moment integrability and improper FTC. The two tail identities still need to be assembled. |
| Transfer of integrability to density-weighted Lebesgue integrals | Use `integrable_withDensity_iff_integrable_smul'` or `integrable_withDensity_iff`, with the measurable, finite Gaussian density. |
| Interchange on the two triangular regions | The kernels are nonnegative and jointly measurable. Use `lintegral_lintegral_swap`; compute the inner weights and use finite energy before converting back to real integrals. |
| Joining the half-lines | Use disjoint half-lines or discard their null endpoint. The total right-hand side is exactly v times the energy. |

Two details require care when implementing this route:

- Equality of real integrals alone does not prove integrability in Lean. In particular,
  `integral_gaussianReal_eq_integral_smul` must be accompanied by the separate integrability
  transfer. The available `withDensity` iff provides that transfer.
- Do not introduce a global Lebesgue L² condition on f′. The FTC–Cauchy step only needs
  finite-interval integrability. The admissible test f(x) = x has derivative 1, which is
  not in L² of Lebesgue measure on the whole real line.

## 4. Zero variance and optimality

For `v = 0`, `gaussianReal_zero_var` identifies the law with `Measure.dirac m`, and
`variance_dirac` makes every test variance zero. Thus `Holds … 0` follows directly.
The ambient space remains ℝ; no subsingleton-space argument is used.

For every `v ≥ 0`, `memLp_id_gaussianReal` and the existing linear-test admissibility API
make the identity an admissible test. `variance_id_gaussianReal` gives variance v, and
`energy_linearTest` at the real vector 1 gives energy 1. This includes the Dirac case:
the identity still has derivative 1, even though its variance under that law is zero.

Consequently every finite valid constant C satisfies v ≤ C. Existing `le_constant`
converts this universal lower bound to `(v : ENNReal) ≤ constant …`; `constant_le`
applied to the new upper bound gives the reverse inequality. This proves equality without
assuming that the infimum is attained or invoking a multivariate covariance theorem.

## 5. Lean verification actually performed

Using the project's pinned Lean/Mathlib v4.33.0, a temporary file outside the repository
was checked with `lake env lean`. It imported `Poincare.LinearTest`, Gaussian `Real`,
interval-integral `ContDiff`, and `IntegralEqImproper`. All 24 `#check` items passed,
and the process exited with code 0:

- both proposed target proposition types;
- typed Gaussian probability, identity L² membership, identity variance and linear-test
  energy applications, for arbitrary m and v without a positive-variance premise;
- variance shift, variance-versus-second-moment, and Dirac variance interfaces;
- the Gaussian zero-variance, density-integral and density-integrability interfaces;
- the gradient/derivative identity, finite-interval FTC, integral Hölder, and both improper
  FTC interfaces;
- nonnegative Tonelli and both named `withDensity` integrability iff interfaces;
- linear-test admissibility, its fixed-constant variance bound, and the two optimal-constant
  order interfaces.

This validates the candidate types and the availability of the named APIs. It does not
certify the Gaussian upper-bound proof, the assembled helper lemmas, or a future ledger
certificate. No new proof placeholder or axiom was introduced. The next preparation step
remains the issue's proposed statement/helper audit and human statement review.

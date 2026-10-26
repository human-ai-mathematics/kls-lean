# kls-lean

A Lean 4 library for **Poincaré inequalities, log-concave measures and stochastic
localization**. It develops reusable analysis and probability tools around published
literature, with the dimension-free Kannan–Lovász–Simonovits (KLS) bound as a main application.

[Getting started](examples/FIRST-USE.md) · [Examples](examples/README.md) · [API](formalization/API.md) · [Proof path](research/progress/PROOF-PATH.md) · [Verification](research/verification.md)

**Toolchain:** Lean and Mathlib **v4.33.0**.

## Use the library

| I want to… | Start here |
| --- | --- |
| Apply KLS to a variance bound or Gaussian convolution | [KLS applications](examples/KlsApplications.lean) |
| Combine Gaussian/product laws and transport covariance | [Finite products and covariance](examples/FiniteProductCovariance.lean) |
| Compare energy and test-function interfaces | [Poincaré foundations](examples/PoincareFoundation.lean) |
| Work with metric perimeter or matrix trace estimates | [Metric BV](examples/MetricBV.lean) · [Matrix integrals](examples/MatrixIntegral.lean) |

Further tools cover one-dimensional log-concave bounds, coarea/Sard, Cheeger–Buser
comparisons, Bakry–Émery calculus and finite-horizon cutoff localization.
[Library design](LEAN_DESIGN.md) explains the mathematical layers and the hypotheses
needed when changing energy or test class.

## What is proved

There is **one finite constant**, independent of dimension and law, such that every
finite-dimensional log-concave probability law μ with finite second moment satisfies

```math
C_{\mathrm P}^{\mathrm{lit}}(\mu)
\le C\,\|\operatorname{Cov}_{\mu}\|_{\mathrm{op}}.
```

The constant on the left is the intrinsic local-slope Poincaré constant.
**Dimension zero and singular affine supports are included.** The Lean endpoint is
[`KLS.kls`](formalization/FunctionalInequalities/KLS/Target.lean), proving
[`KLS.Conjecture`](formalization/FunctionalInequalities/KLS/Statement.lean).

The proof follows **Bizeul–Klartag–Lehec, arXiv:2610.05474v1**, using the compact
Letwin constant-8 bound and finite-horizon cutoff localization. The
[proof path](research/progress/PROOF-PATH.md) maps the source steps to Lean declarations
and certificates.

Also formalized:

- **The exact OpenAI statement**, through the separate [bridge package](integrations/openai/README.md).
- **[Letwin Theorem 1.2](formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean)**
  with exact constant **8**, for every positive-dimensional isotropic log-concave law
  and every self-adjoint quadratic form, without compact support.
- **[Letwin Lemma A.1](formalization/FunctionalInequalities/KLS/Letwin/Approximation.lean)**:
  regular approximation preserving exact isotropy, with convergence of mixed moments
  of degree at most four.

## Limits

- **No explicit numerical KLS constant is extracted.** Letwin's constant 8 bounds
  quadratic-form variance; it is separate from the final KLS constant.
- **Letwin's original proof of Theorem 1.1 remains incomplete locally.** Its conclusion
  is implied by the stronger BKL bound. Full moment-map regularity in Lemma 2.2 for
  the paper's merely convex source class also remains incomplete. See the
  [smooth-route gap map](research/progress/letwin-smooth-route.json).
- **The uncut Eldan construction remains unformalized**, including strong solution,
  uniqueness, non-explosion and the literal stochastic identities (68)–(73).
  The proved KLS route uses finite-horizon cutoff localization.

The [literature register](research/progress/LITERATURE.md) records exact hypotheses,
supporting results and paper coverage. The four [exploratory routes](research/progress/README.md#proof-progress-tree)
are historical research records with their own open hypotheses and local proof statuses.

## Related formalizations

The table compares public theorem endpoints at versions checked on **2026-10-20**.
On narrow screens, scroll the table horizontally.

| | kls-lean | [KLS500](https://github.com/HongruZhao/KLS500/tree/c1a50992a81456849996deef2971d4a0b3190bdd) | [KLS15](https://github.com/HongruZhao/KLS15/tree/fe59199e9c039a79a436daa939f79662df2596da) |
| --- | --- | --- | --- |
| Poincaré bound | Finite universal constant; no numerical value | ≤ 500; also a Cheeger bound | ≤ 15 |
| Main endpoint scope | Covariance-normalized; all `n ≥ 0`, including singular affine supports | Isotropic log-concave laws, `n ≥ 1` | Isotropic log-concave laws, `n ≥ 1` |
| Exact OpenAI statement | [Proved](integrations/openai/README.md) | Proved | Proved |
| Main proof source | BKL, finite-horizon cutoff route | BKL and Song–Zhang | Balasubramanian–Kasiviswanathan v2 |
| Comparator | Linux sandbox pass reported | Not run | Not run |

Comparator entries follow the pinned verification notes and reports. The reported
kls-lean pass covers `2639e79`; the final release still needs a rerun.
[Pinned comparison details](research/progress/formalization-comparison.md) record sources,
shared dependencies and verification scope. KLS15 continues KLS500.

## Build and verify

Install Git, Python 3 and [Elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/human-ai-mathematics/kls-lean.git
cd kls-lean
python3 research/cache_mathlib.py
(cd formalization && lake build)
```

Private checkouts require GitHub read access. To use the library in another Lean
project, follow the [separate-project walkthrough](examples/FIRST-USE.md).

For **full local verification**, run `python3 research/verify.py`. This builds sources,
checks statements and metadata, audits local declarations and replays local modules.
Pinned third-party compiled imports remain trusted. The OpenAI bridge has
[separate build and audit instructions](integrations/openai/README.md); prepare both
packages' caches with `python3 research/cache_mathlib.py --project all`.

Receipts certify their recorded source snapshot. The [verification guide](research/verification.md#receipts-and-trust-scope)
explains the scope of full local checks, remote Lean certification and Comparator runs.
Earlier receipts do not certify later changes.

## Where to look

- **Follow the mathematics:** [literature register](research/progress/LITERATURE.md) and [progress diagrams](research/progress/README.md).
- **Contribute or review:** [contributing guide](CONTRIBUTING.md), [human-review checklist](research/progress/public-interface-review.md#focused-maintainer-checklist) and [maintainer index](research/README.md).
- **Audit or cite:** [Comparator setup](research/audits/KLS/Comparator/README.md), [citation metadata](CITATION.cff) and [provenance metadata](formalization.yaml).

## License and credit

Project-owned code uses [Apache-2.0](LICENSE). [Vendored libraries](formalization/vendor/README.md)
retain their licenses and notices. The project builds on Mathlib and other pinned packages;
its early foundational work and proof development started from the roadmap organized by
Nicolas ([nbrosse](https://github.com/nbrosse)).

AI involvement is substantial: ChatGPT helped organize literature and proof approaches,
and Claude and GPT participated in review passes. The maintainer has reviewed key
mathematical statements; no external human peer review is claimed. See the
[provenance metadata](formalization.yaml).

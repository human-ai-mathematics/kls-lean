# kls-lean

Lean 4 formalization of the dimension-free Kannan–Lovász–Simonovits (KLS) bound,
following the proof of Bizeul, Klartag, and Lehec.

[Getting started](examples/FIRST-USE.md) · [Examples](examples/README.md) · [API](formalization/API.md) · [Proof path](research/progress/PROOF-PATH.md) · [Verification](research/verification.md)

**Toolchain:** Lean and Mathlib **v4.35.0**; library, vendor, solution, example and audit sources use Lean `module` headers.
**Palomar:** the contained [submission project](integrations/palomar/README.md) compares the
pinned OpenAI form of the dimension-free bound and its locally Lipschitz `L²` extension.
[Registered version 2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-01-000014&version=2)
covers both statements at source commit `e60bc39b18ef691263c66e2dba8d64726f18060d`.
The submission guide records their scope and verification evidence.

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

- **The exact OpenAI statement**, through the separate [bridge package](integrations/openai/README.md),
  and its extension to every locally Lipschitz `L²` test (a density-coordinate formulation of
  BKL Theorem 1.1, with possibly infinite gradient energy).
- **[Letwin Theorem 1.2](formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean)**
  with exact constant **8**, for every positive-dimensional isotropic log-concave law
  and every self-adjoint quadratic form, without compact support;
  [source-form certificate](solutions/ThmLetwinQuadraticBound.lean).
- **[Letwin Theorem 1.1](solutions/ThmLetwinIsoperimetricBound.lean)**:
  the logarithmic-quarter bound for n ≥ 2, certified through the stronger BKL result.
- **[Letwin Lemma A.1](formalization/FunctionalInequalities/KLS/Letwin/Approximation.lean)**:
  regular approximation preserving exact isotropy, with convergence of mixed moments
  of degree at most four.
- **[Letwin Lemma 2.2 and Theorem 2.5](formalization/FunctionalInequalities/KLS/Letwin/MomentMap.lean)**
  for the paper's merely convex source class, at every moment potential: the moment map
  is smooth with the stated properties and satisfies the trace bound with exact constant
  **2**; Lemmas 2.3, 2.4, 2.7, 2.9 and A.4–A.6 hold at the same potential.
- **[Cordero-Erausquin–Klartag Theorem 2](formalization/FunctionalInequalities/KLS/CEK/Uniqueness.lean)**
  (Letwin Lemma 2.1): existence of essentially continuous moment potentials and their
  uniqueness up to translation.
- **[Letwin Proposition 2.8](formalization/FunctionalInequalities/KLS/Letwin/HminusOne.lean)**
  for every full-dimensional log-concave law, and the Section 1 constants with the
  [Cheeger–Buser ratio](formalization/FunctionalInequalities/KLS/Letwin/IsoperimetricBound.lean)
  1/4 ≤ ψ²/C_P ≤ π in every positive dimension.

## Limits

- **No explicit numerical KLS constant is extracted.** Letwin's constant 8 bounds
  quadratic-form variance; it is separate from the final KLS constant.
- **Letwin's original proof of Theorem 1.1 remains incomplete locally.** Its conclusion
  is implied by the stronger BKL bound.
- **Letwin coverage is its certified main-theorem conclusion**, through the BKL alternative
  route; Proposition 2.8 retains its full-dimensional restriction. Cordero-Erausquin–Klartag
  has no paper-target certificate. The [smooth-route map](research/progress/letwin-smooth-route.json)
  records the moment-map results and remaining auxiliary gaps.
- **The uncut Eldan construction remains unformalized**, including strong solution,
  uniqueness, non-explosion and the literal stochastic identities (68)–(73).
  The proved KLS route uses finite-horizon cutoff localization.

The [literature register](research/progress/LITERATURE.md) records exact hypotheses,
supporting results and paper coverage. The four [exploratory routes](research/progress/README.md#proof-progress-tree)
are historical research records with their own open hypotheses and local proof statuses.

## Build and verify

Install Git, Python 3 and [Elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/human-ai-mathematics/kls-lean.git
cd kls-lean
python3 research/cache_mathlib.py
(cd formalization && lake build)
```

The public repository supports anonymous HTTPS cloning. To use the library in another
Lean project, follow the [separate-project walkthrough](examples/FIRST-USE.md).

For **full local verification**, install the
[validation dependencies](research/verification.md#verification-commands) and run
`python3 research/verify.py`. This builds sources,
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

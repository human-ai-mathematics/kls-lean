# kls-lean

kls-lean is a Lean 4 library for functional inequalities, with reusable analysis,
probability, energy and Poincaré interfaces developed around published literature on
the Kannan–Lovász–Simonovits (KLS) conjecture. Lean and Mathlib are pinned to **v4.33.0**.

## Use the library

The library provides:

- Gaussian and one-dimensional log-concave Poincaré bounds, finite tensorization
  and convolution bounds;
- covariance and affine transport, distinct energy and test-function interfaces,
  and proved comparisons between them;
- coarea/Sard, Cheeger–Buser comparisons, metric BV/Minkowski recovery and the
  selected Bakry–Émery bound.

Start with the [calling examples](examples/README.md) and
[separate-project walkthrough](examples/FIRST-USE.md). The
[KLS application client](examples/KlsApplications.lean) obtains a variance bound
and composes it with Gaussian convolution. Use the [API directory](formalization/API.md)
for signatures and imports, and [library design](LEAN_DESIGN.md) for mathematical layers
and the hypotheses needed when changing energy or test class.

## KLS result

`KLS.Conjecture` asks for one finite constant `C` such that
`C_P^lit(μ) ≤ C ‖Cov_μ‖_op` for every log-concave probability law with finite second moment
in every finite-dimensional Euclidean space, including dimension zero and singular affine
supports. `C_P^lit` is the intrinsic local-slope Poincaré constant.
**[`KLS.kls`](formalization/FunctionalInequalities/KLS/Target.lean) proves this
[statement](formalization/FunctionalInequalities/KLS/Statement.lean).**
The proof follows Bizeul–Klartag–Lehec (arXiv:2610.05474v1): the compact Letwin bound
and finite-horizon cutoff localization yield the source-form Theorems 4.1 and 1.1,
followed by the affine/isotropic reduction. The [proof path](research/progress/PROOF-PATH.md)
maps the source steps to Lean declarations and certificates.

Letwin's Theorem 1.2 is also formalized for every positive-dimensional isotropic
log-concave law, with exact constant 8, in the separate
[noncompact result](formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean).
Letwin's Lemma A.1 (regular approximation, mixed moments of degree at most four) is formalized in
[KLS/Letwin/Approximation.lean](formalization/FunctionalInequalities/KLS/Letwin/Approximation.lean).
For the strong regular class, a weak target Stein kernel (Lemma 2.7 counterpart: μ-a.e. positive definite,
∫|τ|²_HS ≤ 2n) is formalized in
[MomentRegularity/TraceStein.lean](formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/TraceStein.lean).
The directional weak subsolution of the weak Hessian evolution, with compact-local coefficient bounds, is formalized at
the same witness in
[MomentRegularity/WeakHessian.lean](formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean).
Nonlinear weak H¹ test tools, the Caccioppoli inequality for bounded weak supersolutions, weak Sobolev bounds
(n > 2 critical; n = 2 every finite q ≥ 2; n = 1 essential L^∞) and the Moser inputs (log and power energies, uniform
cutoffs, the L^p → L^∞ limit), the Morrey/critical-potential inputs (all-ball Morrey bounds, critical-potential
exponential integrability) and the local bounded Moser inputs (energies needing nonnegativity only on the cutoff support,
buffered Morrey, one-step gains), bounded weak John–Nirenberg with fixed-compact joint inputs and the bounded actual weak
Harnack inequality (Moser iteration, essential infimum; n > 2 for 0 < p < n/(n−2), n = 1, 2 for every finite p > 0), its
given-data form with the application at one regular potential, the GT 17.13 fixed rank-one frame, the GT 8.23 scalar
iteration and the essential deficit identity are formalized as supports. At the same regular moment potential,
`exists_regular_moment_potential_holder_hessian` in
[MomentRegularity/HessianHolder.lean](formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/HessianHolder.lean)
proves that u is C² with a locally Hölder Hessian and satisfies the log-determinant equation with positive definite Hessian at
every point (strong class; frame oscillation decay by the rough-divergence form of GT 17.14); for the same u,
[MomentRegularity/Inverse.lean](formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Inverse.lean) adds a homeomorphism
∇u : ℝⁿ → int K with a C¹ inverse. Weak Harnack for unbounded data and Schauder/C^∞ regularity are not formalized.
The [paper register](research/progress/LITERATURE.md#when-a-paper-is-covered) records exact
hypotheses, constants, dimensions and paper coverage.

## Limits

- **No explicit numerical KLS constant is extracted.** The final theorem gives one
  finite universal constant; Letwin's constant 8 is a separate bound.
- **Letwin's Theorem 1.1 and the smooth moment map of Lemma 2.2 remain unformalized in this
  library.** The [smooth-route gap map](research/progress/letwin-smooth-route.json) lists the missing
  regularity tools (Caffarelli and W^{2,p} for the source class, Schauder for C^∞); strong-class C^{2,α} and a C¹ gradient
  inverse onto int K at the regular moment potential are proved.
- **The uncut Eldan construction remains unformalized**, including strong solution,
  uniqueness, non-explosion and the literal stochastic identities (68)–(73).
  The proved KLS route uses finite-horizon cutoff localization.

The four [exploratory routes](research/progress/README.md#proof-progress-tree) are
historical research records with their own open hypotheses and local proof statuses;
they are not current formalization targets.

## Related formalizations

Source comparison checked on 2026-10-20; third-party columns describe their pinned public endpoints.

| | kls-lean | [KLS500](https://github.com/HongruZhao/KLS500/tree/c1a50992a81456849996deef2971d4a0b3190bdd) | [KLS15](https://github.com/HongruZhao/KLS15/tree/fe59199e9c039a79a436daa939f79662df2596da) |
| --- | --- | --- | --- |
| Poincaré bound | One finite universal constant; no explicit numerical value | At most 500; also a Cheeger bound | At most 15 |
| Main endpoint scope | Covariance-normalized; all `n ≥ 0`, including singular affine supports | Isotropic log-concave laws, `n ≥ 1` | Isotropic log-concave laws, `n ≥ 1` |
| Exact OpenAI statement | [Proved in the bridge package](integrations/openai/README.md) | `KLS500.openaiKLS` | `KLS15.openaiKLS` |
| Main proof source | BKL, finite-horizon cutoff route | BKL and Song–Zhang | Balasubramanian–Kasiviswanathan v2 |
| Comparator | macOS development checks passed; Linux sandbox pass reported, receipts pending | Not run, per verification notes | Not run, per verification notes |

[Pinned source details](research/progress/formalization-comparison.md) distinguish endpoint scope,
shared dependencies and verification modes. KLS15 continues KLS500; this table makes no priority claim.

## Where to look

| Entry | Contents |
| --- | --- |
| [Literature register](research/progress/LITERATURE.md) | Exact source statements, full lemma maps and certificates |
| [OpenAI statement bridge](integrations/openai/README.md) | Separate Lean package proving the exact pinned OpenAI statement |
| [Verification guide](research/verification.md) | Checks, receipts and trust scope |
| [Contributing](CONTRIBUTING.md) | Changes, reviews and reuse |
| [Citation metadata](CITATION.cff) · [Formalization metadata](formalization.yaml) | Credit, sources, AI involvement and review scope |

For current work and repository operations, use the [maintainer index](research/README.md).

## Build and verify

Prerequisites: Git, Python 3 and [Elan](https://github.com/leanprover/elan), which installs the
pinned Lean. While the repository is private, cloning needs GitHub read access. Stay at the root:

```bash
git clone https://github.com/human-ai-mathematics/kls-lean.git
cd kls-lean
python3 research/cache_mathlib.py
(cd formalization && lake build)
```

For full verification, use these root commands in place of the plain build:

```bash
python3 research/check_ledger.py
python3 research/verify.py
```

Full local verification builds sources, strictly compiles audit clients, audits every local
declaration, replays local modules and checks statements/metadata. Remote certification runs
the Lean build and strict declaration, vendor and
[classical KLS audits](research/audits/KLS/Classical/README.md), with only `propext`,
`Classical.choice` and `Quot.sound` permitted and no upstream-hole exception in the selected
[vendor closure](formalization/vendor/README.md#upstream-holes). It runs by manual dispatch
or a `milestone/**` tag and excludes local-module replay and metadata/Python checks.
See [receipt scope](research/verification.md#receipts-and-trust-scope). The recorded
[run 39228796618](https://github.com/human-ai-mathematics/kls-lean/actions/runs/39228796618)
passed for `845e61b` (9,856 local declarations audited, `KLS.kls` included) and does not certify
later commits.

The separate [Comparator setup](research/audits/KLS/Comparator/README.md) checks the KLS
statement and proof closure, with explicit modes for macOS development and Linux sandbox runs.
The [public-interface review](research/progress/public-interface-review.md) records the current
statement checks and the specific items still awaiting maintainer review.

## License and credit

Project-owned code uses [Apache-2.0](LICENSE); [vendored libraries](formalization/vendor/README.md)
retain their licenses and notices. The project builds on Mathlib and the other pinned packages.
The project initially followed the roadmap organized by Nicolas ([nbrosse](https://github.com/nbrosse));
its early foundational work and proof development started from that roadmap.
ChatGPT helped organize literature and proof approaches. AI involvement is substantial,
and Claude and GPT participated in separate review passes. The maintainer has reviewed
key mathematical statements; no external human peer review is claimed
(see [receipts and trust scope](research/verification.md#receipts-and-trust-scope)).

# kls-lean

Lean formalization of functional inequalities and published literature around the
Kannan–Lovász–Simonovits (KLS) conjecture. Lean and Mathlib are pinned to **v4.33.0**.

## Statement

`KLS.Conjecture` asks for one finite constant `C` such that
`C_P^lit(μ) ≤ C ‖Cov_μ‖_op` for every log-concave probability law with finite second moment
in every finite-dimensional Euclidean space. `C_P^lit` is the intrinsic local-slope
Poincaré constant. See the [statement](formalization/FunctionalInequalities/KLS/Statement.lean)
and [target theorem](formalization/FunctionalInequalities/KLS/Target.lean).
**`KLS.kls` proves it** through Bizeul–Klartag–Lehec Theorem 1.1 (arXiv:2610.05474v1) on the
finite-horizon cutoff stochastic-localization route. The [verification guide](research/verification.md#receipts-and-trust-scope) explains
snapshot-bound build, axiom-audit and kernel-replay evidence.

## What is proved

The certified library includes Gaussian and one-dimensional log-concave Poincaré bounds,
finite tensorization, coarea/Sard, energy identification, Cheeger–Buser comparisons,
metric BV/Minkowski recovery and the selected Bakry–Émery bound.
The four-stage main line to KLS is formalized:

1. Letwin's Theorem 1.2 for compactly supported isotropic log-concave laws with the exact
   constant 8 (`thm:letwin-compact-quadratic-bound`);
2. BKL (95) in finite-horizon cutoff form (`lem:bkl-cutoff-energy`), on the cutoff
   stochastic-localization route rather than the uncut Eldan process;
3. BKL Theorem 4.1 in source form (`thm:bkl-cumulant-bound`: one universal K, every m ≥ 2,
   every dimension and isotropic log-concave law);
4. BKL Theorem 1.1 in source form (`thm:bkl-poincare`), with Theorem 3.1, Proposition 7.1
   and regular approximation, and `KLS.kls` through the affine/isotropic reduction.

The [proof path](research/progress/PROOF-PATH.md) maps each source step and proof device to its
Lean entry. The separate [noncompact Letwin bound](formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean)
also proves Theorem 1.2 for every positive-dimensional isotropic log-concave law, with constant 8.
The [paper register](research/progress/LITERATURE.md#when-a-paper-is-covered) owns exact
hypotheses, constants, dimensions, paper coverage and certificates.

## What is not proved

Letwin's Theorem 1.1 and full smooth regular approximation (Lemma A.1), BKL's uncut Eldan process (strong solution,
uniqueness, non-explosion) with the literal stochastic identities (68)–(73), and the four
exploratory KLS routes are not proved; the cutoff route does not need them. The declaration
audit covers every project-local declaration, `KLS.kls` included. The separately audited
[vendored stochastic calculus](formalization/vendor/README.md#upstream-holes) contains
known upstream holes; no project-local proved declaration may depend on them.

## Where to look

| Where to look | Entry | Contents |
| --- | --- | --- |
| **Read the mathematics** | [Proof path](research/progress/PROOF-PATH.md) | Main chain, source steps and Lean entries |
| | [Literature register](research/progress/LITERATURE.md) | Exact source statements, full lemma maps and paper coverage |
| | [Lean design](LEAN_DESIGN.md) | Mathematical layers and current interfaces |
| | [Calling examples](examples/README.md) | Narrow imports and checked clients |
| **Build, verify, contribute** | [Verification guide](research/verification.md) | Local checks, receipts and remote scope |
| | [Contributing](CONTRIBUTING.md) | Changes, reviews and reuse |
| | [Citation metadata](CITATION.cff) | Credit and revision information |

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

The verifier builds sources, strictly compiles audit clients, audits every local declaration,
replays local modules and checks statements/metadata, including the
[Mathlib-only classical KLS formulations](research/audits/KLS/Classical/README.md).
Remote certification checks the Lean build, strict audit clients, every local declaration
against only `propext`, `Classical.choice` and `Quot.sound`, and the vendor/classical KLS gates,
by manual dispatch or a `milestone/**` tag. See [receipt scope](research/verification.md#receipts-and-trust-scope)
for full local kernel replay evidence. The latest
[run 39228796618](https://github.com/human-ai-mathematics/kls-lean/actions/runs/39228796618)
passed for `845e61b` (9,856 local declarations audited, `KLS.kls` included) and does not certify
later commits.

## License and credit

Project-owned code uses [Apache-2.0](LICENSE); [vendored libraries](formalization/vendor/README.md)
retain their licenses and notices. The project builds on Mathlib and the other pinned packages.
Development and review used AI coding agents; no external human peer review is claimed
(see [receipts and trust scope](research/verification.md#receipts-and-trust-scope)).

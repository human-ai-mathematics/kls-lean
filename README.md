# kls-lean

Lean formalization of functional inequalities and published literature around the
Kannan–Lovász–Simonovits (KLS) conjecture. Lean and Mathlib are pinned to **v4.33.0**.

## Statement

`KLS.Conjecture` asks for one finite constant `C` such that
`C_P^lit(μ) ≤ C ‖Cov_μ‖_op` for every log-concave probability law with finite second moment
in every finite-dimensional Euclidean space. `C_P^lit` is the intrinsic local-slope
Poincaré constant. See the [statement](formalization/FunctionalInequalities/KLS/Statement.lean)
and [open target](formalization/FunctionalInequalities/KLS/Target.lean).
**Dimension-free KLS remains open.**

## What is proved

The certified library includes one-dimensional log-concave and Gaussian Poincaré bounds,
finite tensorization, coarea and Sard infrastructure, canonical energy identification,
Cheeger–Buser comparisons, metric BV/Minkowski recovery, and the selected Bakry–Émery bound.
BKL Theorem 3.1 and Proposition 7.1 have source-form certificates; Proposition 7.1 retains
its universal cumulant hypothesis. The regular approximation and final BKL assembly are
formalized; BKL Theorem 4.1 is formalized through a cutoff Eldan-localization route, and with it
`KLS.Conjecture` (`conjecture_of_letwinCompact`), conditionally on one open input: Letwin's
Theorem 1.2 for compactly supported isotropic log-concave laws (`LetwinCompactBound`).
That compact bound is reduced to the smooth uniformly convex regular class. Weak
Hessian symmetry and convex-range mollification are proved supports. The weak regular
moment-potential package now supplies C1, a 16/kappa-Lipschitz gradient and a.e.
Hessian/log-det data, the weak C^{1,1} inverse-Hessian generator identities (Letwin (2.2)) and the
integrated Hessian-increment energy estimate are proved supports; the regular-class constant-8 bound
remains open.

The [paper register](research/progress/LITERATURE.md) owns exact hypotheses, constants,
dimensions, selected paper coverage and certificates. The
[BKL main proof chain](research/progress/README.md#bkl-main-proof-chain) locates the current
entries and missing inputs. Supporting results and conditional reductions do not cover a paper.

## What is not proved

BKL Theorems 1.1 and 4.1 without hypotheses, Letwin Theorem 1.2 (the `LetwinCompactBound` input)
and the project's dimension-free KLS target remain open. The current goal is that compact constant-8
input, `LetwinCompactBound` (see [HANDOFF](HANDOFF.md)). `KLS.kls` is the intentional
project-local hole, outside certificate closures. The separately audited
[vendored stochastic calculus](formalization/vendor/README.md#upstream-holes) contains
known upstream holes; no project-local proved declaration may depend on them.

## Where to look

| Entry | Contents |
| --- | --- |
| [Proof path](research/progress/PROOF-PATH.md) | Four-stage main line to KLS through BKL, with exact inputs |
| [Literature register](research/progress/LITERATURE.md) | Primary paper-by-paper scope and coverage |
| [Progress hub](research/progress/README.md) · [Node register](research/progress/STATUS.md) | BKL navigation, complete diagrams and generated status |
| [Current handoff](HANDOFF.md) | Current controller, scope, snapshot evidence and next step |
| [Formalization guide](formalization/README.md) · [Blueprint](formalization/blueprint/README.md) | Library layout, builds and mathematical reading order |
| [Certificates](solutions/README.md) · [Ledger](research/a-series/ledger.yaml) | Lean certificate entry points and registrations |
| [Workflow](research/workflow.md) · [Verification](research/verification.md) | Placement, checks, receipts and CI policy |
| [Decision records](research/decisions/README.md) | Dated history and archived guides |

## Verify

From the repository root:

```bash
python3 research/check_ledger.py
python3 research/verify.py
```

The full local verifier builds, strictly checks audit clients, audits transitive axioms,
replays local modules and checks statement baselines and metadata. To check generated views,
use `python3 research/progress/update.py --check` with the same canonical Git index used to
produce them; see the [generation procedure](research/verification.md#progress-generation).
Remote certification runs only the Lean scope, by manual dispatch or a `milestone/**` tag.
[Run 37516844384](https://github.com/human-ai-mathematics/kls-lean/actions/runs/37516844384)
passed for `36e7c78`; it does not certify later work or prove KLS.

Earlier detailed status wording is preserved in the
[2026-10-12 root-guide archive](research/decisions/2026-10-12-root-guide-history.md).

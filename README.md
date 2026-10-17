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
owner-selected cutoff stochastic-localization route. The integrated proof snapshot passed full local verification and independent acceptance;
[HANDOFF](HANDOFF.md) links the recorded evidence and its scope.

## What is proved

The certified library includes one-dimensional log-concave and Gaussian Poincaré bounds,
finite tensorization, coarea and Sard infrastructure, canonical energy identification,
Cheeger–Buser comparisons, metric BV/Minkowski recovery, and the selected Bakry–Émery bound.
The four-stage main line to KLS is formalized:

1. Letwin's Theorem 1.2 for compactly supported isotropic log-concave laws with the exact
   constant 8 (`thm:letwin-compact-quadratic-bound`), through the actual regular-class moment
   potential, the Gaussian product coupling, the H⁻¹ inequality, a spectral noise identity and
   the singular extension (Lemma A.2);
2. BKL (95) in finite-horizon cutoff form (`lem:bkl-cutoff-energy`), on the owner-selected
   cutoff stochastic-localization route;
3. BKL Theorem 4.1 in source form (`thm:bkl-cumulant-bound`: one universal K, every m ≥ 2,
   every isotropic log-concave law);
4. BKL Theorem 1.1 in source form (`thm:bkl-poincare`), with the certified Theorem 3.1,
   Proposition 7.1 and the regular approximation, and `KLS.kls` through the affine/isotropic
   reduction.

The [proof path](research/progress/PROOF-PATH.md) maps each source step to its Lean entry.
The [paper register](research/progress/LITERATURE.md) owns exact hypotheses, constants,
dimensions, selected paper coverage and certificates. The
[BKL main proof chain](research/progress/README.md#bkl-main-proof-chain) locates the entries
and certificates. Supporting results and conditional reductions do not cover a paper.

## What is not proved

Letwin's noncompact Theorem 1.2 and Theorem 1.1, BKL's uncut Eldan process (strong solution,
uniqueness, non-explosion) with the literal stochastic identities (68)–(73), and the four
exploratory KLS routes are not proved; the selected route does not need them. The declaration
audit covers every project-local declaration, `KLS.kls` included. The separately audited
[vendored stochastic calculus](formalization/vendor/README.md#upstream-holes) contains
known upstream holes; no project-local proved declaration may depend on them.

## Where to look

| Entry | Contents |
| --- | --- |
| [Proof path](research/progress/PROOF-PATH.md) | Four-stage main line to KLS through BKL, with exact inputs |
| [Literature register](research/progress/LITERATURE.md) | Primary paper-by-paper scope and coverage |
| [Progress hub](research/progress/README.md) · [Node register](research/progress/STATUS.md) | BKL navigation, complete diagrams and generated status |
| [Current handoff](HANDOFF.md) | Current controller, scope, snapshot evidence and next step |
| [Lean design](LEAN_DESIGN.md) · [Calling examples](examples/README.md) | Current interfaces, mathematical layers and narrow imports |
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
replays local modules and checks statement baselines and metadata. Its `classical-kls` gate compiles
independent [Mathlib-only classical KLS formulations](research/audits/KLS/Classical/README.md) and their proof from `KLS.kls`. To check generated views,
use `python3 research/progress/update.py --check` with the same canonical Git index used to
produce them; see the [generation procedure](research/verification.md#progress-generation).
Remote certification runs only the Lean scope, by manual dispatch or a `milestone/**` tag.
[Run 37516844384](https://github.com/human-ai-mathematics/kls-lean/actions/runs/37516844384)
passed for `36e7c78`; it does not certify later work.

## License

Project-owned code is licensed under the [Apache License 2.0](LICENSE). The vendored libraries under
`formalization/vendor/` keep their own licenses, notices and copyright lines.

Earlier detailed status wording is preserved in the
[2026-10-12 root-guide archive](research/decisions/2026-10-12-root-guide-history.md).

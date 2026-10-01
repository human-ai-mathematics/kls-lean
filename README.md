# kls-lean

Lean formalization of functional inequalities and the published literature around the
Kannan–Lovász–Simonovits conjecture. Work is selected by source paper and target theorem. Lean and Mathlib are pinned to **v4.33.0**.

## Statement

The covariance-normalized KLS target asks for a finite universal constant `C` such that
`C_P^lit(μ) ≤ C ‖Cov_μ‖_op` for every finite-dimensional log-concave probability law with
finite second moment. See the [Lean statement](formalization/FunctionalInequalities/KLS/Statement.lean)
and [open target](formalization/FunctionalInequalities/KLS/Target.lean).
**Dimension-free KLS remains open.** The target theorem contains the library's one intentional
`sorry`; it lies outside every certificate import closure.

## Current status (2026-10-02)

There are **26 registered Lean certificates**, with additional proved auxiliary results.
Selected completed results include the one-dimensional `4 Var` Poincaré upper bound,
finite tensorization and Gaussian constants, weighted coarea and sharp scalar Sard,
and the numerical Cheeger–Buser comparisons `C_P^lit ≤ 4 Ψ²` and `Ψ² ≤ π C_P^lit`
for every finite-dimensional log-concave law, including degenerate affine supports.

Metric BV recovery now gives ADMG Theorem 3.6's relaxed Minkowski/perimeter identities
at finite-mass Borel targets for measures finite on bounded Borel sets. These are equalities
of relaxation infima. General RCD comparisons and the literature's high-dimensional KLS
bounds remain unformalized. Supporting tools and conditional reductions do not certify a paper.

| Entry | Contents |
| --- | --- |
| [Literature register](research/progress/LITERATURE.md) | Paper versions, target theorems, Lean statements, certificates and remaining scope |
| [Progress hub](research/progress/README.md) | Literature map, current paper priorities and maintenance workflow |
| [Node register](research/progress/STATUS.md) | Current Blueprint statements and certificate mappings |
| [Current handoff](HANDOFF.md) | Verified baseline and current work |
| [Formalization guide](formalization/README.md) | Library layout, Lean builds and local Blueprint builds |
| [Workflow](research/workflow.md) · [Naming](research/naming.md) | Verification and public API rules |

## Verify

From the repository root:

```sh
cd formalization
lake build
cd ..
python3 research/check_ledger.py
python3 research/verify.py
python3 research/progress/update.py --check
```

The full local verifier checks proofs, independent audit clients, axioms, kernel replay,
statement baselines and metadata. Remote CI runs the Lean-only scope by manual dispatch
or `milestone/**` tags. Ordinary pushes and PR updates do not trigger CI.

[Lean certification run 36846629874](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/36846629874)
passed for commit `6ca1824f18e81b7409fd6e5aafdc0df53b14678e`; the full local receipt for that
snapshot also passed. This evidence does not prove KLS or certify later documentation edits.
Use [the verification workflow](research/workflow.md#remote-ci-at-verification-milestones)
for exact-SHA evidence and local pre-push checks. Historical handoffs are in
[research/decisions](research/decisions/2026-10-01-handoff-history.md).

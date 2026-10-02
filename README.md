# kls-lean

Lean formalization of functional inequalities and the published literature around the
Kannan–Lovász–Simonovits (KLS) conjecture. Work is selected by source paper and target theorem.
Lean and Mathlib are pinned to **v4.33.0**. Public interfaces may still change; see the
[lifecycle](research/ledger-schema.md#lifecycle) and the [naming guide](research/naming.md).

## Statement

`KLS.Conjecture` asks for one finite constant `C` such that `C_P^lit(μ) ≤ C ‖Cov_μ‖_op` for every
log-concave probability law `μ` with finite second moment on every finite-dimensional Euclidean
space, where `C_P^lit` is the intrinsic local-slope Poincaré constant. See the
[statement](formalization/FunctionalInequalities/KLS/Statement.lean) and the
[open target](formalization/FunctionalInequalities/KLS/Target.lean): `KLS.kls` is the library's
one intentional `sorry` and lies outside every certificate import closure.
**Dimension-free KLS remains open.**

## What is proved

There are **27 registered Lean certificates**, plus proved auxiliary results. Highlights:

- the one-dimensional upper bound `C_P^lit ≤ 4 Var` for log-concave laws on the line;
- finite Poincaré tensorization and the sharp one-dimensional Gaussian constant;
- scalar and vector weighted coarea (C¹, Lipschitz, locally Lipschitz) and sharp scalar Sard;
- canonical energy `E^can = 2 Ch` for every Borel probability law; the weighted-gradient heat
  semigroup with its Markov and positive-time smoothing properties; the Bakry–Émery `Γ`/`Γ₂`
  calculus with `Γ₂ ≥ 0` for smooth convex potentials;
- both numerical Cheeger–Buser comparisons `C_P^lit ≤ 4 Ψ²` and `Ψ² ≤ π C_P^lit` for every
  finite-dimensional log-concave law, including degenerate affine supports;
- metric BV relaxation and Minkowski recovery; Ambrosio–Di Marino–Gigli Theorem 3.6 (relaxed
  Minkowski content equals the Definition 3.3 perimeter, for measures finite on bounded sets) is
  certified as a paper target.

## What is not proved

- Any published high-dimensional KLS bound (KLS 1995, Eldan, Lee–Vempala, Chen, Klartag–Lehec,
  Klartag, Letwin) or the stochastic-localization machinery they use.
- Any complete paper other than Ambrosio–Di Marino–Gigli (Theorem 3.6, the first covered paper).
  A paper is covered only when its main theorem is stated faithfully in Lean, proved without
  nonstandard axioms, and certified for that exact statement. Supporting lemmas, restricted cases
  and conditional reductions do not count.
- General RCD comparisons, nonproper locally Lipschitz BV variants and nonconvex support transfer.

## Where to look

| Entry | Contents |
| --- | --- |
| [Literature register](research/progress/LITERATURE.md) | **Primary progress view**: paper versions, target theorems, Lean statements, status, certificates |
| [Progress hub](research/progress/README.md) | Literature priorities, literature map, exploratory route diagrams |
| [Node register](research/progress/STATUS.md) | Blueprint statements, provenance and certificate mappings |
| [Current handoff](HANDOFF.md) | Verified baseline, current scope and next step |
| [Formalization guide](formalization/README.md) · [Blueprint](formalization/blueprint/README.md) | Library layout, builds, theorem map |
| [Ledger](research/a-series/ledger.yaml) · [Certificates](solutions/README.md) | Certified nodes and their Lean entry points |
| [Workflow](research/workflow.md) · [Verification](research/verification.md) | Task selection, module placement, verification and CI rules |
| [Decision records](research/decisions/) | Dated history, including earlier handoffs |

## Verify

From the repository root:

```bash
(cd formalization && lake build)
python3 research/check_ledger.py
python3 research/verify.py
python3 research/progress/update.py --check
```

`research/verify.py` is the full local verifier: build, strict audit clients, transitive axiom
audit of every local declaration except `KLS.kls`, kernel replay, statement baselines and
metadata checks. Remote CI runs its Lean-only scope (`--lean-only`) on manual dispatch
(`gh workflow run lean.yml`) or a pushed `milestone/**` tag; ordinary pushes do not trigger it.
[Run 36846629874](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/36846629874)
passed for commit `6ca1824`; it does not certify later commits or prove KLS.

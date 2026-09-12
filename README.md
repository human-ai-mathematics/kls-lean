# kls-lean

公共 API 的短名去除命名空间中的重复信息，见[命名指南](research/naming.md)。

Lean formalization of functional inequalities toward the KLS conjecture, with separate
statement review and proof stages. Lean and Mathlib are pinned to **v4.33.0**.

Public Lean interfaces may evolve during this exploratory stage, including interfaces of proved
results. Proof work does not require a prior freeze. `proved` and `\leanok` certify the current
statement and proof, without promising signature stability. Mathematical scope changes are
recorded explicitly and checked against the original goal; see the
[current lifecycle](research/ledger-schema.md#lifecycle). Earlier freeze records remain dated
review snapshots.

## Current status (2026-09-12)

The ledger contains **24 Lean-certified nodes**. Four isolated WIP modules retain **24 explicit
`sorry` proofs**; some downstream proof bodies also depend transitively on those holes. The owner
has chosen to retain this work for later proof development. Neither a WIP file's presence nor its
successful ordinary elaboration promotes it to certified mathematics. The four
[boundary-regularity interfaces](research/decisions/2026-09-12-outward-normal-interfaces-proofs.md)
now have proofs with only standard axioms; Gauss--Green itself remains open.

The recent results include the one-dimensional `4 Var` upper bound, the conditional-fiber
comparison with factor `4`, and `E^can = 2 Ch` in the local-slope convention whenever the intrinsic
law is absolutely continuous, hence for all log-concave laws. The universal conditional-fiber
frame bound and the dimension-free KLS bound remain open. The one-dimensional certificate proves
the upper bound; it does not separately certify optimality of the coefficient `4` across all laws.
See the [status audit and WIP policy](research/decisions/2026-09-12-status-audit-and-wip-retention.md) for the remaining proof
obligations, existing inputs awaiting integration, and verification boundaries.

## Mathematical API organization (2026-09-08)

The public frontends are `SmoothTest`, `SmoothGradient`, `WeightedGradient`,
`CovarianceGradient`, and `LocalSlope`; `Ambient` and `Intrinsic` identify the carrier construction.
Probability pushforwards and L² pullbacks occupy their own layers. See [the naming guide](research/naming.md) and [the migration record](research/decisions/2026-09-08-mathematical-api-organization.md).

## Where to look

| Purpose | Entry point |
| --- | --- |
| Lean source layout, imports, and build instructions | [formalization/README.md](formalization/README.md) |
| Executable theorem map and long-route alternatives | [formalization/blueprint/README.md](formalization/blueprint/README.md) |
| `L²`/energy foundation guide | [Poincare/README.md](formalization/FunctionalInequalities/Poincare/README.md) |
| Compiled foundation examples and boundary cases | [PoincareFoundation.lean](examples/PoincareFoundation.lean) |
| Proved ambient/intrinsic and smooth-test/relaxed comparisons | [Comparison guide](formalization/FunctionalInequalities/Poincare/Euclidean/README.md) |
| Mathematical definitions and scope | [LEAN_DESIGN.md](LEAN_DESIGN.md) |
| Current work and proof handoff | [HANDOFF.md](HANDOFF.md) |
| Node statements and certification status | [research/a-series/ledger.yaml](research/a-series/ledger.yaml) |
| Node-specific Lean entry points | [solutions/README.md](solutions/README.md) |
| Review history | [research/decisions/](research/decisions/) and [research/explorations/](research/explorations/) |
| Literal Lean KLS target | [KLS/Statement.lean](formalization/FunctionalInequalities/KLS/Statement.lean) |
| Local task atlas and snapshot-bound verification | [research/verification.md](research/verification.md) |

The linear-test/covariance lower bound ([#2](https://github.com/numina-functional-inequalities/kls-lean/issues/2))
and binary tensorization upper bound ([#6](https://github.com/numina-functional-inequalities/kls-lean/issues/6))
are proved. Finite tensorization and optimal-constant equality
([#7](https://github.com/numina-functional-inequalities/kls-lean/issues/7)) have completed human
acceptance and semantic review, with a node certificate and `proved` / `checked_by: lean` status.
The [freeze record](research/decisions/2026-09-03-finite-tensorization-freeze.md) preserves the
approved statements, and the [acceptance record](research/explorations/2026-09-03-finite-tensorization-acceptance.md)
records the review and validation. The publication commit and its matching CI result are tracked
in Issue #7.

The sharp one-dimensional Gaussian Poincaré constant has also completed proof and human
semantic review. Its 20 library declarations are proof-complete, and
`Solutions.LemPoincareGaussianOneDimensional.certificate` certifies the two main conclusions;
the node is `proved` / `checked_by: lean`. Start with the
[Gaussian reading guide](formalization/FunctionalInequalities/Poincare/Gaussian/README.md)
for the mathematical meaning, proof architecture, examples and file map. The earlier
[candidate statements](research/decisions/2026-09-04-gaussian-poincare-candidate.md) remain an
append-only record of the review stage rather than the current status. Finite tensorization
supplies infrastructure for the independent-product subclass; it is not a complete product-case
proof for arbitrary one-dimensional log-concave factors. The accepted Gaussian theorem covers
Gaussian factors only and is another certified node toward the broader program.

The [Gaussian freeze](research/decisions/2026-09-04-gaussian-poincare-freeze.md) records the
approved contract and the two permitted tail-API generalizations. The
[Gaussian acceptance record](research/explorations/2026-09-04-gaussian-poincare-acceptance.md)
records the final module split, certificate, axiom audit and local validation gates.

The reusable foundation now also provides intrinsic real `L²` variance, extended energies,
sequential relaxation and recovery, quadratic closure, and affine-support coordinates. The
compactly supported `C∞` gradient realization is dense, and both its direct relaxation and its
intrinsic-affine pullback are proved densely defined closed quadratic energies. Here ordinary
`C∞` is correctly encoded by Mathlib's `ContDiff ℝ ∞`; `ContDiff ℝ ⊤` is analytic and is not an
assumption. The Markov/Dirichlet property of both relaxations is now a proved theorem; agreement
with every raw gradient test and identification with Cheeger energy `2 Ch` remain explicit later
theorems rather than hidden premises; raw/core agreement is now proved for every law with a local
density (`Energy/SmoothGradient/Core.lean`), while the Dirac and normal-direction obstructions show
why it cannot hold unconditionally for the ambient pre-energy. The sharp one-dimensional bound `C_P^lit(ν) ≤ 4 Var_ν` for
every log-concave law on the real line, zero variance included, is now a local Lean theorem (Bobkov's
`12 Var` is a corollary) rather than an imported published input. The conditional-fiber form of the frame route is a proved
Dirichlet energy on `L²(μ)` for every Borel law and every direction law
(`KLS/ConditionalFiber/Closed.lean`), through its symmetric two-point jump representation, and its
comparison with the gradient energy under a fiber Poincaré input `κ`
(`D_{μ,ρ}(f) ≤ κ ∫‖∇f‖² dμ`, hence a form-gap bound `C` gives `C_P^lit(μ) ≤ κ C`) is proved in
`KLS/ConditionalFiber/EnergyComparison.lean`.

The 12 comparison theorems are now proved, with two additional ledger certificates and guarded
transitive axiom checks. They identify arbitrary pre-energy optima with their relaxations and
connect the finite-dimensional legacy, ambient and selected intrinsic frontends. They are exported
by `Poincare.Foundation`; the Gaussian bound and exact constant now transfer through the proved
bridge. See the [comparison guide](formalization/FunctionalInequalities/Poincare/Euclidean/README.md)
for sources, generality and examples. The locally Lipschitz literature comparison has an analytic
argument in Blueprint Appendix A. Its weighted approximation input and all eight constant-comparison
interfaces are Lean-certified under explicit intrinsic absolute continuity. The general
log-concave extension now derives that premise and proves the same constant equality for every
finite-dimensional log-concave probability law, including singular and zero-dimensional support.
See the [general proof record](research/decisions/2026-09-06-general-logconcave-comparison.md).
KLS remains open.

The [Lean Blueprint](formalization/blueprint/README.md) is the navigable mathematical map for
this program. It displays the certified canonical spine, records the remaining bridges and their
mathematical and formalization status, and presents four sufficient KLS route alternatives. The
Blueprint does not replace Lean or the ledger as the source of certification status: a rendered
PDF or web page is documentation, while `\leanok` is reserved for statements and proofs backed by
checked local declarations and, for ledger-backed certificate nodes, matching ledger records.

## Verify

For a quick structural/task check, run `python3 research/atlas.py check`.
For the complete local acceptance workflow, including the statement/definition golden comparison,
all certificate axiom reports and local module kernel replay, run `python3 research/verify.py`. Then run
`python3 research/atlas.py export` and `python3 research/atlas.py ready` to inspect tasks against
the verified source snapshot. See the [workflow guide](research/verification.md).
The KLS statement remains a proposition declaration. The general log-concave constant-comparison
pilot is proved; it supplies no dimension-free bound.

From the repository root:

```bash
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
(cd formalization && lake build)
```

To validate declaration links and build both rendered Blueprint formats, follow the exact local
commands in the [formalization guide](formalization/README.md#lean-blueprint). CI publishes the
PDF and web tree as workflow artifacts; it deliberately does not deploy GitHub Pages.

The `Solutions` default target builds all twenty-four proved certificates and the twenty-five named
definition checks of `StatementChecks.lean`, including the zero-dimensional and Euclidean checks for
the implemented affine covariance Poincaré constant `def:affine-poincare-constant` (a definition
node, not a ledger theorem). The certificates include all four weighted
approximation contracts; see their [acceptance record](research/decisions/2026-09-06-weighted-approximation-acceptance.md).
The eighth certificate packages the eight proved smooth/literature comparison interfaces;
two further certificates cover intrinsic absolute continuity and the general log-concave equality.
The [smooth comparison proof record](research/decisions/2026-09-06-smooth-literature-proofs.md) records
the hypotheses, proof route and local evidence. All eight components have axiom guards.
The reusable-library root
also exports the accepted Gaussian implementation, organized as density calculus, Hardy/Tonelli
estimates, and the final sharp real-line theorem. Default-build audits pin the Gaussian certificate
and 27 foundation and comparison declarations to the transitive axioms `propext`, `Classical.choice`, and
`Quot.sound`. The `Examples` target compiles the foundation's usage and boundary examples.
All proved certificates and their local imports are free of proof escapes.
See the [ledger contract](research/ledger-schema.md).

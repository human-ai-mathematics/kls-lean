# kls-lean

Public API short names omit information already expressed by their namespaces; see the [naming guide](research/naming.md).

Lean formalization of functional inequalities toward the KLS conjecture, with separate
statement review and proof stages. Lean and Mathlib are pinned to **v4.33.0**.

Public Lean interfaces may evolve during this exploratory stage, including interfaces of proved
results. Proof work does not require a prior freeze. `proved` and `\leanok` certify the current
statement and proof, without promising signature stability. Mathematical scope changes are
recorded explicitly and checked against the original goal; see the
[current lifecycle](research/ledger-schema.md#lifecycle). Earlier freeze records remain dated
review snapshots.

## Current status (2026-09-15)

The ledger contains **24 Lean-certified nodes**. Three isolated WIP modules retain **10 explicit
`sorry` proofs** (2/3/5); some downstream proof bodies also depend transitively on those holes.
The proved infrastructure now includes global Gauss–Green, smooth recovery sequences, the
Minkowski coarea inequality, smooth Sard, level-set integral measurability, critical-slice nullity,
weighted graph area on open domains, and C¹ coarea on regular open domains.

The general C¹ and Lipschitz weighted coarea formulas and the reverse Cheeger comparison remain
open. So do the universal conditional-fiber frame bound and the dimension-free KLS bound.
The one-dimensional certificate proves the `4 Var` upper bound; it does not separately certify
optimality of the coefficient `4` across all laws. The identity `E^can = 2 Ch` uses the local-slope
convention and holds when the intrinsic law is absolutely continuous, hence for log-concave laws.
See the [current handoff](HANDOFF.md) for precise scopes and remaining obligations.

## Proof progress tree

Last updated: **2026-09-15**.

**Legend:** ✓ Proved · ◐ Partially complete · ○ Open. The highlighted node is the next planned step.
Here `h_M` denotes the Minkowski Cheeger constant and `h_S` the smooth-boundary Cheeger constant.
Edges group results by topic and route; they are not an exact theorem-dependency graph.
“Proved” refers to the stated result and its checked proof, not to completion of its parent route
or registration as a separate ledger certificate. The [ledger](research/a-series/ledger.yaml)
and [verification guide](research/verification.md) retain those certification boundaries.

```mermaid
flowchart LR
    ROOT["KLS Formalization<br/>○ Dimension-free bound remains open"]

    ROOT --> A["✓ Formulation and Reductions"]
    A --> A1["Log-concave densities<br/>and intrinsic affine support"]
    A --> A2["Centering and covariance whitening"]
    A --> A3["Affine ⇔ Covariance-normalized ⇔ Isotropic"]

    ROOT --> B["✓ Analysis and Energy Foundations"]
    B --> B1["Closed quadratic forms"]
    B --> B2["Normal contraction estimates<br/>→ Dirichlet property"]
    B --> B3["For log-concave densities<br/>Canonical energy = 2 × Cheeger energy"]

    ROOT --> C["◐ Conditional-Fiber Route"]
    C --> C1["✓ One-dimensional log-concave bound<br/>Poincaré constant ≤ 4 × variance"]
    C --> C2["✓ Almost-everywhere fiber log-concavity"]
    C --> C3["✓ Fiber energy ≤ 4 × gradient energy"]
    C --> C4["○ Key frame bound<br/>Dimension-free control needed"]

    ROOT --> D["◐ Isoperimetric Comparison<br/>Current development focus"]
    D --> D1["✓ Forward inequality: h_M ≤ h_S"]
    D1 --> D11["✓ Global Gauss–Green theorem"]
    D1 --> D12["✓ Smooth recovery sequences"]
    D1 --> D13["✓ Minkowski coarea inequality"]

    D --> D2["○ Reverse inequality: h_S ≤ h_M"]
    D2 --> D21["✓ Smooth Sard theorem<br/>Regular superlevel sets"]
    D2 --> D22["◐ Weighted Coarea Formula"]
    D22 --> D221["✓ Measurability of level-set integrals"]
    D22 --> D222["✓ Weighted graph area on open domains"]
    D22 --> D223["✓ Critical slices are null<br/>for almost every level"]
    D22 --> D224["✓ Coarea on regular open domains<br/>Parametric implicit functions and substitution"]
    D22 --> D225["○ Assemble the general C¹ formula<br/>Next step"]
    D22 --> D226["○ Extend to Lipschitz functions"]
    D2 --> D23["○ Smooth coarea inequality<br/>Combine with distance cutoffs"]

    ROOT --> E["✓ Benchmark Results"]
    E --> E1["Sharp one-dimensional Gaussian constant"]
    E --> E2["Finite Poincaré tensorization"]

    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    classDef partial fill:#fff3df,stroke:#c88719,color:#66420d;
    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    classDef focus fill:#fff0dc,stroke:#d47b13,color:#663800,stroke-width:3px;

    class A,A1,A2,A3,B,B1,B2,B3,C1,C2,C3,D1,D11,D12,D13,D21,D221,D222,D223,D224,E,E1,E2 done;
    class C,D,D22 partial;
    class ROOT,C4,D2,D226,D23 todo;
    class D225 focus;

    click ROOT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Statement.lean" "KLS Formalization — ○ Dimension-free bound remains open" _blank
    click A href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean" "✓ Formulation and Reductions" _blank
    click A1 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean" "Log-concave densities — and intrinsic affine support" _blank
    click A2 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean" "Centering and covariance whitening" _blank
    click A3 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean" "Affine ⇔ Covariance-normalized ⇔ Isotropic" _blank
    click B href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/README.md" "✓ Analysis and Energy Foundations" _blank
    click B1 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/SmoothGradient/Closed.lean" "Closed quadratic forms" _blank
    click B2 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean" "Normal contraction estimates — → Dirichlet property" _blank
    click B3 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/Cheeger.lean" "For log-concave densities — Canonical energy = 2 × Cheeger energy" _blank
    click C href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber.lean" "◐ Conditional-Fiber Route" _blank
    click C1 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean" "✓ One-dimensional log-concave bound — Poincaré constant ≤ 4 × variance" _blank
    click C2 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean" "✓ Almost-everywhere fiber log-concavity" _blank
    click C3 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean" "✓ Fiber energy ≤ 4 × gradient energy" _blank
    click C4 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Key frame bound — Dimension-free control needed" _blank
    click D href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean" "◐ Isoperimetric Comparison — Current development focus" _blank
    click D1 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean" "✓ Forward inequality: h_M ≤ h_S" _blank
    click D11 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean" "✓ Global Gauss–Green theorem" _blank
    click D12 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean" "✓ Smooth recovery sequences" _blank
    click D13 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean" "✓ Minkowski coarea inequality" _blank
    click D2 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean" "○ Reverse inequality: h_S ≤ h_M" _blank
    click D21 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/SmoothSard.lean" "✓ Smooth Sard theorem — Regular superlevel sets" _blank
    click D22 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md" "◐ Weighted Coarea Formula" _blank
    click D221 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean" "✓ Measurability of level-set integrals" _blank
    click D222 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean" "✓ Weighted graph area on open domains" _blank
    click D223 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean" "✓ Critical slices are null — for almost every level" _blank
    click D224 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean" "✓ Coarea on regular open domains — Parametric implicit functions and substitution" _blank
    click D225 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l11" "○ Assemble the general C¹ formula — Next step" _blank
    click D226 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l12" "○ Extend to Lipschitz functions" _blank
    click D23 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean" "○ Smooth coarea inequality — Combine with distance cutoffs" _blank
    click E href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Poincare/README.md" "✓ Benchmark Results" _blank
    click E1 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Poincare/Gaussian/Real.lean" "Sharp one-dimensional Gaussian constant" _blank
    click E2 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean" "Finite Poincaré tensorization" _blank
```

Click any node to open its Lean source or documentation in a new tab. Open nodes link to
unproved obligations or route plans. Links follow `main` so they stay aligned with the current tree.
If your Markdown viewer disables diagram links, use the directory below.

<details>
<summary>Node links: Lean sources and documentation</summary>

| Node | Destination |
| --- | --- |
| KLS Formalization — ○ Dimension-free bound remains open | [Open Lean source](formalization/FunctionalInequalities/KLS/Statement.lean) |
| ✓ Formulation and Reductions | [Open Lean source](formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean) |
| Log-concave densities — and intrinsic affine support | [Open Lean source](formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean) |
| Centering and covariance whitening | [Open Lean source](formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean) |
| Affine ⇔ Covariance-normalized ⇔ Isotropic | [Open Lean source](formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean) |
| ✓ Analysis and Energy Foundations | [Open documentation](formalization/FunctionalInequalities/Energy/README.md) |
| Closed quadratic forms | [Open Lean source](formalization/FunctionalInequalities/Energy/SmoothGradient/Closed.lean) |
| Normal contraction estimates — → Dirichlet property | [Open Lean source](formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean) |
| For log-concave densities — Canonical energy = 2 × Cheeger energy | [Open Lean source](formalization/FunctionalInequalities/Energy/Cheeger.lean) |
| ◐ Conditional-Fiber Route | [Open Lean source](formalization/FunctionalInequalities/KLS/ConditionalFiber.lean) |
| ✓ One-dimensional log-concave bound — Poincaré constant ≤ 4 × variance | [Open Lean source](formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean) |
| ✓ Almost-everywhere fiber log-concavity | [Open Lean source](formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| ✓ Fiber energy ≤ 4 × gradient energy | [Open Lean source](formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| ○ Key frame bound — Dimension-free control needed | [Open documentation](formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ◐ Isoperimetric Comparison — Current development focus | [Open Lean source](formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean) |
| ✓ Forward inequality: h_M ≤ h_S | [Open Lean source](formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean) |
| ✓ Global Gauss–Green theorem | [Open Lean source](formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean) |
| ✓ Smooth recovery sequences | [Open Lean source](formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean) |
| ✓ Minkowski coarea inequality | [Open Lean source](formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean) |
| ○ Reverse inequality: h_S ≤ h_M | [Open Lean source](formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| ✓ Smooth Sard theorem — Regular superlevel sets | [Open Lean source](formalization/FunctionalInequalities/Analysis/SmoothSard.lean) |
| ◐ Weighted Coarea Formula | [Open documentation](research/decisions/2026-09-15-weighted-coarea-route.md) |
| ✓ Measurability of level-set integrals | [Open Lean source](formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean) |
| ✓ Weighted graph area on open domains | [Open Lean source](formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean) |
| ✓ Critical slices are null — for almost every level | [Open Lean source](formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean) |
| ✓ Coarea on regular open domains — Parametric implicit functions and substitution | [Open Lean source](formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean) |
| ○ Assemble the general C¹ formula — Next step | [Open documentation](research/decisions/2026-09-15-weighted-coarea-route.md#l11) |
| ○ Extend to Lipschitz functions | [Open documentation](research/decisions/2026-09-15-weighted-coarea-route.md#l12) |
| ○ Smooth coarea inequality — Combine with distance cutoffs | [Open Lean source](formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| ✓ Benchmark Results | [Open documentation](formalization/FunctionalInequalities/Poincare/README.md) |
| Sharp one-dimensional Gaussian constant | [Open Lean source](formalization/FunctionalInequalities/Poincare/Gaussian/Real.lean) |
| Finite Poincaré tensorization | [Open Lean source](formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean) |

</details>

**Maintenance:** Whenever proof progress changes, update this tree, its date, and the current
status above in the same change as the proof and its verification records. Keep labels in English,
preserve the exact mathematical scope, and move completion markers or the next-step highlight only
when supported by the current source and verification evidence. Keep every node link and the
link directory aligned with its current source or document, including after file moves.

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
| Proof corrections, stronger bounds, and simpler arguments | [Proof Corrections and Improvements](research/proof-corrections-and-improvements.md) |
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

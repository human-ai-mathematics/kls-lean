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

## Current status (2026-09-22)

The ledger contains **26 Lean-certified nodes**. The former coarea, Sard, Cheeger-infimum
and Energy WIP modules have been closed and removed. **One explicit target hole remains**:
`KLS.kls` in `KLS/Target.lean`, outside every certificate import closure. The dimension-free
KLS bound remains open.

**Formalized in Lean:** scalar and vector weighted coarea for C¹, Lipschitz and locally
Lipschitz maps; scalar Sard at the sharp `C^(finrank)` regularity; the Cheeger superlevel
integral bound and both infimum comparisons; canonical energy `E^can = 2 Ch` for every Borel
probability law, using the local-slope convention; and the intrinsic literature Poincaré
constant's gradient characterization. The one-dimensional Poincaré certificate gives the
`4 Var` upper bound, without separately certifying optimality across all laws.

The Cheeger direction `C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²` is proved for every log-concave law. The Buser
direction is proved for affine-support dimension at most one with constant **12**. The target
`Ψ_KLS(μ)² ≤ π C_P^lit(μ)` remains unproved locally; 12 does not establish π.

The semigroup program now includes **S1–S8**, the concrete weighted-gradient heat semigroup,
and its **Markov properties**: positivity, preservation of constants and integrals, the
sub-Markov bound, absolute-value domination, and contraction of finite essential bounds on
`L²`. The full-dimensional theorems apply to arbitrary log-concave laws in intrinsic
coordinates. For a smooth tilted potential the generator is identified on smooth compactly
supported tests: `T̄†T̄ [f] = [-(Δf - ⟪∇U, ∇f⟫)]`, via weighted integration by parts. This is a
per-test statement, not an operator-core result. The local Bakry–Émery calculus is proved
pointwise for smooth functions: the carré-du-champ product identity, positive semidefiniteness
of the Hessian of a convex potential, the Bochner identity
`Γ₂(f) = ∑ᵢ∑ⱼ (D²f(eᵢ, eⱼ))² + D²U(∇f, ∇f)` in the fixed standard basis, and `Γ₂ ≥ 0`
(`Analysis/BakryEmery/Gamma.lean`, `Bochner.lean`). Right generator limits now characterize
`D(A)`: for inputs in `D(A)`, `P_t` preserves that domain, commutes with `A`, and has right
derivative `-A(P_t f)` at every `t ≥ 0`. The **whole form domain** is now stable as well: for
every `f ∈ D(T̄)` and `t ≥ 0`, `P_t f ∈ D(T̄)` and `‖T̄(P_t f)‖ ≤ ‖T̄ f‖`, proved through
graph-norm density of `D(A)` in `D(T̄)` and a two-parameter resolvent energy identity
(`Analysis/Semigroup/Generated/FormDomain.lean`, `Resolvent/Limit.lean`). **Positive time even
regularizes arbitrary data**: for every `f ∈ L²(ν)` and `t > 0`, `P_t f ∈ D(T̄†T̄)` with
`‖T̄(P_t f)‖ ≤ ‖f‖/√(2t)` and `‖T̄†T̄(P_t f)‖ ≤ ‖f‖/t`, from two second-order dissipation estimates
for the Yosida exponentials (`Analysis/Semigroup/Exponential/Dissipation.lean`,
`Generated/Smoothing.lean`). The heat wrappers retain arbitrary weights and give closed weighted
gradients. The sharp constants `1/√(2et)` and `1/(et)`, classical representatives and pointwise
gradient estimates remain open; membership in `D(T̄†T̄)` does not supply a classical representative
or the integrability, domains and differentiation rules for `Γ(P_t f)`. Weak Γ integrability, stability, smooth-test integrated Bochner and conditional limit-transfer
interfaces are now proved. The **second-order field has since been eliminated** from the weak
`Γ₂` inequality: a Leibniz rule for the closed gradient against a `C_c^∞` multiplier, valid on
the whole form domain, gives
`∫ φ Γ(T̄F, T̄(AF)) dν = ∫ φ (AF)² dν - ∫ (AF) Γ(T̄F, T̄φ) dν`, so the inequality transfers along
`[fₙ] → F` and `A[fₙ] → A F` in `L²` alone
(`L2/BoundedMultiplier.lean`, `KLS/LogConcave/WeightedGradient/Multiplier.lean`,
`KLS/LogConcave/HeatSemigroup/GammaTwo.lean`). For the heat flow the inequality was first proved under a
single explicit hypothesis, then that hypothesis was **reduced to a local one**
(`KLS/LogConcave/HeatSemigroup/OperatorCore.lean`), and that local statement — interior
regularity of distributional solutions of `ℒ u = u`, i.e. `[χ u] ∈ D(T̄)` for every
`χ ∈ C_c^∞` — is now **proved** by mollification against the Haar measure
(`Analysis/Mollification.lean`, `KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean`). Hence
`C_c^∞` **is an operator core** of `T̄†T̄` for every `C¹` potential (`ℒ` is essentially
self-adjoint on `C_c^∞`), and the **heat-flow weak `Γ₂` inequality holds with only the model
hypotheses** — `C^∞` convex potential, unit weight, arbitrary `g ∈ L²(ν)`, every `t > 0`, every
nonnegative `φ ∈ C_c^∞` (`HeatSemigroup.integral_mul_weakGamma_apply_nonneg`). The product/chain rules otherwise still apply to `IsTest` inputs, and the
original second-stage gradient-estimate target remains open. There
are no pointwise Bakry–Émery gradient estimates for the semigroup or small-time heat bounds yet.

The heat-test extension is **partial** (`HeatSemigroup/TestClass.lean`): evolved smooth tests
`P_s φ` and their generator images have uniform essential bounds, and both weak-Γ pairings
are integrable for arbitrary `L²` fields. The inequality accepts these tests when the data
are smooth and compactly supported. Its extension to arbitrary positive-time heat data still
requires an unproved limit argument; time interpolation and gradient estimates remain open.

**Next priority:** [complete the Buser comparison with constant π for every finite-dimensional
log-concave law](research/decisions/2026-09-20-buser-handoff-prompt.md), then combine it with the
proved Cheeger half. Generator identification, Bochner/gradient estimates, general-law passage
and small-time heat bounds are internal proof milestones, not the final deliverable. This is
an implementation target, not a completed result. Even its completion will leave the four KLS
routes' open research conditions to resolve.

The [current handoff](HANDOFF.md#current-operational-status-2026-09-22) and
[status correction record](research/decisions/2026-09-20-current-status-alignment.md) supersede
older pending-work summaries. The latest proof-round receipt is
`20260922T110108.224405Z`, identified in
`build/audit/heat-test-class-takeover/final-snapshot.json`. It records a local build and kernel
replay for that snapshot. The subsequent documentation alignment leaves Lean sources and
certificate status unchanged; it is not a fresh full verification or a remote CI result.

## Proof progress tree

The [progress hub](research/progress/README.md) keeps our
[route diagrams](research/progress/README.md#proof-progress-tree) and
[node-by-node progress table](research/progress/STATUS.md) together.
The diagrams use ✓ / ◐ / ○ for local Lean progress, with arrows pointing toward KLS.
The table separates upstream mathematical status from local formalization and certificate records.
The [literature map](research/progress/README.md#kls-literature-through-july-2026) and
[paper-by-paper register](research/progress/LITERATURE.md) cover foundational sources and the
KLS, thin-shell and slicing literature through July 2026, with explicit local proof coverage.

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
with raw gradient tests retains explicit hypotheses, while identification with Cheeger energy
`2 Ch` is proved for every Borel probability law. Raw/core agreement is proved for every law with a local
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
all certificate axiom reports, strict compilation of every research audit client, and local module
kernel replay, run `python3 research/verify.py`. Then run
`python3 research/atlas.py export` and `python3 research/atlas.py ready` to inspect tasks against
the verified source snapshot. See the [workflow guide](research/verification.md).
`KLS.Conjecture` names the proposition; `KLS.kls` in the isolated target module remains unproved.
The general log-concave constant comparison is proved; it supplies no dimension-free bound.

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

The `Solutions` default target builds all twenty-six proved certificates and the twenty-five named
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

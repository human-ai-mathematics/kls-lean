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

## Current status (2026-09-27)

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

Both numerical Cheeger–Buser directions are now proved for every finite-dimensional
log-concave probability law: `C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²` and
`Ψ_KLS(μ)² ≤ π C_P^lit(μ)`. The second bound uses actual Gaussian convolution,
Cheeger test stability and intrinsic-coordinate transport; it includes zero-dimensional
affine support and infinite optima. This does not prove a dimension-free KLS bound.
The bounded-support metric BV perimeter and closed-support probability law now have
Lean interfaces. Equivalence with the unrestricted Lipschitz-test perimeter, the
general BV--Minkowski identification, and its Cheeger-infimum equality remain
literature comparisons. The current formalization handoff is this BV bridge;
the dimension-free KLS routes remain open.

For the actual full-dimensional log-concave weighted-gradient heat semigroup, an explicit
form-domain Poincaré inequality with `C > 0` now gives centered squared `L²` decay
`‖center(P_t f)‖² ≤ exp(-2t/C) ‖center(f)‖²` for every `f ∈ L²` and `t ≥ 0`.
The centered indicator correlation is at most `exp(-t/C) ν(D)(1-ν(D))`, including
mass-zero/full sets and time zero. The closed unit-gradient form's optimal constant is now
identified with `C_P^lit`; indicator L¹ displacement and the π perimeter bound yield the
exact π comparison for the smooth convex tilted model, including zero and infinite optima.
The affine-support transport is now proved in that smooth intrinsic model. A new
Prékopa–Leindler argument shows that Gaussian convolution of an arbitrary intrinsic
Borell density is measurable, finite, positive, and log-concave. The Gaussian
mass is now computed, and the normalized convolution is a log-concave probability
law with a positive `C∞` density and `C∞` convex potential, including dimension
zero. Every finite Gaussian-kernel derivative has a uniform bound, allowing
iterated differentiation of the actual source-law integral without source
moments. The normalized densities converge almost everywhere and in `L¹(volume)`;
the laws converge on every measurable set. The intrinsic literature Poincaré
constant of the actual convolution is at most the source constant plus
`1/(2s)` for every `s > 0`, including dimension zero and infinite optima.
The Cheeger-infimum passage now transfers the exact π comparison to general
nonsmooth laws. It does not assert a pointwise perimeter limit for each smooth
domain. See
the [bridge record](research/decisions/2026-09-25-heat-buser-bridge.md),
[affine continuation](research/decisions/2026-09-25-affine-smooth-buser.md),
[approximation continuation](research/decisions/2026-09-25-gaussian-approximation.md),
[first regularity](research/decisions/2026-09-25-gaussian-first-regularity.md),
[second regularity](research/decisions/2026-09-25-gaussian-second-regularity.md), and
[all-order regularity](research/decisions/2026-09-25-gaussian-infinite-regularity.md), and
[Poincaré stability](research/decisions/2026-09-25-gaussian-poincare-stability.md), and
[general π-Buser passage](research/decisions/2026-09-26-nonsmooth-pi-buser.md).

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
original second-stage gradient-estimate target was still open at that stage; the later
pointwise and small-time heat results are recorded below. This integrated square estimate
itself is a tested, rather than pointwise, statement.

The heat-test extension is **proved** (`HeatSemigroup/TestClass.lean`,
`HeatSemigroup/TestClassExtension.lean`). Evolved smooth tests `P_s φ` and their generator
images have uniform essential bounds, and both weak-Γ pairings are integrable for arbitrary
`L²` fields. For arbitrary `g`, `r > 0`, nonnegative `φ ∈ C_c^∞` and `s ≥ 0`, the inequality
`0 ≤ -(1/2)∫(A P_s φ)Γ(T̄P_r g,T̄P_r g) + ∫ P_s φ Γ(T̄P_r g,T̄A P_r g)` holds
(`HeatSemigroup.integral_weakGamma_operator_nonneg`, 2026-09-23). The time interpolation
`r ↦ ∫ (P_{t-r} φ) Γ(T̄P_r f) dν` is monotone. It gives the integrated square gradient
estimate `∫ φ Γ(T̄P_t f) dν ≤ ∫ (P_t φ) Γ(T̄f) dν` for every `f ∈ D(T̄)`, `t ≥ 0` and
nonnegative `φ ∈ C_c^∞` (`HeatSemigroup.integral_mul_weakGamma_le`,
[record](research/decisions/2026-09-23-heat-gradient-square-estimate.md)). Two further
estimates are proved in tested form:

- the reverse local Poincaré inequality
  `2t ∫ φ Γ(T̄P_t f) ≤ ∫ (P_t φ) f² - ∫ φ (P_t f)²` for arbitrary `f ∈ L²`, with the bounded-data
  `L^∞ → Lip` form;
- Bakry's `L¹` self-improvement `∫ φ |T̄P_t f| ≤ ∫ (P_t φ) |T̄f|` for `f ∈ D(T̄)`
  ([record](research/decisions/2026-09-23-heat-reverse-poincare-self-improvement.md)).

The [a.e. continuation](research/decisions/2026-09-23-heat-almost-everywhere.md) proves
`|T̄P_t f| ≤ M/√(2t)` for bounded initial data (`t > 0`), and
`|T̄P_t f| ≤ P_t|T̄f|` for form-domain data (`t ≥ 0`), together with global gradient `L¹`
contraction. The [small-time continuation](research/decisions/2026-09-23-heat-small-time-perimeter.md)
proves `∫ |f-P_t f| ≤ √(2t) ∫ |T̄f|` on the form domain and
`∫ |1_D-P_t 1_D| ≤ √(2t) P_ρ(D)` for smooth domains, using the actual relative-perimeter
recovery sequence (including infinite perimeter in ENNReal and time zero).
The coefficient needed for the sharp route, `2√(t/π)`, is now formalized in the
smooth convex model via the Gaussian-profile BGL inequality and the coefficient
continuation below. The smooth-model Buser assembly is proved in the later
[bridge continuation](research/decisions/2026-09-25-heat-buser-bridge.md). The numerical
general-law π bound is now proved through Gaussian Cheeger stability; a direct
general-law heat/perimeter estimate is a separate statement.
The [Gaussian scalar continuation](research/decisions/2026-09-24-gaussian-profile.md)
constructs the actual density/quantile profile and proves `I I'' = -1` on `(0,1)`,
its attained upper bound `1/sqrt(2*pi)`, endpoint limits, continuity and strict concavity
on `[0,1]`. The [regularization continuation](research/decisions/2026-09-24-gaussian-regularization.md)
adds interior smoothness, reflection, the midpoint value, shifted-profile bounds and
pointwise epsilon convergence, and a globally smooth extension with bounded first two
derivatives agreeing near the admissible range. The
[tested chain-rule continuation](research/decisions/2026-09-24-heat-chain-rule.md)
proves the identity on arbitrary `D(A)` data and the actual shifted Gaussian-profile
specialization, including integrability of the generic pairings. It needs only a C1
potential and bounded `psi`, with no bound on `A psi`. The
[composition-domain continuation](research/decisions/2026-09-24-heat-composition-domain.md)
now identifies `Phi(F) in D(A)` and its generator when Gamma is in L2, via the actual
smooth graph core and self-adjointness. It proves that integrability for bounded
positive-time heat data and derives the actual shifted Gaussian operator identity,
including range preservation from the initial datum. The
[time-differentiation continuation](research/decisions/2026-09-24-heat-composition-derivative.md)
proves nonlinear differentiation along L2 curves, the actual Gaussian positive-time
L2 derivative, and the tested interior heat-interpolation derivative with exact
generator cancellation. The
[strong-interpolation continuation](research/decisions/2026-09-24-heat-strong-interpolation.md)
now proves the outer varying-datum product rule, strong L2 Gaussian interpolation,
the unshifted positive profile, and its bounded-test squared derivative. The
[weighted-Cauchy continuation](research/decisions/2026-09-24-heat-weighted-cauchy.md)
proves positive-map quadratic preservation and combines it with L1 gradient
self-improvement to obtain the Gaussian dissipation lower bound and the quantitative
square differential inequality for bounded nonnegative tests. The
[integrated-profile continuation](research/decisions/2026-09-24-heat-integrated-profile.md)
fixes one continuous interpolation curve, integrates the bound with both time endpoints,
and proves the a.e. regularized inequality retaining the terminal heat-profile square.
The [profile-limit continuation](research/decisions/2026-09-24-heat-profile-limit.md)
removes the epsilon/range margin by dominated L2 convergence and heat/closed-gradient
linearity. For every `0 <= f <= 1`, it proves
`2t Gamma(T P_t f) <= I(P_t f)^2 - (P_t I(f))^2` a.e. in the smooth convex model.
The [pi-coefficient continuation](research/decisions/2026-09-25-heat-pi-coefficient.md)
proves `|T P_t f| <= M/sqrt(pi*t)` and the `2 sqrt(t/pi)` whole-form-domain L1 bound,
then transfers it through the actual recovery sequence to smooth-domain relative
perimeter. The ENNReal bound includes zero time and infinite perimeter. Earlier
numerical API statements are preserved as weaker bounds.
The later [bridge continuation](research/decisions/2026-09-25-heat-buser-bridge.md)
completes the smooth-model π Buser assembly at the exact extended literature optimum.
The [affine continuation](research/decisions/2026-09-25-affine-smooth-buser.md)
transports it to `inverseScale` for any law with a smooth convex tilted intrinsic
representation. General-law heat/perimeter transfer remains open.
The [approximation continuation](research/decisions/2026-09-22-heat-test-approximation.md)
proves `r³ ‖T A P_r g‖² ≤ 4 ‖g‖²` and continuity of both heat fields in the initial datum.
It constructs two-field approximants `P_{r/2}[fₙ]` with `fₙ ∈ C_c^∞`, but these heat values
are not asserted to be compactly supported smooth data. At that point the higher-order core
was still missing; the 2026-09-23 two-field core below supplies it.
The subsequent [resolvent route review](research/decisions/2026-09-22-heat-test-extension-route.md)
added no Lean proof: at that point density of `(I+A)C_c^∞` in the form domain was unproved,
and its orthogonality condition involves `(I+A)²`, beyond the existing deficiency-element theorem.
The [finite splitting construction](research/decisions/2026-09-22-wave-splitting-construction.md)
now formalizes explicit flows, jointly smooth cells and common compact support. The
[energy continuation](research/decisions/2026-09-22-wave-splitting-energy.md) proves Haar
preservation of every finite derivative energy under coordinate sweeps, and zero-order split
stability under an explicit coefficient bound. The [higher-order continuation](research/decisions/2026-09-23-wave-splitting-stability.md)
proves the finite Leibniz bound and reaction, split, grid and cell stability at every finite order,
including five, under explicit bounds on coefficient derivatives. The [localization continuation](research/decisions/2026-09-23-wave-splitting-localization.md)
constructs a compact coefficient agreeing on the propagation ball and removes those global bounds
from fixed-horizon stability for the original smooth coefficient. The [consistency continuation](research/decisions/2026-09-23-wave-splitting-consistency.md)
proves the complete-step generator identity and the actual residual's joint smoothness, zero
initial value and exact time-integral representation. The [generator bounds](research/decisions/2026-09-23-wave-generator-bounds.md)
prove one-order energy loss for the full generator and two-order loss for its square and all
ordered elementary pairs. The [residual continuation](research/decisions/2026-09-23-wave-splitting-residual.md)
bounds the differentiated split products with their flow factors and proves the tame residual
estimate `E_k(e_Y(t)) <= C t^2 E_(k+2)(Y)` for `0 <= t <= 1`, with an explicit mesh-independent
constant. On actual grid cells it gives `E_k <= C δ^2`, for original smooth coefficients over a
fixed horizon. The [weighted-energy continuation](research/decisions/2026-09-23-wave-splitting-weighted-energy.md)
proves the weighted skew identity and the forced bound `sqrt W(cell) <= sqrt W(Y) + C δ`, with
horizon-independent leading term. It also bounds the gradient compatibility defect `p - D u` and
the weighted form energy of `u` on actual cells. The [time-average continuation](research/decisions/2026-09-23-wave-splitting-time-average.md)
proves that the cellwise average `q` is `C_c^∞` and satisfies the exact identity for `J_cl q - h`.
The [error continuation](research/decisions/2026-09-23-wave-splitting-average-error.md)
proves `sqrt FE_w(J_cl q - h) <= sqrt(∫ w h^2)/L + C δ` on all meshes `N δ = L`, and hence
classical form-range approximation for every compactly supported smooth `h`. The
[form-range continuation](research/decisions/2026-09-23-wave-splitting-form-range.md) proves
the norm and operator identifications and the class-level density: for every `z` in the form
domain `D(T̄)` and `ε > 0` some `q ∈ C_c^∞` has `[q] ∈ D(A)`, `(I+A)[q] ∈ D(T̄)` and
`‖(I+A)[q] - z‖_E < ε` in the graph norm (`HeatSemigroup/FormRange.lean`). The
[frontend continuation](research/decisions/2026-09-23-heat-test-extension-frontend.md) proves
the expansion `‖Je‖² + ‖TJe‖² = ‖e‖² + 3‖Te‖² + 3‖Ae‖² + ‖TAe‖²`. Hence every `F ∈ D(A)` with
`AF ∈ D(T̄)` has a `C_c^∞` two-field approximation, and the heat-test frontend above follows.

**Next priority:** resolve an outstanding dimension-free KLS route condition in the
[four-route overview](research/progress/README.md#proof-progress-tree). The numerical
Cheeger–Buser comparison is complete, but none of the four sufficient routes
has yet proved the dimension-free KLS bound.

The [current handoff](HANDOFF.md#current-result-nonsmooth-gaussian-cheeger-passage-2026-09-26)
supersedes older pending-work summaries. The historical
[status correction record](research/decisions/2026-09-20-current-status-alignment.md) and
the tested-chain-rule verification receipt at `build/audit/heat-chain-rule/final-snapshot.json`
remain dated records.
The local verifier builds sources and replays local modules while trusting pinned third-party
compiled imports; it is not a fresh replay of dependencies or a remote CI result.

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

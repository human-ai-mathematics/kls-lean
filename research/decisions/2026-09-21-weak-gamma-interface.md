# The weak `Γ` interface: `W0`–`W3`

2026-09-21, after the positive-time smoothing round
(`2026-09-21-semigroup-positive-time-smoothing.md` and its scope correction). This round builds
the interface that connects the **pointwise** Bochner calculus of `Analysis/BakryEmery/` to the
**closed-form** heat semigroup of `Analysis/Semigroup/` and `KLS/LogConcave/HeatSemigroup/`. It
preserves all earlier work, makes no commit or push, does not upgrade Lean/Mathlib, and does
**not** complete Bakry–Émery, Buser or KLS. In particular it does not prove `Γ(P_t f) ≤ P_t Γ(f)`
in any form.

## The intermediate class, stated in full

Throughout, `V` is a finite-dimensional real inner product space with its Borel structure
(`[CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
[FiniteDimensional ℝ V]`), `m` is a Haar measure on `V`, and `ν : ProbabilityMeasure V` is
full-dimensional log-concave (`hν : LogConcave ν`,
`hi : (interior (ν : Measure V).support).Nonempty`) with

`(ν : Measure V) = m.tilted (-U)`.

The potential's regularity is stated **per theorem** and is never assumed globally:

| Result | `U` | data `f` | test `φ` |
| --- | --- | --- | --- |
| weighted IBP, symmetry of `ℒ` (`W2` input) | `C¹` | `C²`, compact support | `C²`, compact support |
| pointwise `Γ₂ ≥ 0` (existing `B4`) | `C²`, `ConvexOn ℝ Set.univ U` | `C³` | — |
| integrated Bochner `W2` (classical and weak) | `C²` convex | `C³`, compact support | `C²`, compact support, `φ ≥ 0` |
| `A [f] = [-ℒf] ∈ D(T̄)` (`W3` field) | `C^∞` | `C^∞`, compact support | — |

`C^∞` is required exactly where a *second* application of the differential operator must stay in
the smooth compactly supported test class, i.e. where `-ℒ f` itself has to be a test; nowhere
else. No convexity is used outside the `Γ₂` statements. The weight is `B = I`
(`ContinuousLinearMap.id ℝ V`) exactly where the classical `Γ(f, g) = ⟪∇f, ∇g⟫` is involved;
every purely operator-theoretic statement keeps an **arbitrary** weight `B : V →L[ℝ] V`.

`T = hν.weightedOperator m B hi` is the weighted gradient on Lipschitz `L²` tests, `T̄` its
closure (`hν.closedWeightedOperator`), `A = T̄†T̄ = adjointComp T̄` the **nonnegative** generator,
`ℒ = -A`, and `P_t = HeatSemigroup.operator m B hν hi ht = exp (-t A)`.

## Placement plan (recorded before editing)

| Item | Object and role | Destination | Decision |
| --- | --- | --- | --- |
| `W0` weak carré du champ of two `L²` vector fields, its `L¹` theory and stability | generic measure-space/`L²` object; reusable analytic tool | `Analysis/BakryEmery/WeakGamma.lean` | **create**: the `BakryEmery` family owns `Γ`; `Gamma.lean` is pointwise-classical and must not acquire `Lp`/`LinearPMap` dependencies. The one operator-level theorem (`Γ` against `T†T`) is the integration boundary between the form and the generator, so it belongs here rather than in the abstract Hilbert-space module `Semigroup/VonNeumann.lean`, which carries no measure |
| `W1` Leibniz and chain rules | calculus on the weighted-gradient **test class** | `Energy/WeightedGradient/Leibniz.lean` | **create**: `Basic.lean` owns the test class and its additive/homogeneous a.e. rules, `Core.lean` the dense domain and smooth core, `Closable.lean` closability. The nonlinear rules need new hypotheses (boundedness; a `C¹` outer map) and a different proof pattern, so they split off rather than enlarging `Basic.lean` |
| pointwise `∇(Φ ∘ g)`, `∇(-g)` | local differential tools | `Analysis/BakryEmery/Calculus.lean` | **extend**: that module already owns `gradient_mul` and `gradient_sub` |
| `ContDiff`/support regularity of `ℒ` and of `Γ` | elementary properties of the owning objects | `Analysis/BakryEmery/Laplacian.lean`, `Gamma.lean` | **extend**: same objects, same role as the existing continuity and compact-support lemmas |
| symmetry `∫ (ℒf) g dμ = ∫ f (ℒg) dμ` | tilted-measure integral identity | `Analysis/BakryEmery/IntegrationByParts.lean` | **extend**: it is `G0` applied twice, in the module that owns `G0`; no convexity enters |
| `W2` integrated Bochner, classical and weak, and the `W3` limit transfer | substantive theorem: the **integrated** form of `Γ₂ ≥ 0` | `Analysis/BakryEmery/IntegratedBochner.lean` | **create**: `Bochner.lean` is pointwise and measure-free by design; the integrated statement needs `IntegrationByParts.lean` and `WeakGamma.lean`, which `Bochner.lean` must not import |
| general-test domain and value of `T̄` | elementary properties of the closed weighted gradient | `KLS/LogConcave/WeightedGradient/Closure.lean` | **extend**: that module owns `T̄`'s closedness and dense domain. The existing `C_c^∞` versions in `HeatSemigroup/Generator.lean` are left untouched; the new lemmas are strictly more general and carry `_of_isTest`/`_apply_toLp` in their names, and are not aliases |
| second-order positive-time regularity `A (P_t g) ∈ D(T)` | abstract semigroup domain statement at positive times | `Analysis/Semigroup/Generated/Smoothing.lean` | **extend**: that module owns the positive-time domain statements `E2`–`E4`, and the new one is their composition through `P_t = P_{t/2} P_{t/2}` plus `S0a`'s commutation |
| its concrete frontend | concrete specialization, arbitrary weight `B` | `KLS/LogConcave/HeatSemigroup/Domain.lean` | **extend**: that module is the concrete domain frontend for exactly these statements |
| `W0`–`W3` concrete frontends for `T̄`, `A` and `P_t` | concrete specialization and identification bridge | `KLS/LogConcave/HeatSemigroup/Gamma.lean` | **create**: `HeatSemigroup/Domain.lean` owns the domain interfaces and `Generator.lean` the `C_c^∞` generator identification; the `Γ` interface is a third responsibility with its own imports (`IntegratedBochner`, `Leibniz`) |

No empty module, compatibility alias or old-path wrapper was created; no existing statement,
parameter list or namespace was changed. `FunctionalInequalities.lean` gains the four new leaves.
`Analysis/BakryEmery/Calculus.lean` gains one Mathlib import
(`Mathlib.Analysis.InnerProductSpace.Calculus`, for `ContDiff.inner`).

## `W0`: a legal weak `Γ` pairing

`WeakGamma.apply u v = fun x => ⟪u x, v x⟫` for `u v : Lp H 2 μ`, on any measure space and any
real inner product space `H`. Proved in `Analysis/BakryEmery/WeakGamma.lean`:

| Obligation | Declaration |
| --- | --- |
| a.e. strong measurability | `WeakGamma.aestronglyMeasurable` |
| **`L¹`**, not `L²`, integrability | `WeakGamma.integrable` |
| representative independence | `WeakGamma.ae_eq_of_ae_eq` |
| symmetry, `Γ(u, u) = ‖u‖²`, nonnegativity, Cauchy–Schwarz | `comm`, `self_eq_norm_sq`, `self_nonneg`, `abs_le_mul` |
| `∫ Γ(u, v) dμ = ⟪u, v⟫`, `∫ Γ(u, u) dμ = ‖u‖²` | `integral_eq_inner`, `integral_self_eq_norm_sq` |
| legality of `∫ φ Γ(u, v) dμ` | `integrable_mul`, for `φ` a.e. bounded and a.e. strongly measurable |
| `L¹` stability | `integral_abs_sub_le`, `abs_integral_mul_sub_le`, `tendsto_integral_mul` |
| `L²` Cauchy–Schwarz for the pointwise norms | `integrable_norm_mul_norm`, `integral_norm_mul_norm_le` |

The prompt's warning is respected: `Γ(u, v)` is **not** treated as an `L²` function anywhere, no
`L¹` semigroup extension is introduced, and the only admissible multipliers are a.e. bounded
functions. The bridge to the classical `Γ` of `Gamma.lean` is
`KLS.LogConcave.weakGamma_toLp`: for `f, g ∈ C_c^∞` and the unit weight,
`Γ(T̄ [f], T̄ [g]) =ᵐ[ν] gamma f g`. Its input is
`KLS.LogConcave.coeFn_closedWeightedOperator_toLp` (the representative of `T̄` on any test class
is `B ∘ ∇g`) and `coeFn_closedWeightedOperator_toLp_gradient`.

## `W1`: product, chain and weak generator rules

**Test class.** The rules close on the following classes, and the closure hypotheses are the
content of the statements, not decorations:

* `IsTest.apply_mul_ae` (`hac` only): `B ∇(g₁ g₂) =ᵐ[ν] g₁ (B ∇g₂) + g₂ (B ∇g₁)`;
* `IsTest.mul`: the product of two tests is a test **when both are bounded** — without
  boundedness the product need not be Lipschitz and its weighted gradient need not be in `L²`;
* `IsTest.apply_comp_ae` (`hac` and `Φ` differentiable): `B ∇(Φ ∘ g) =ᵐ[ν] Φ'(g) (B ∇g)`;
* `IsTest.comp`: `Φ ∘ g` is a test when `Φ` is `C¹` with `|Φ'| ≤ K` and `Φ 0 = 0`; `Φ 0 = 0`
  is what keeps `Φ ∘ g` square integrable without assuming `g` bounded.

The operator values are `coeFn_operator_mul`, `coeFn_operator_comp` (they need the frontier
hypothesis, exactly as `operator_apply` does) and, for the closure,
`KLS.LogConcave.coeFn_closedWeightedOperator_mul` and `coeFn_closedWeightedOperator_comp`.

**Weak generator.** `WeakGamma.integral_eq_integral_mul_adjointComp` and its concrete form
`KLS.LogConcave.integral_weakGamma_eq_integral_mul_adjointComp`:

`∫ Γ(T̄ f, T̄ x) dν = ∫ (A f) x dν` for `f ∈ D(A)`, `x ∈ D(T̄)`, arbitrary weight `B`,

with `A ≥ 0` and `ℒ = -A`. Only density of `D(T̄)` is used; there is no operator-core claim and
none is needed, because the identity is proved from the defining property of the adjoint and not
from a core approximation. Its compatibility with the classical statement is
`KLS.LogConcave.integral_weakGamma_toLp_eq`: for `f ∈ C_c^∞`, the left-hand side equals
`∫ (-ℒf) x dν` for **every** `x ∈ D(T̄)`, which is strictly more than `G0` gave.
`KLS.LogConcave.exists_closedWeightedOperator_eq_of_tendsto` records that graph-norm limits
identify `T̄` of the limit, so the convergence hypotheses used in `W3` are exactly graph
convergence for `T̄`.

## `W2`: the integrated Bochner inequality

`Analysis.BakryEmery.integral_mul_gammaTwo_nonneg` (classical form): with `μ = m.tilted (-U)`,
`U` `C²` convex, `f` `C³` with compact support, `φ` `C²` with compact support and `φ ≥ 0`,

`0 ≤ (∫ (ℒφ) Γ(f, f) dμ) / 2 - ∫ φ Γ(f, ℒf) dμ`.

The proof is `∫ φ Γ₂(f) dμ ≥ 0` (pointwise `B4`, integrated against `φ ≥ 0`) followed by the new
symmetry `integral_weightedLaplacian_mul_comm`, which moves `ℒ` from `Γ(f, f)` to `φ`. The
integrability of each of the three integrands is proved, not assumed: `Γ(f, f)` is `C²` with
compact support (`contDiff_gamma`, `hasCompactSupport_gamma_left`), `ℒf` is `C¹`
(`contDiff_weightedLaplacian`) with compact support, `ℒφ` is continuous with compact support, so
every integrand is continuous with compact support and `μ` is finite. `Γ(f, f)` is **never**
claimed to be in `L²`.

`integral_mul_weakGamma_nonneg` is the same inequality with the two classical gradients replaced
by arbitrary `L²` fields `u`, `w` representing `∇f` and `-∇(ℒf) = ∇(Af)`:

`0 ≤ (∫ (ℒφ) Γ(u, u) dμ) / 2 + ∫ φ Γ(u, w) dμ`.

The test function `φ` deliberately stays classical. Its role is to be a **bounded** multiplier,
which an abstract `L²` datum is not; replacing `ℒφ` by `A [φ]` would produce an `L²` class with
no bound, and the `L¹` pairing would no longer be justified. This is the "different weak form"
the task allows, and `W3` shows it is exactly the form that survives the limit.

## `W3`: what connects to the heat flow, and what does not

**Proved outright, for the actual semigroup.**

| Statement | Declaration |
| --- | --- |
| `∫ Γ(T̄ (P_t f)) dν ≤ ∫ Γ(T̄ f) dν` for `f ∈ D(T̄)`, `t ≥ 0`, arbitrary `B` | `HeatSemigroup.integral_weakGamma_apply_le` |
| `2t ∫ Γ(T̄ (P_t g)) dν ≤ ‖g‖²` for **arbitrary** `g ∈ L²(ν)`, `t > 0` | `HeatSemigroup.two_mul_integral_weakGamma_apply_le` |
| `∫ Γ(T̄ (P_t g), T̄ x) dν = ∫ (A (P_t g)) x dν` for arbitrary `g`, `t > 0`, `x ∈ D(T̄)` | `HeatSemigroup.integral_weakGamma_apply_eq_integral_mul_adjointComp` |
| **second-order regularity**: `A (P_t g) ∈ D(T̄)` for arbitrary `g`, `t > 0` | `Generated.mem_domain_adjointComp_apply_of_pos`, `HeatSemigroup.mem_closedWeightedOperator_domain_adjointComp_of_pos` |

These are integrated, `L¹` statements. They are **not** pointwise: nothing here bounds
`Γ(T̄ (P_t f))(x)` at a point, and no Jensen-type self-improvement is attempted.

**The extension lemma, with every term checked.**
`Analysis.BakryEmery.integral_mul_weakGamma_nonneg_of_tendsto` and its concrete form
`KLS.LogConcave.integral_mul_weakGamma_adjointComp_nonneg_of_tendsto` prove that the weak `W2`
inequality passes to `L²` limits of the two fields. The norms are named explicitly: it is
`‖u n - u₀‖ → 0` and `‖w n - w₀‖ → 0` in `L²(ν; V)`, nothing weaker. Each term survives because

* `|∫ φ (Γ(u, v) - Γ(u', v'))| ≤ C (‖u - u'‖ ‖v‖ + ‖u'‖ ‖v - v'‖)` with `C` an a.e. bound on the
  multiplier (`WeakGamma.abs_integral_mul_sub_le`), and
* both multipliers, `ℒφ` and `φ`, are continuous with compact support, hence bounded.

For the concrete form the fields of the smooth data are identified:
`KLS.LogConcave.adjointComp_toLp_mem_closedWeightedOperator_domain` proves `A [f] ∈ D(T̄)` and
`coeFn_closedWeightedOperator_adjointComp_toLp` proves that its field is `-∇(ℒf)`, for
`f ∈ C_c^∞` and a `C^∞` potential. The audit's `W3_nonvacuous` discharges the transfer theorem
with the constant sequence, so the statement is not vacuous.

The second-order regularity is new in this round and it removes half of the obstruction listed in
the previous record: it is proved by splitting the time, `A (P_t g) = P_{t/2} (A (P_{t/2} g))` by
`S0a`'s commutation, and then sending the `L²` vector `A (P_{t/2} g)` into `D(T̄)` by `E2`. As a
consequence `HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_tendsto` states the weak `Γ₂`
inequality **for `P_t g` with an arbitrary datum `g` and `t > 0`**, with both fields
`T̄ (P_t g)` and `T̄ (A (P_t g))` supplied by the library and the two `L²` convergences as the
only remaining hypotheses.

**Not proved, and this is the remaining gap.** For `F = P_t g` the two convergence hypotheses are
**not** available. What is missing is a *second-order* approximation property: a sequence
`fₙ ∈ C_c^∞` with

`∇fₙ → T̄ F` and `∇(A fₙ) = -∇(ℒ fₙ) → T̄ (A F)`, both in `L²(ν; V)`.

Graph-norm density of `D(A)` in `D(T̄)` (`F1` of the form-domain round) does **not** supply this:
it controls `u n → F` and `T̄ (u n) → T̄ F`, but says nothing about `A (u n)`, let alone about
`T̄ (A (u n))`. Equivalently, what is missing is that `C_c^∞` is a core of `A` in the graph norm
of the *second-order* operator `x ↦ (x, T̄ x, A x, T̄ (A x))`. This is not proved here, and it is
not packaged as a structure field or a standing hypothesis: it appears as two explicit, visible
convergence hypotheses of the transfer theorems.

## Boundaries

`Γ(u, v)` is `L¹`; it is not in `L²`, `P_t` is not applied to it, and no `L¹` semigroup is
constructed. A continuous representative is not produced and is not claimed to suffice.
`P_t f ∈ D(A)` is not used to conclude anything about `Γ(P_t f)` beyond integrability and the
integrated bounds above. Compact support is not claimed to be preserved by `P_t`. No `Γ₂`
condition, extension or interpolation conclusion is packaged into a structure and then assumed.
The integrated energy contraction is not turned into a pointwise gradient contraction, and no
Jensen step is used to upgrade a square estimate to a first-order one. No default `RCD` identity,
Neumann boundary condition or unformalized literature theorem is used as a proof. Zero `sorry`,
zero custom placeholder axiom, no circular dependency, and no existing public signature is
weakened.

## Sources, with the normalizations actually used

The diffusion convention is Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion
Operators* (Grundlehren 348, 2014): `Γ(f, g) = (ℒ(fg) - fℒg - gℒf)/2`, `Γ₂(f) =
(ℒΓ(f, f))/2 - Γ(f, ℒf)`, generator `ℒ = Δ - ⟪∇U, ∇⟫` for `dν ∝ e^{-U} dx`, and `CD(0, ∞)` for
convex `U`; the weak form `∫ φ Γ₂(f) dν ≥ 0` obtained by integrating against a nonnegative test
and moving `ℒ` onto the test is the standard Γ-calculus formulation used there (§1.16, §3.3).
The sign convention of this repository keeps `A = T̄†T̄ ≥ 0` and `ℒ = -A`, so the generator of
BGL is `ℒ` and the form is `∫ Γ(f, g) dν = ⟪A f, g⟫`, as in the Dirichlet-form presentation of
Fukushima–Ōshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*, §1.3. The target of
the second stage is Ledoux's semigroup proof of Buser's inequality (*A simple analytic proof of
an inequality by P. Buser*, Proc. AMS 121 (1994), 951–959) and, for the constant `π`,
De Ponti–Mondino (*Sharp Cheeger–Buser type inequalities in `RCD(K, ∞)` spaces*, J. Geom. Anal.
31 (2021), 2416–2438). **No step of either paper is used as a proof here**; the citations record
the convention and the target only.

## Validation

`FunctionalInequalities/Analysis/BakryEmery/{Calculus, Laplacian, Gamma, IntegrationByParts,
WeakGamma, IntegratedBochner}.lean`,
`FunctionalInequalities/Energy/WeightedGradient/Leibniz.lean`,
`FunctionalInequalities/KLS/LogConcave/WeightedGradient/Closure.lean`,
`FunctionalInequalities/Analysis/Semigroup/Generated/Smoothing.lean`,
`FunctionalInequalities/KLS/LogConcave/HeatSemigroup/{Domain, Gamma}.lean` and the independent audit
`research/audits/BakryEmeryWeakGammaAudit.lean` are checked with `-DwarningAsError=true`. The
audit restates and **proves** every public conclusion of the round, exercises the zero field, the
zero test function and the reflexive case of the stability estimate, and prints **87 axiom
reports, all standard** (`propext`, `Classical.choice`, `Quot.sound`). The existing deliberate
target warning in `KLS/Target.lean` is outside these proofs. Progress views are regenerated from
a temporary Git index that preserves the real staging area.

Validation logs and the final verification receipt pointer are in
`build/audit/weak-gamma-interface/`. Default `lake build` (3572 jobs) passed. The root
`python3 research/verify.py` was rerun at the **end** of the round, after every documentation
edit, so that its snapshot is the delivered one; the receipt is identified in
`build/audit/weak-gamma-interface/final-snapshot.json`. An earlier receipt of the same day
certifies its own, earlier snapshot and is not quoted as verification of this one.

| Proved | Interface only (explicit assumptions) | Still an informal plan |
| --- | --- | --- |
| `W0` in full; `W1` product/chain rules and the weak generator identity; `W2` classical and weak, with all integrability discharged; the three integrated heat-flow statements; second-order positive-time regularity; the `W3` limit-transfer theorems, including the `P_t g` form | the weak `Γ₂` inequality for `F = P_t g`, which needs the two stated `L²` convergences of the smooth fields | `Γ(P_t f) ≤ P_t Γ(f)`, `|T(P_t f)| ≤ P_t |Tf|`, the `Γ` time interpolation `s ↦ P_s Γ(P_{t-s} f)`, BGL/BV, general-law passage, the constant `π`, Buser, KLS |

## Minimal remaining gap toward the `Γ` time interpolation

1. ~~`A F ∈ D(T̄)` for `F = P_t g`~~ — **proved in this round**
   (`HeatSemigroup.mem_closedWeightedOperator_domain_adjointComp_of_pos`).
2. A **second-order** smooth core: `fₙ ∈ C_c^∞` with `∇fₙ → T̄ F` and `∇(ℒfₙ) → T̄ (A F)` in `L²`.
   This is the genuine obstruction; graph-norm density of `D(A)` in `D(T̄)` is insufficient.
3. With 1 and 2, the weak `Γ₂` inequality holds for `P_s f`, and the interpolation
   `s ↦ ∫ φ Γ(T̄ (P_{t-s} f)) dν` becomes the next object: its differentiability in `s` needs, in
   addition, the product rule for `s ↦ P_s` against the bounded multiplier and a dominated
   convergence step, neither of which this round provides.


## Scope and sign correction after review

2026-09-21. This addendum supersedes the affected wording above while preserving the original
implementation record. The second approximation in the final numbered list must read
`-∇(ℒfₙ) → T̄(AF)`, since `A = -ℒ`. The Lean transfer statements already use that negative
sign correctly. No declaration or proof changes are required.

Weak Γ is guaranteed to be `L¹`, not guaranteed to be `L²`; it can belong to both. Bounded,
a.e. strongly measurable multipliers are sufficient for the current testing API, not necessary
for every individual integrability claim. The implemented product/chain rules, including their
closed-gradient versions, take `IsTest` inputs with the stated additional hypotheses. They do
not yet give these rules for arbitrary form-domain or heat-flow inputs.

The transfer theorem needs two `L²` field convergences. A smooth core controlling all four
components `(f, T̄f, Af, T̄(Af))` would provide them, but is a stronger sufficient result, not an
equivalent formulation established here. Constant-sequence audit examples show applicability
on smooth instances only, not existence of approximants for every heat-flow value.

The next task is to prove the two-field approximation for heat flow under an explicit smooth
convex-potential scope, or prove a sufficient stronger core theorem and its implication.
Γ time interpolation still requires its own test-class, domain, differentiation and endpoint
arguments. Neither the original second-stage gradient estimates nor Buser is complete.

Receipt `20260921T090645.663996Z` belongs to the pre-correction snapshot. This comment and
documentation correction retains all mathematical declarations and proofs; structural checks
and progress regeneration are not a fresh full verification of the edited snapshot.

## Interpolation correction after review

2026-09-22. This addendum supersedes the affected wording above while preserving the original
implementation record. No declaration, statement or proof changes.

Item 3 of the final numbered list names `s ↦ ∫ φ Γ(T̄ (P_{t-s} f)) dν` as the object that follows.
The object the Bakry–Émery argument requires is
`s ↦ ∫ (P_s φ) Γ(T̄ (P_{t-s} f)) dν`,
with the **outer semigroup** applied to the test function; a pairing against a fixed `φ` is a
different functional and does not replace it. Extending the weak `Γ₂` inequality from smooth
compactly supported test functions to the class `{P_s φ}` is therefore a separate proof
obligation, not a formal product-rule computation: `P_s φ` is an `L²` class with no available
classical representative, no compact support and no available boundedness of `ℒ P_s φ`.

Item 2 of that list was superseded earlier by
[the generator form](2026-09-21-generator-gamma-two.md), which removes the second-order field.
The remaining `hcore` hypothesis is reduced — not discharged — by
[the operator-core criterion](2026-09-22-operator-core-criterion.md).

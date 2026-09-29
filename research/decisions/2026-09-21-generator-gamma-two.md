# The generator form of the weak `Γ₂` inequality: `G0`–`G5`

2026-09-21, after the weak `Γ` interface round
(`2026-09-21-weak-gamma-interface.md` and its scope correction). This round attacks the single
obligation that record left open — the **two-field convergence** that the weak `Γ₂` transfer
theorem needs when the datum is `F = P_t g` — and changes what has to be supplied. It preserves
all earlier work, makes no commit or push, does not upgrade Lean/Mathlib, and does **not**
complete Bakry–Émery, Buser or KLS.

**Headline, stated without varnish.** The task asked for smooth compactly supported `fₙ` with
`∇fₙ → T̄ F` *and* `-∇(ℒfₙ) → T̄ (A F)` in `L²(ν; V)` for `F = P_t g`, and for a heat-flow weak
`Γ₂` theorem with no approximation hypothesis. **The second field is now unnecessary** — that
part of the obligation is eliminated, not assumed — but the **first** one is not proved for
`P_t g`, and the heat-flow theorem therefore still carries one hypothesis. What changed is the
nature of that hypothesis: from two `L²` convergences of vector fields, one of them second
order and specific to each `F`, `φ`, `t`, to the single standard operator-theoretic statement
that `C_c^∞(V)` is an operator core of `A = T̄†T̄`. Section 6 says exactly what is and is not
proved, and section 7 records the obstruction.

## 1. The setting, stated in full

`V` is a finite-dimensional real inner product space with its Borel structure
(`[CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
[FiniteDimensional ℝ V]`), `m` is a Haar measure on `V`, and `ν : ProbabilityMeasure V` is
full-dimensional log-concave (`hν : LogConcave ν`,
`hi : (interior (ν : Measure V).support).Nonempty`) with `(ν : Measure V) = m.tilted (-U)`.

`T = hν.weightedOperator m B hi` is the weighted gradient on Lipschitz `L²` tests,
`T̄ = hν.closedWeightedOperator m B hi` its closure, `A = adjointComp T̄ = T̄†T̄` the
**nonnegative** generator, `ℒ = -A`, and `P_t = HeatSemigroup.operator m B hν hi ht`.

Regularity is stated per theorem and never globally:

| Result | weight `B` | `U` | test `φ` |
| --- | --- | --- | --- |
| bounded multipliers on `L²` (`G0`) | — | — | any a.e. bounded multiplier |
| `L¹` pairing and its stability (`G1`) | — | — | any a.e. bounded field on the right |
| Leibniz for `T̄` against a multiplier (`G2`) | arbitrary | none | `C^∞`, compact support |
| elimination of the second field (`G3`) | arbitrary | none | `C^∞`, compact support |
| generator form on `C_c^∞`, transfer (`G4`) | `B = I` | `C^∞`, `ConvexOn ℝ Set.univ U` | `C^∞`, compact support, `φ ≥ 0` |
| heat flow under the core hypothesis (`G5`) | `B = I` | `C^∞` convex | `C^∞`, compact support, `φ ≥ 0` |

Convexity of `U` enters only where the pointwise Bochner inequality is used, i.e. in `G4`–`G5`.
`C^∞` for `U` is required exactly where `-ℒf` must itself be a smooth compactly supported test,
which is what `KLS.LogConcave.adjointComp_toLp_mem_closedWeightedOperator_domain` needs. No
global bound on any derivative of `U` is assumed anywhere, and none is used.

## 2. Placement plan (recorded before editing)

| Item | Object and role | Destination | Decision |
| --- | --- | --- | --- |
| `G0` multiplication of an `L²` class by an a.e. bounded scalar or vector multiplier | generic `L²` construction, no measure-space or differential content | `L2/BoundedMultiplier.lean` | **create**: the `L2` family owns bare `L²` constructions (`MeanVariance.lean`, `Transport.lean`); this one has no gradient, no measure hypothesis and no potential, so it must not live in `Energy/` or `Analysis/BakryEmery/` |
| `G1` pairing an `L²` multiplier with a weak `Γ` whose right field is a.e. bounded | the weak `Γ` object and its `L¹` theory | `Analysis/BakryEmery/WeakGamma.lean` | **extend**: same object, same role as the existing `integrable_mul` / `abs_integral_mul_sub_le` / `tendsto_integral_mul` group. The two Cauchy–Schwarz helpers are generalized in place to two different value spaces — a strictly weaker hypothesis, no signature is weakened and every existing call site keeps its meaning |
| the three-term transfer lemma | the transfer engine of the integrated inequality | `Analysis/BakryEmery/IntegratedBochner.lean` | **extend**: that module already owns `integral_mul_weakGamma_nonneg_of_tendsto`, the two-field transfer; the generator-form transfer is its sibling and is equally measure-theoretic (no potential, no convexity, no semigroup) |
| `G2` smooth graph core of `T̄` in sequential form, and the Leibniz rule for `T̄` against a `C_c^∞` multiplier | elementary properties of the **closed** weighted gradient | `KLS/LogConcave/WeightedGradient/Multiplier.lean` | **create**: `Closure.lean` owns closedness, the dense domain and the test-class values of `T̄` and must not acquire `L2/BoundedMultiplier` and `Energy/Relaxation` dependencies; `Energy/WeightedGradient/Leibniz.lean` owns the **test-class** rules and is deliberately free of `LogConcave`. Multiplication by a test on the whole form domain is a third responsibility |
| `G3`–`G4` the identity, the generator form, its transfer, the class stability | substantive theorems about `T̄` and `A` in the tilted model | `KLS/LogConcave/HeatSemigroup/GammaTwo.lean` | **create**: `HeatSemigroup/Gamma.lean` owns the `Γ`-level interfaces and the two-field transfer; the `Γ₂` identity and the generator-form inequality have different imports (`Multiplier.lean`) and a different content, and `Gamma.lean` is left untouched |
| `G5` the heat-flow frontend | concrete specialization | `KLS/LogConcave/HeatSemigroup/GammaTwo.lean`, namespace `HeatSemigroup` | **extend** the new module: the frontend is one instantiation of `G4` and shares all of its imports |

No empty module, compatibility alias or old-path wrapper was created. No existing statement was
weakened or renamed. `FunctionalInequalities.lean` gains the three new leaves.

## 3. `G0`: bounded multipliers on `L²`

`L2/BoundedMultiplier.lean` packages the two multiplications a closed differential operator
needs, as continuous linear maps so that `map_sub` and the operator bound come for free:

* `L2.bddSmulL hc hM : Lp H 2 μ →L[ℝ] Lp H 2 μ`, `u ↦ [x ↦ c x • u x]`, for an a.e. strongly
  measurable `c` with `|c| ≤ M` a.e.;
* `L2.bddSmulRightL hβ hM : Lp ℝ 2 μ →L[ℝ] Lp H 2 μ`, `u ↦ [x ↦ u x • β x]`, for an a.e.
  bounded field `β`.

Each comes with `memLp_*`, `coeFn_*` (the representative), `norm_*ₗ_le` and `norm_*L_sub_le`
(the bound `|M|`, which is a bound and **not** claimed to be the operator norm). Both are stated
for the exponent `2` only, which is the only case used.

## 4. `G1`: pairing an `L²` multiplier with a bounded field

`WeakGamma.apply u β` is `L¹` when `u, β ∈ L²`, and it is in `L²` when `β` is a.e. bounded. The
new group in `Analysis/BakryEmery/WeakGamma.lean` uses only the second, weaker fact and never
names an `L²` class for `Γ`:

| Obligation | Declaration |
| --- | --- |
| `a · Γ(u, β) ∈ L¹` for `a ∈ L²` and `β` a.e. bounded | `WeakGamma.integrable_mul_of_bdd_right` |
| its `L¹` stability in `‖a - a'‖` and `‖u - u'‖` | `WeakGamma.abs_integral_mul_sub_le_of_bdd_right` |
| the resulting limit transfer | `WeakGamma.tendsto_integral_mul_of_bdd_right` |
| `Γ(a, a) = a²` for a scalar class | `WeakGamma.apply_self_real` |
| mixed-space Cauchy–Schwarz for the pointwise norms | `WeakGamma.integrable_norm_mul_norm`, `integral_norm_mul_norm_le` (generalized to two value spaces) |

The boundedness hypothesis is on `β`, not on `a`: `a` is the generator image `A F`, which is an
arbitrary `L²` class, and no bound on it is available or used.

## 5. `G2`: the Leibniz rule for `T̄` on the whole form domain

Two statements in `KLS/LogConcave/WeightedGradient/Multiplier.lean`, for an arbitrary weight `B`:

* `exists_seq_smooth_tendsto_graph`: every `x ∈ D(T̄)` is a **graph-norm** limit of smooth
  compactly supported classes, `[gₙ] → x` and `[B ∇gₙ] → T̄ x` in `L²`. This is the sequential
  form of `closure_domRestrict_eq_of_smoothCore_le`, obtained through
  `Energy.mem_graph_topologicalClosure_iff`; it controls the function and its **first**
  derivative only.
* `exists_mem_domain_closedWeightedOperator_toLp_mul`, with its two clauses
  `toLp_mul_mem_closedWeightedOperator_domain` and `coeFn_closedWeightedOperator_toLp_mul`: for
  `φ ∈ C_c^∞(V)` and **every** `x ∈ D(T̄)`, `[φ x] ∈ D(T̄)` and
  `T̄ (φ x) = φ (T̄ x) + x (B ∇φ)` almost everywhere.

The second is a genuine extension of the test-class rule `IsTest.apply_mul_ae`, which the
previous record explicitly flagged as **not** available for arbitrary form-domain inputs. The
proof applies the classical product rule to `φ gₙ`, notes that `φ` and `B ∇φ` are bounded with
compact support so that multiplication by either is a bounded operator on `L²` (`G0`), and lets
closedness of `T̄` absorb the limit. No boundedness, continuity or differentiability of `x` is
assumed.

## 6. `G3`–`G5`: what is proved, and the one hypothesis that remains

**`G3`, the identity that removes the second-order field.** For `F ∈ D(A)` with `A F ∈ D(T̄)`,
arbitrary weight `B` and `φ ∈ C_c^∞(V)`
(`KLS.LogConcave.integral_mul_weakGamma_adjointComp_eq`):

`∫ φ Γ(T̄ F, T̄ (A F)) dν = ∫ φ (A F)² dν - ∫ (A F) Γ(T̄ F, T̄ φ) dν`.

Its proof pairs `T̄ F` against `T̄ (φ (A F))`: `G2` splits that field into `φ (T̄ (A F))` and
`(A F) (B ∇φ)`, and the weak integration by parts of `Gamma.lean` evaluates the pairing as
`∫ (A F) (φ (A F)) dν`. Integrability of each of the three integrands is proved, not assumed.
The sign is checked separately in the audit (`G3_sign`), because `A = -ℒ` makes it easy to get
wrong: the `Γ(T̄ F, T̄ φ)` term is **subtracted**.

**`G4`, the generator form and its transfer.**

* `integral_mul_sq_adjointComp_toLp_nonneg`: for `f, φ ∈ C_c^∞(V)`, `φ ≥ 0`, `U` `C^∞` convex,
  `B = I`,
  `0 ≤ (∫ (ℒφ) Γ(T̄ f, T̄ f) dν)/2 + ∫ φ (A f)² dν - ∫ (A f) Γ(T̄ f, T̄ φ) dν`.
  This is the previous round's `integral_mul_weakGamma_nonneg` with `G3` applied; no new
  analytic input.
* `integral_mul_sq_adjointComp_nonneg_of_tendsto`: the same inequality at any
  `F ∈ D(A)` for which there are `fₙ ∈ C_c^∞(V)` with **`[fₙ] → F` and `A [fₙ] → A F` in `L²`**.
  Convergence of `T̄ fₙ` is *derived* inside the proof from `‖T̄ y‖² = ⟪A y, y⟫`, not assumed.
  No second-order field occurs in the hypotheses or in the conclusion.
* `integral_mul_weakGamma_adjointComp_nonneg_of_graph_tendsto`: the **two-field** conclusion
  `0 ≤ (∫ (ℒφ) Γ(T̄ F, T̄ F) dν)/2 + ∫ φ Γ(T̄ F, T̄ (A F)) dν` under the same two hypotheses, for
  any `F ∈ D(A)` with `A F ∈ D(T̄)`. Compared with
  `HeatSemigroup/Gamma.lean`'s `integral_mul_weakGamma_adjointComp_nonneg_of_tendsto`, the
  hypothesis `-∇(ℒ fₙ) → T̄ (A F)` is **gone**, and `∇fₙ → T̄ F` is replaced by the weaker pair
  `[fₙ] → F`, `A [fₙ] → A F`.
* `exists_seq_smooth_tendsto_adjointComp_toLp` and
  `exists_seq_smooth_tendsto_adjointComp_of_tendsto`: the class of admissible `F` contains every
  smooth compactly supported class (constant sequence) and is closed for the graph norm of `A`.
  Together these say that it is exactly the domain of the **closure of `A` restricted to
  `C_c^∞(V)`**, a closed operator extending the classical `-ℒ`. It is **not** claimed to be all
  of `D(A)`.

**`G5`, the heat flow.** `HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`: for an
arbitrary `g ∈ L²(ν)` and every `t > 0`,

`0 ≤ (∫ (ℒφ) Γ(T̄ (P_t g), T̄ (P_t g)) dν)/2 + ∫ φ Γ(T̄ (P_t g), T̄ (A (P_t g))) dν`,

under the single hypothesis `hcore`: every `y ∈ D(A)` is a graph limit of smooth compactly
supported classes for `A`. Everything else is proved: `P_t g ∈ D(A)` and `A (P_t g) ∈ D(T̄)`
come from positive-time smoothing, and all integrabilities are discharged.

`hcore` is a property of the model. It mentions no `φ`, no `g`, no `t`, and no second-order
field. It is the statement that `C_c^∞(V)` is an **operator core** of `A = T̄†T̄`, equivalently
that `ℒ = Δ - ⟪∇U, ∇·⟫` is essentially self-adjoint on `C_c^∞(V)` in `L²(ν)`. It is a visible
hypothesis of one theorem; it is not packaged into a structure, not made an instance, and not
used anywhere else.

## 7. The obstruction, and the routes that were considered and rejected

`hcore` is not proved here, and the honest reason is that it is a genuine theorem about
Dirichlet operators, not a missing lemma.

* **Form core is not operator core.** `C_c^∞(V)` is a core of `T̄` (this is
  `closure_domRestrict_eq_of_smoothCore_le`, and it is what `G2` uses). That gives `[fₙ] → F`
  and `T̄ fₙ → T̄ F` and nothing about `A fₙ`. Graph-norm density of `D(A)` in `D(T̄)` (`F1`)
  is likewise first order in the wrong operator.
* **Weak convergence does not suffice, and the convexity of the missing term points the wrong
  way.** With only `sup ‖A fₙ‖ < ∞` one gets `A fₙ ⇀ A F`, and then
  `∫ φ (A fₙ)² dν` is weakly lower semicontinuous. It enters the inequality with a `+` sign, so
  lower semicontinuity gives `Q(F) ≤ liminf Q(fₙ)`, which is the useless direction. Mazur's
  lemma would upgrade a bounded sequence to convex combinations converging strongly, but since
  the graph of `A|_{C_c^∞}` is a linear subspace its weak and strong closures coincide, so this
  route defines the *same* class and adds nothing.
* **Truncation and mollification are blocked by the second-order terms.** For `f = χ (ρ_ε * F)`
  the quantity `ℒ f` needs `∇²F ∈ L²_loc`, i.e. interior `H²` elliptic regularity for
  `div(e^{-U} ∇·)`, which Mathlib does not have and which this round does not attempt; the
  truncation commutator `⟪∇U, ∇χ⟫` is additionally unbounded for a general smooth convex `U`,
  exactly as the task warned.
* **Essential self-adjointness itself.** Under the unitary map `f ↦ f e^{-U/2}` the operator
  becomes `-Δ + (|∇U|²/4 - ΔU/2)` on `L²(dx)`; essential self-adjointness on `C_c^∞` is then a
  Kato–Rellich/Faris–Lavine type theorem. Nothing of this is in Mathlib, and no step of it is
  used or assumed here.

So the round delivers an unconditional theorem on the domain of the minimal closed extension of
`-ℒ`, and a conditional theorem for the heat flow whose condition is one standard, clearly
named property. It does **not** deliver the unconditional heat-flow weak `Γ₂` inequality.

## 8. Boundaries

`Γ(u, v)` is `L¹`; it is in `L²` only when one field is a.e. bounded, which is used solely for
`β = T̄ φ` with `φ ∈ C_c^∞`. No `L¹` semigroup is constructed and `P_t` is never applied to a
`Γ`. A classical or smooth representative of `P_t g` is not produced and not claimed to exist.
Compact support is not claimed to be preserved by `P_t`. No `Γ₂` condition, extension or
interpolation conclusion is packaged into a structure and then assumed. The integrated energy
contraction is not turned into a pointwise gradient contraction, and no Jensen step is used. No
default `RCD` identity, Neumann boundary condition or unformalized literature theorem is used as
a proof. Zero `sorry`, zero custom axiom, no circular dependency, and no existing public
signature weakened. The deliberate `KLS/Target.lean` hole is unchanged and untouched.

## 9. Sources, with the normalizations actually used

Conventions are Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators*
(Grundlehren 348, 2014): `Γ(f, g) = (ℒ(fg) - fℒg - gℒf)/2`,
`Γ₂(f) = (ℒΓ(f, f))/2 - Γ(f, ℒf)`, generator `ℒ = Δ - ⟪∇U, ∇⟫` for `dν ∝ e^{-U} dx`, and
`CD(0, ∞)` for convex `U`. The repository keeps `A = T̄†T̄ ≥ 0` and `ℒ = -A`, so the Dirichlet
form is `∫ Γ(f, g) dν = ⟪A f, g⟫` as in Fukushima–Ōshima–Takeda, *Dirichlet Forms and Symmetric
Markov Processes*, §1.3. The `algebra 𝒜₀` that BGL assumes (stable under the semigroup and under
`ℒ`) is precisely what `hcore` would provide and what is **not** available here; BGL assumes it,
it does not prove it. Essential self-adjointness of Dirichlet operators and its counterexamples
are the subject of A. Eberle, *Uniqueness and Non-Uniqueness of Semigroups Generated by Singular
Diffusion Operators* (LNM 1718, 1999). The target of the second stage remains Ledoux's semigroup
proof of Buser's inequality (Proc. AMS 121 (1994), 951–959) and, for the constant `π`,
De Ponti–Mondino (J. Geom. Anal. 31 (2021), 2416–2438). **No step of any of these papers is used
as a proof here**; the citations record conventions, the target and the status of the missing
hypothesis.

## 10. Validation

New: `FunctionalInequalities/L2/BoundedMultiplier.lean`,
`FunctionalInequalities/KLS/LogConcave/WeightedGradient/Multiplier.lean`,
`FunctionalInequalities/KLS/LogConcave/HeatSemigroup/GammaTwo.lean`, audit
`research/audits/BakryEmeryGeneratorGammaTwoAudit.lean`.
Extended: `FunctionalInequalities/Analysis/BakryEmery/WeakGamma.lean`,
`FunctionalInequalities/Analysis/BakryEmery/IntegratedBochner.lean`,
`FunctionalInequalities.lean`.
All are checked with `-DwarningAsError=true`. The audit restates and **proves** every public
conclusion of the round, exercises the zero multiplier, the reflexive case of the stability
estimate, the sign of the subtracted term, the constant sequence and the consistency of the
transfer theorem with the smooth case, and prints **59 axiom reports, all standard**
(`propext`, `Classical.choice`, `Quot.sound`). The previous round's audit
`research/audits/BakryEmeryWeakGammaAudit.lean` is rerun unchanged and stays clean, which is the
check that generalizing the two Cauchy–Schwarz helpers weakened nothing. Default `lake build`
passes with the single deliberate `KLS/Target.lean` warning. Progress views are regenerated from
a temporary Git index that preserves the real staging area, and the root
`python3 research/verify.py` is rerun at the **end** of the round so that its snapshot is the
delivered one.

| Proved | Interface only (explicit assumptions) | Still an informal plan |
| --- | --- | --- |
| `G0`–`G3` in full; the generator form on `C_c^∞`; its transfer along first-order graph convergence for `A`; the two-field conclusion under the same hypotheses; stability and non-vacuity of the approximation class | the heat-flow weak `Γ₂` inequality, which needs `hcore`: `C_c^∞(V)` is an operator core of `A` | essential self-adjointness of `ℒ` on `C_c^∞`, interior `H²` regularity, `Γ(P_t f) ≤ P_t Γ(f)`, the `Γ` time interpolation, BGL/BV, general-law passage, the constant `π`, Buser, KLS |

## 11. Minimal remaining obligations toward the `Γ` time interpolation

1. ~~`A F ∈ D(T̄)` for `F = P_t g`~~ — proved in the previous round.
2. ~~a **second-order** smooth core (`∇fₙ → T̄ F` and `-∇(ℒfₙ) → T̄ (A F)`)~~ — **no longer
   needed**: `G3` removes the second field from the inequality.
3. `hcore`: `C_c^∞(V)` is an operator core of `A`, i.e. `ℒ` is essentially self-adjoint on
   `C_c^∞(V)` in `L²(ν)` for a smooth convex `U`. This is the whole remaining gap between `G5`
   and an unconditional heat-flow weak `Γ₂` inequality.
4. With 3, the interpolation `s ↦ ∫ φ Γ(T̄ (P_{t-s} f)) dν` becomes the next object; its
   differentiability in `s` needs, in addition, the product rule for `s ↦ P_s` against a bounded
   multiplier and a dominated convergence step, neither of which this round provides.

## Comparison and interpolation correction after review

2026-09-22. This addendum supersedes the affected wording above while preserving the original
implementation record. No declaration, statement or proof changes.

1. **The two hypothesis sets are not comparable as stated.** Section 6 describes the pair
   `[fₙ] → F`, `A [fₙ] → A F` as a *weaker* replacement for `∇fₙ → T̄ F`. That comparison is not
   proved and should not be made. What is proved is that the generator-graph pair is **sufficient**
   for the transfer theorem, and that it makes the second-order field `-∇(ℒ fₙ) → T̄ (A F)`
   unnecessary. Whether generator-graph convergence implies, is implied by, or is independent of
   the earlier two-field condition is an open question about the operators involved; the correct
   description of the change is "a different, self-contained sufficient condition that eliminates
   the second field", not "a weaker assumption".
2. **The interpolation carries the outer semigroup.** Item 4 of section 11 names
   `s ↦ ∫ φ Γ(T̄ (P_{t-s} f)) dν` as the next object. The object the Bakry–Émery argument actually
   requires is
   `s ↦ ∫ (P_s φ) Γ(T̄ (P_{t-s} f)) dν`,
   with `P_s` applied to the test function. A pairing against a **fixed** `φ` is a different
   functional and does not replace it. Consequently, extending the weak `Γ₂` inequality from
   smooth compactly supported test functions to the class `{P_s φ}` is a separate proof
   obligation — `P_s φ` is an `L²` class with no available classical representative, no
   compact support and no available boundedness of `ℒ P_s φ` — and it is not discharged by a
   formal product-rule computation. Item 4 must also not be read as claiming that a single
   dominated-convergence step separates `hcore` from the interpolation.

The status of `hcore` itself is updated by the following round: see
[the operator-core criterion](2026-09-22-operator-core-criterion.md), which proves the global
cutoff half and reduces `hcore` to interior elliptic regularity. `hcore` remains unproved.

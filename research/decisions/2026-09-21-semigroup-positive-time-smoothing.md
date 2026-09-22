# Positive-time smoothing for `P_t = exp (-t T†T)` (E0–E5)

2026-09-21, stage two after the form-domain round
(`2026-09-20-semigroup-form-domain-stability.md`). This round closes the two statements that
both previous audits carried as **type-checked candidates only**: for an *arbitrary* datum and
every positive time, the generated semigroup value lies in the form domain and in the generator
domain, with explicit constants. It preserves all earlier work, makes no commit or push, does not
upgrade Lean/Mathlib, and does not complete Bakry–Émery, Buser or KLS.

## Placement plan (recorded before editing)

| Item | Object and role | Destination | Decision |
| --- | --- | --- | --- |
| Bounded dissipation estimates | quadratic forms along `u ↦ exp (-u • L) y` for bounded symmetric `L`; reusable analytic tool | `Analysis/Semigroup/Exponential/Dissipation.lean` | **create**: `Exponential/Contraction.lean` owns the first-order version and `S5` verbatim with its route wrapper, and explicitly advertises symmetry of `L` as unused; the new estimates need symmetry and three derivative lemmas of their own |
| `LinearPMap` witness glue | `S` on a difference; a closed operator absorbs graph limits | `Analysis/Semigroup/AdjointClosure.lean` | **extend**: that module already owns graph/closure limit arguments for partially defined operators. `Generated/FormDomain.lean` now uses the shared `apply_sub_of_eq_sub` instead of its private copy (proof-only change) |
| E0–E4 | `P_t` mapping arbitrary `H₀` data into `D(T)` and `D(T†T)` | `Analysis/Semigroup/Generated/Smoothing.lean` | **create**: `Generated/Domain.lean` owns the operator domain and `Generated/FormDomain.lean` the form domain, both for data already in a domain; the new statements need the Yosida limit passage and both earlier modules |
| E5 | concrete specialization, arbitrary weight `B` | `KLS/LogConcave/HeatSemigroup/Domain.lean` | **extend**: that module is the concrete domain frontend; its docstring now separates generator-domain, form-domain and positive-time interfaces |

No empty module, compatibility alias or old-path wrapper was created; no existing statement,
parameter list or namespace was changed. `FunctionalInequalities.lean` gains the two new leaves.

## Statements

Write `A = adjointComp T = T†T` and `P_t = Generated.apply T hT hd t`, `L_s = yosida T hT hs`.

| Obligation | Public declaration | Exact scope |
| --- | --- | --- |
| E0 | `Generated.two_mul_norm_map_apply_sq_le_sub` | `f ∈ D(A)`, `t ≥ 0`: `2t‖T(P_t f)‖² ≤ ‖f‖² - ‖P_t f‖²` |
| E1 | `Generated.two_mul_norm_adjointComp_apply_sq_le_sub` | `f ∈ D(A)`, `t ≥ 0`: `2t‖A(P_t f)‖² ≤ ‖Tf‖² - ‖T(P_t f)‖²` |
| E2 | `Generated.mem_domain_apply_of_pos`, `two_mul_norm_map_apply_sq_le`, `exists_mem_domain_apply_of_pos` | **every** `g : H₀`, `t > 0`: `P_t g ∈ D(T)` and `2t‖T(P_t g)‖² ≤ ‖g‖²` |
| E3 | `Generated.exists_mem_adjointComp_domain_apply_of_mem_domain` | `f ∈ D(T)`, `t > 0`: `P_t f ∈ D(A)` and `2t‖A(P_t f)‖² ≤ ‖Tf‖²` |
| E4 | `Generated.mem_adjointComp_domain_apply_of_pos`, `mul_norm_adjointComp_apply_le`, `exists_mem_adjointComp_domain_apply_of_pos` | **every** `g : H₀`, `t > 0`: `P_t g ∈ D(A)` and `t‖A(P_t g)‖ ≤ ‖g‖` |
| E5 | `KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_of_pos`, `two_mul_norm_closedWeightedOperator_sq_le`, `mem_adjointComp_domain_of_pos`, `mul_norm_adjointComp_le` | E2 and E4 for the closed weighted operator, arbitrary weight `B` |

Supporting public theorems: in `Exponential/Dissipation.lean` the commutation
`exp_neg_smul_apply_comm`, the three derivative lemmas `hasDerivAt_exp_neg_smul_apply`,
`hasDerivAt_norm_exp_neg_smul_sq`, `hasDerivAt_inner_exp_neg_smul`, and the two estimates
`two_mul_inner_exp_neg_smul_le`, `two_mul_norm_apply_exp_neg_smul_sq_le`; in
`AdjointClosure.lean` the glue `apply_sub_of_eq_sub` and the graph-limit tool
`exists_mem_domain_apply_eq_of_tendsto`; in `Generated/Smoothing.lean` the three sequential
Yosida limits `tendsto_exp_neg_smul_yosida`, `tendsto_yosida_apply`,
`tendsto_yosida_exp_neg_smul_apply`.

## Constants, stated honestly

E2 gives `‖T(P_t g)‖ ≤ ‖g‖ / √(2t)` and E4 gives `‖A(P_t g)‖ ≤ ‖g‖ / t`. The sharp scalar maxima
`sup_{λ≥0} λ exp(-2tλ) = 1/(2et)` and `sup_{λ≥0} λ² exp(-2tλ) = 1/(et)²` are **not** formalized,
so the sharp constants `1/√(2et)` and `1/(et)` remain unproved. The `1/(et)` form that the `S0a`
audit type-checked is therefore still a candidate; the audit of this round type-checks it again
in the equivalent shape `exp(1) · t · ‖A(P_t g)‖ ≤ ‖g‖` and does not prove it.

## Proofs

**The bounded level.** For `L` bounded and symmetric, `v u = exp (-u • L) y`, write
`N u = ‖v u‖²`, `Φ u = ⟪L (v u), v u⟫`, `M u = ‖L (v u)‖²`. Differentiating the orbit
(`hasDerivAt_exp_smul_apply` of `Exponential/Contraction.lean`, with `L (v u) = v_{Ly} u` from
`exp_neg_smul_apply_comm`) gives `N' = -2Φ`, `Φ' = -2M` and `M' = -2⟪L (L v), L v⟫`. Hence

* `θ u = N 0 - N u - 2u Φ u` has `θ 0 = 0` and `θ' u = 4u M u ≥ 0`;
* `σ u = Φ 0 - Φ u - 2u M u` has `σ 0 = 0` and `σ' u = 4u ⟪L (L v), L v⟫ ≥ 0` when `L ≥ 0`.

In both the two first-order terms cancel exactly, which is why these are genuine second-order
statements; `monotoneOn_of_deriv_nonneg` on `Set.Ici 0` finishes. Spectrally both are
`1 - exp(-x) ≥ x exp(-x)`, once for the norm and once for the form. No square root of `L`, no
spectral calculus and no functional calculus is used.

**E0–E1.** Apply the two bounded estimates to `L_s` (symmetric by `Y2`, nonnegative by `Y1`) and
let `s ↓ 0` along `s_n = 1/(n+1)`. The three sequential limits needed are `S6`
(`exp (-t • L_{s_n}) f → P_t f`), `Y5` (`L_{s_n} f → A f`) and the mixed one
`L_{s_n} (exp (-t • L_{s_n}) f) = exp (-t • L_{s_n}) (L_{s_n} f) → P_t (A f)`, which follows from
the other two plus the contraction `S5`. `le_of_tendsto_of_tendsto'` transports each inequality,
and `V1` together with `S0a`'s `generator_comm` rewrites `⟪P_t (A f), P_t f⟫ = ‖T (P_t f)‖²` and
`‖P_t (A f)‖ = ‖A (P_t f)‖`.

**E2–E4.** Each estimate applied to *differences* is a Cauchy estimate. For E2 take
`u n ∈ D(A)` with `u n → g` (density of `D(A)`): `2t‖T(P_t u n) - T(P_t u m)‖² ≤ ‖u n - u m‖²`, so
`T (P_t u n)` converges, and `exists_mem_domain_apply_eq_of_tendsto` with closedness of `T`
identifies the limit. For E3 take the graph-norm approximants of `F1` and use closedness of `A`,
which holds because `A` is self-adjoint (`IsSelfAdjoint.isClosed`). E4 composes the two through
`P_t = P_{t/2} P_{t/2}`: `t‖T(P_{t/2} g)‖² ≤ ‖g‖²` and `t‖A(P_t g)‖² ≤ ‖T(P_{t/2} g)‖²` multiply
to `t²‖A(P_t g)‖² ≤ ‖g‖²`.

**E5** is one `exact` per statement, with the concrete object's full hypotheses preserved and an
arbitrary weight `B`.

## Boundaries

E0–E1 allow `t = 0`; E2–E5 need `t > 0`, and that is not an artifact: at `t = 0` an arbitrary `L²`
datum has no reason to lie in `D(T)`. The zero vector is allowed and audited. Nothing here
produces a **classical** representative of `P_t g`: the conclusions are membership in `D(T)` and
`D(T†T)` with norm bounds on `T (P_t g)` and `T†T (P_t g)` in the closed-operator sense. No
operator-core claim, no pointwise gradient, no `Γ`-calculus. No axiom, `sorry`,
conclusion-bearing structure, circular dependency or unresolved analytic hypothesis is
introduced, and no existing public theorem is weakened.

Still unproved: a continuous or smooth representative of `P_t g` for `t > 0`, the sharp constants,
gradient commutation, the square estimate `Γ(P_t f) ≤ P_t Γ(f)` and its `L¹` self-improvement,
BGL, small-time BV bounds, general-law passage and Buser's inequality. Bakry–Émery stays partial;
the full Cheeger–Buser comparison and the dimension-free KLS bound stay pending, and the constant
`π` is not approached.

| 已有证明 | 仅类型检查 | 仍是非形式化方案 |
| --- | --- | --- |
| E0–E5, including arbitrary weights, the zero vector and `t = 0` for E0–E1; the bounded dissipation estimates and the two generic `LinearPMap` tools | the sharp generator bound `exp(1)·t·‖A(P_t g)‖ ≤ ‖g‖` | classical/smooth representatives, `Γ(P_t f) ≤ P_t Γ(f)`, BGL/BV, general-law passage, Buser |
| Earlier `S0a` `D0`–`D4`, `F0`–`F4`, `G0`/`G1`, pointwise `B0`–`B4` | earlier route candidates remain candidates | time differentiation of `s ↦ P_s Γ(P_{t-s} f)` and interchange with derivatives, integrals and limits |

## Next stage

With `Generated.mem_adjointComp_domain_apply_of_pos` the semigroup now maps **all** of `H₀` into
`D(T†T)` for `t > 0`, so `S0a`'s commutation and right time derivative apply to `P_t g` for
arbitrary `g`, and `F2`/`F3` apply to `T (P_t g)`. The two facts a third stage can use directly are
that pairing, and the quantitative `mul_norm_adjointComp_apply_le` / `two_mul_norm_map_apply_sq_le`
bounds, which give the `1/t` and `1/√t` blow-up rates needed for a time-interpolation argument.
The remaining obstruction on the Bakry–Émery route is unchanged and is *not* a domain question any
more: it is the passage from the pointwise `Γ₂ ≥ 0` of `Analysis/BakryEmery/Bochner.lean` to a
statement about `P_t`, i.e. a classical representative for `P_t g` plus differentiation of
`s ↦ P_s Γ(P_{t-s} f)`.

## Validation

Validation logs and the final verification receipt pointer are in
`build/audit/semigroup-smoothing/`. The two new modules, the three extended modules and the
independent audit `research/audits/SemigroupSmoothingAudit.lean` are checked with
`-DwarningAsError=true`; that audit restates E0–E5 in full, proves each one, exercises the zero
vector, and prints 43 axiom reports, all standard-only (`propext`, `Classical.choice`,
`Quot.sound`). The existing deliberate target warning in `KLS/Target.lean` is outside these
proofs. Progress views are regenerated from a temporary Git index that preserves the real
staging area.


## Scope correction after independent review

2026-09-21. This addendum supersedes the scope wording in “Next stage” above without
rewriting the implementation record. “Stage two” there names the positive-time regularization
substage E0–E5; it does not mean that the original second-stage square and first-order
pointwise gradient-estimate targets have been proved.

The assertion that the remaining obstruction is “not a domain question any more” is too broad.
E0–E5 put `P_t g` in `D(A)` and `D(T)` at positive times. They do not establish integrability
or appropriate operator domains for `Γ(P_t f)`, product/chain rules, the Γ interpolation
derivative, or the interchange of limits and integrals. In particular, a form-domain gradient
is in `L²`, whereas its squared norm is generally only in `L¹`; applying the current `L²`
semigroup to that square requires a justified extension or a suitable weak formulation.

A classical route must supply sufficient differentiability, not merely a continuous
representative. Alternatively, a weak Γ route may avoid constructing classical smooth
representatives. In either case the bridge from pointwise Bochner to the actual closed-form
semigroup remains to be proved, followed by the square and first-order gradient estimates.
Also, F2/F3 apply to `P_t g` as a form-domain input, not to `T(P_t g)`, which lives in the
operator's target space. The `1/√(2t)` and `1/t` estimates remain unchanged and are not claimed
to be sharp. No mathematical statement, proof or completion marker changes in this correction.

The prior independent receipt `20260921T074919.898873Z` certifies its recorded snapshot;
this documentation/comment correction changes source hashes. Structural metadata and generated
progress checks for the correction are separate from a fresh Lean/kernel verification.

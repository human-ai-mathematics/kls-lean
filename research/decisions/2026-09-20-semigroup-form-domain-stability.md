# Bakry–Émery form-domain stability and energy contraction (F0–F4)

2026-09-20, after `S0a` (`2026-09-20-semigroup-domain-stability.md`). This round extends the
gradient interface of the generated semigroup from the operator domain `D(T†T)` to the whole form
domain `D(T)`, for closed densely defined `T : H₀ ⇀ H₁` between real Hilbert spaces and for the
concrete closed weighted gradient with an arbitrary weight `B`. It preserves all earlier work,
makes no commit or push, does not upgrade Lean/Mathlib, and does not complete Bakry–Émery,
Buser or KLS.

## Placement plan (recorded before editing)

| Item | Object and role | Destination | Decision |
| --- | --- | --- | --- |
| Graph-norm resolvent limits | `s ↓ 0` limits of `J_s` measured in the graph norm of `T`; substantive theorems, adjoint-free | `Analysis/Semigroup/Resolvent/Limit.lean` | **extend**: same object (`resolventDomain`), same role (resolvent convergence, `R1`–`R3`), same dependency level, and the proofs reuse `norm_resolventCLM_sub_sq_eq` of that module |
| `⟪T†T x, x⟫ = ‖T x‖²` | `V1` on the diagonal | `Analysis/Semigroup/VonNeumann.lean` | **extend**: the module owns `V1`; one theorem added |
| `F0`–`F3` | `P_t` on the **form** domain | `Analysis/Semigroup/Generated/FormDomain.lean` | **create**: `naming.md` keeps operator domain and form domain distinct, `Generated/Domain.lean` owns the operator domain (`S0a`) and does not depend on `Resolvent/Limit.lean` |
| `F4` | concrete specialization, arbitrary `B` | `KLS/LogConcave/HeatSemigroup/Domain.lean` | **extend**: that module is the concrete domain frontend; its docstring now separates the generator-domain and form-domain interfaces |

No empty module, compatibility alias or old-path wrapper was created; no existing statement,
parameter list or namespace was changed. `FunctionalInequalities.lean` gains the new leaf.

## Statements

Write `A = adjointComp T = T†T`, `P_t = Generated.apply T hT hd t`, `J_s = resolventCLM T hT hs`.

| Obligation | Public declaration | Exact scope |
| --- | --- | --- |
| F0 | `Analysis.Semigroup.Generated.norm_map_apply_le_of_generator` | `f ∈ D(A)`, `t ≥ 0` implies `‖T (P_t f)‖ ≤ ‖T f‖` |
| F0 (form) | `Analysis.Semigroup.Generated.inner_adjointComp_apply_le` | `⟪A (P_t f), P_t f⟫ ≤ ⟪A f, f⟫` on `D(A)` |
| F1 | `Analysis.Semigroup.Generated.exists_seq_mem_adjointComp_domain_tendsto_graph` | for `f ∈ D(T)` there are `u n ∈ D(A)` with `u n → f` **and** `T (u n) → T f` |
| F2 | `Analysis.Semigroup.Generated.preserves_form_domain` | `f ∈ D(T)`, `t ≥ 0` implies `P_t f ∈ D(T)` |
| F3 | `Analysis.Semigroup.Generated.norm_map_apply_le` | `f ∈ D(T)`, `t ≥ 0` implies `‖T (P_t f)‖ ≤ ‖T f‖` |
| F2+F3 | `Analysis.Semigroup.Generated.exists_mem_domain_norm_map_apply_le` | the membership witness and the estimate in one statement |
| F4 | `KLS.LogConcave.HeatSemigroup.preserves_form_domain`, `norm_closedWeightedOperator_le` | F2–F3 for the closed weighted operator, arbitrary weight `B` |

Supporting public theorems, all adjoint-free and in `Analysis/Semigroup/Resolvent/Limit.lean`:
`resolventDomain_energy_identity`, `norm_map_resolventDomain_sq_le_of_le`,
`norm_map_resolventDomain_sub_sq_le_sub`, `norm_map_resolventDomain_le`,
`norm_map_resolventDomain_sub_map_sq_le`,
`exists_delta_norm_map_resolventDomain_sub_map_lt`; plus
`Analysis.Semigroup.inner_adjointComp_self` and the two `Generated` steps
`norm_map_apply_sq_le_mul`, `norm_map_apply_sq_le_mul_norm`.

## Proofs

**F1's analytic core** is a two-parameter identity for the resolvent, obtained by testing the weak
`s`-equation against `J_s f - J_r f`, the weak `r`-equation against `J_r f - J_s f` and adding:

`2 ‖J_s f - J_r f‖² + (s + r) ‖T (J_s f) - T (J_r f)‖² + (s - r)(‖T (J_s f)‖² - ‖T (J_r f)‖²) = 0`.

It needs no datum regularity and no closedness. Its two consequences are that the energy
`s ↦ ‖T (J_s f)‖²` is **antitone** and that the energy increments dominate the graph distances:
`‖T (J_s f) - T (J_r f)‖² ≤ ‖T (J_s f)‖² - ‖T (J_r f)‖²` for `s ≤ r`. On `D(T)` the energies are
bounded by `‖T f‖²` (`norm_map_resolventDomain_le`, from the `R1` computation and
Cauchy–Schwarz), so along `s_n = 1/(n+1)` the monotone bounded energies force `T (J_{s_n} f)` to
be Cauchy; completeness of `H₁` gives a limit and **closedness of `T`** identifies it with `T f`.
The transfer back to every small `s` uses `‖T (J_s f) - T f‖² ≤ ‖T f‖² - ‖T (J_s f)‖²`, which is
again the `R1` computation. No weak compactness, no spectral calculus and no functional calculus
is used, and the adjoint does not appear in this module.

**F0.** `V1` on the diagonal gives `‖T x‖² = ⟪A x, x⟫` for `x ∈ D(A)`. With `S0a`'s invariance and
commutation, symmetry `P4` and the semigroup law `P6`,

`‖T (P_t f)‖² = ⟪A (P_t f), P_t f⟫ = ⟪P_t (A f), P_t f⟫ = ⟪A f, P_{2t} f⟫ = ⟪T f, T (P_{2t} f)⟫
  ≤ ‖T f‖ ‖T (P_{2t} f)‖`,

so the energy at time `t` is controlled by the **doubled** time; the `L²` contraction `P3` bounds
every such energy by `‖A f‖ ‖f‖`. Hence `M = sup_{t ≥ 0} ‖T (P_t f)‖` exists and every member `y`
of that family satisfies `y² ≤ ‖T f‖ M`, so `M ≤ √(‖T f‖ M)`, `M² ≤ ‖T f‖ M` and `M ≤ ‖T f‖`.
The doubling step is applied to the supremum, not iterated, so no real powers, no time
derivative and no monotonicity theorem for one-sided derivatives are needed.

**F2–F3.** For `f ∈ D(T)` take `u n` from F1. Then `P_t (u n) ∈ D(A) ⊆ D(T)`, and F0 applied to
the differences `u n - u m ∈ D(A)` gives `‖T (P_t u n) - T (P_t u m)‖ ≤ ‖T (u n) - T (u m)‖`, so
`T (P_t u n)` is Cauchy and converges; `P_t (u n) → P_t f` because `P_t` is bounded. Closedness of
`T` yields `P_t f ∈ D(T)` and `T (P_t f) = lim T (P_t u n)`, whose norm is at most
`lim ‖T (u n)‖ = ‖T f‖` by F0. The membership witness and the bound are produced together
because the bound mentions the witness.

**F4** is one `exact` per statement, with the full hypotheses of the concrete object preserved and
an arbitrary weight `B`; the gradient delivered is the closed weighted operator, in the
closed-operator sense.

## Boundaries

Every result allows `t = 0` and the zero vector, and both are audited. F0 assumes `f ∈ D(A)`;
F1–F4 assume only membership in the form domain — no smooth test class, no compact support, no
positive-time smoothing and no strengthening of the input. Nothing here applies a scalar
semigroup contraction to `T f`: there is no intertwining theorem between `T` and a semigroup on
`H₁`, and none is used. No standard-result shortcut replaces an unformalized spectral or limit
step: the only limit passages are the two Cauchy/closed-graph arguments above, both carried out
explicitly. No axiom, `sorry`, conclusion-bearing structure, circular dependency or unresolved
analytic hypothesis is introduced.

Still unproved: positive-time membership of `P_t g` in `D(A)` for arbitrary `g ∈ H₀`, a `C/t`
generator bound, classical smooth representatives of `P_t f`, preservation of compactly supported
smooth functions, the operator-core claim, gradient commutation, the square estimate
`Γ(P_t f) ≤ P_t Γ(f)` and its `L¹` self-improvement, BGL, small-time BV bounds, general-law
passage and Buser's inequality. Bakry–Émery stays partial; the full Cheeger–Buser comparison and
the dimension-free KLS bound stay pending, and the constant `π` is not approached.

| 已有证明 | 仅类型检查 | 仍是非形式化方案 |
| --- | --- | --- |
| F0–F4, including arbitrary weights, `t = 0` and the zero vector; the six resolvent graph-norm theorems | `∀ g t, 0 < t → P_t g ∈ D(T)` for arbitrary `g` | Classical representatives, `Γ(P_t f) ≤ P_t Γ(f)`, BGL/BV, general-law passage, Buser |
| Existing `S0a` `D0`–`D4`, `G0`/`G1`, pointwise `B0`–`B4` | Earlier route candidates remain candidates | Time differentiation of `s ↦ P_s Γ(P_{t-s} f)` and interchange with derivatives, integrals and limits |

## Next stage

The two theorems a second stage can use directly are
`Analysis.Semigroup.Generated.preserves_form_domain` (form-domain stability, so `T (P_t f)` is a
legitimate object for every `f ∈ D(T)` and `t ≥ 0`) and
`Analysis.Semigroup.Generated.norm_map_apply_le` (energy contraction, the integrated
`Γ`-estimate), with
`Analysis.Semigroup.Generated.exists_seq_mem_adjointComp_domain_tendsto_graph` as the
graph-norm approximation tool that transfers any statement proved on `D(T†T)` to `D(T)`, and
`Analysis.Semigroup.Generated.inner_adjointComp_apply_le` as the Dirichlet-form phrasing.
Concretely, `KLS.LogConcave.HeatSemigroup.preserves_form_domain` and
`norm_closedWeightedOperator_le` give the same two facts for the closed weighted gradient with
arbitrary `B`.

## Validation

Validation logs and the final verification receipt pointer are in
`build/audit/semigroup-form-domain/`. The four touched modules, the new module and the
independent audit `research/audits/SemigroupFormDomainStabilityAudit.lean` are checked with
`-DwarningAsError=true`; that audit restates F0–F4 in full, proves each one, exercises `t = 0`
and the zero vector, and prints 33 axiom reports, all standard-only (`propext`,
`Classical.choice`, `Quot.sound`). The existing deliberate target warning in `KLS/Target.lean`
is outside these proofs. Progress views are regenerated from a temporary Git index that
preserves the real staging area.

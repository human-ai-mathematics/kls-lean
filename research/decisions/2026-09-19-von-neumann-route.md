# Semigroup Generation Path: von Neumann's Theorem and resolvent Limit ([`S6` Prerequisites] Path)

2026-09-19, immediately following [`S5` round](2026-09-19-semigroup-yosida-proof.md) and owner maintaining a constant π decision
([Handover checklist](2026-09-19-semigroup-handoff.md) §5 Note). This round **only writes definitions and statements, no proofs**;
proofs are delegated to the concurrent Opus session and later integrated by this session. No commit, no push.

## Why this section

`S1`–`S5` proved. `S6` (Yosida index `exp(-t L_s)` converges strongly `s ↓ 0`) is a step not previously present in Mathlib,
the classical proof requires two things `S1`–`S5` deliberately avoided:

1. **von Neumann theorem**: `T` closed and densely defined ⟹ `T†T` self-adjoint, `D(T†T)` dense, and `(1 + s T†T) J_s = 1`;
2. **resolvent limit**: `J_s → 1` strong convergence, `J_s J_r = J_r J_s` (the latter is exactly the commutativity assumed in `S6` statement).

Owner has decided to keep the target at π, with the localization route eliminated, so the semigroup route must be completed; this is the next piece.

## Definition module (this round has been written and compiled)

`formalization/FunctionalInequalities/Analysis/Semigroup/AdjointComp.lean`, only defined with `rfl`-level glue:

| Statement | Content |
| --- | --- |
| `adjointCompDomain T` | `{x ∈ D(T) \| T x ∈ D(T†)}`, as `Submodule ℝ H₀` |
| `adjointComp T` | `T†T`, i.e. `T†.comp (T.domRestrict (adjointCompDomain T)) _` |
| `adjointComp_domain`, `adjointComp_domain_eq` | The domain is defined as `adjointCompDomain T ⊓ T.domain`, equal to `adjointCompDomain T` |
| `adjointComp_apply` | `adjointComp T x = T† ⟨T ⟨x, x.2.2⟩, _⟩` |

Mathlib's `LinearPMap.comp` requires all values of the inner operator to lie within the outer domain, so we first use `domRestrict` to restrict `T`.
`T†` requires `[CompleteSpace H₀]`; the completeness of `H₁` is not used in the definition.
`-DwarningAsError=true` passes, 0 fails with 0 warning; olean was generated separately using `lake build` for import in the proof session.

## Statement file

`research/audits/VonNeumannRouteStatements.lean`, contains only `#check`, all 8 pass type checking:

| Number | Content | Assumptions | Risks |
| --- | --- | --- | --- |
| `V1` | `⟪T†T x, y⟫ = ⟪T x, T y⟫`, `x ∈ D(T†T)`, `y ∈ D(T)` | `Dense` | low: `adjoint_isFormalAdjoint` expansion |
| `V2` | `J_s f ∈ D(T†T)` and `J_s f + s • T†T (J_s f) = f` | closed, `Dense`, `0 < s` | In: weak equation ⟹ `T u ∈ D(T†)` (`mem_adjoint_domain_of_exists`) + `adjoint_apply_eq` |
| `V3` | `IsSelfAdjoint (adjointComp T)` | closed, `Dense` | medium to high: symmetry gives `≤`, reverse using `1 + T†T` surjection (`V2`) |
| `V4` | `Dense (D(T†T))` | closed, `Dense` | low: `V3` + `IsSelfAdjoint.dense_domain` |
| `V5` | `f - J_s f = s • J_s (T†T f)`, `f ∈ D(T†T)` | closed, `Dense`, `0 < s` | low to medium: `f` itself solves the weak equation of `f + s T†T f`, uniqueness |
| `R1` | `‖J_s f - f‖² ≤ s ‖T f‖²`, `f ∈ D(T)` | closed, `0 < s` | low: weak equation test against `v = u - f` and `v = u` |
| `R2` | `∀ f ε>0, ∃ δ>0, ∀ 0<s<δ, ‖J_s f - f‖ < ε` | closed, `Dense` | low: `R1` + dense + contraction |
| `R3` | `J_s ∘ J_r = J_r ∘ J_s` | closed | Medium: weak form's resolvent identity + uniqueness |

`R2` Use ε–δ form instead of `Tendsto`, since `resolventCLM` carries `0 < s` as a parameter, writing `s ↦ J_s f` requires dependence on `if`.
Individual assumptions are expected to be as redundant as `S2`/`S3` (the `V1` `CompleteSpace H₁` and `R1`/`R3` `Dense` have already been omitted),
if the proof session discovers more, by convention: prove a stronger version + word-for-word packaging + record.

## Division of labor

* Session A (von Neumann): `V1`–`V5`, new module `Analysis/Semigroup/VonNeumann.lean`, audit `research/audits/VonNeumannAudit.lean`.
* Session B (resolvent limit): `R1`–`R3`, new module `Analysis/Semigroup/ResolventLimit.lean`, audit `research/audits/ResolventLimitAudit.lean`.

Both are independent (the `R` series does not touch adjoints). Rules remain the same: only create new files, only use `lake env lean -DwarningAsError=true`, no `lake build`, no `verify.py`, no git, no modification of any existing files, zero `sorry`.

## Out of scope

`S6`–`S8` is unproven and not stated herein. Markov property, Γ calculus, small-time heat estimate, Buser inequality are not included in this round.
`thm:logconcave-cheeger-poincare-comparison` No progress markers, `tasks.json` unchanged (registered uniformly during integration).

## Append: `V1`–`V5`, `R1`–`R3` all proven (same day, two parallel Opus sessions, about 8 and 13 minutes)

New module `Analysis/Semigroup/VonNeumann.lean` (`V1`–`V5`) and `Analysis/Semigroup/ResolventLimit.lean` (`R1`–`R3`),
audit `research/audits/VonNeumannAudit.lean` (Article 18 `#print axioms`) and `ResolventLimitAudit.lean` (Article 9),
**Report 27 contains only `propext, Classical.choice, Quot.sound`, 0 contains `sorryAx`**; 8 route statements are token-by-token and fully consistent with route files
(this session independently recompiled and mechanically compared). Three new modules have been integrated into the aggregate root, `lake build` 3524 jobs passed, and six semigroup audit clients, after strict recompilation, all exited with 0.

| Number | Statement | Notes |
| --- | --- | --- |
| `V1` | `inner_adjointComp` | **Does not require `CompleteSpace H₁` and `T.IsClosed`** |
| `V2` | `resolvent_add_smul_adjointComp` (+ `mem_adjointComp_domain_resolventDomain`) | Half of the domain `T(J_s f) ∈ D(T†)` **does not require `Dense`**, audit recorded as `route_V2_domain_of_not_dense` |
| `V3` | `isSelfAdjoint_adjointComp` | see below |
| `V4` | `dense_adjointComp_domain` | direct proof, see below |
| `V5` | `sub_resolvent_eq_smul` | by draft |
| `R1` | `norm_resolventCLM_sub_sq_le` (packaging `norm_resolventCLM_sub_sq_le_quarter`) | **Constant is `s‖Tf‖²/4`**, the `s‖Tf‖²` of the route is packaged character by character |
| `R2` | `exists_delta_norm_resolventCLM_sub_lt` | Draft, `δ = (ε/3)²/(‖Tg‖²+1)` |
| `R3` | `resolventCLM_comp_comm` | The proof differs from the draft, see below |

### Three places differ from the route draft

* The order of `V3 ⟹ V4` is impossible, reversed. Mathlib has `LinearPMap.IsFormalAdjoint.le_adjoint` `include`ed `Dense (T.domain)`,
  At `T := adjointComp T` this is exactly `V4`, so the proof of `V3` must first have `V4`. `V4` is directly proved (`g ⊥ D(T†T)`,
  By `1 + T†T` surjection to `g = x + T†T x`, then `0 = ⟪x, g⟫ = ‖x‖² + ‖Tx‖²`, `V3` is derived. Audit separately given
  `dense_of_route_V3` (by `IsSelfAdjoint.dense_domain`) together with `isClosed_of_route_V3`, maintains that the two entries remain superficially consistent.
* The auxiliary bound `R1` `‖Tu‖ ≤ ‖Tf‖` is not needed. A single verification `v = u − f` plus `s(‖Tu‖ − ‖Tf‖/2)² ≥ 0` directly yields the constant 1/4.
* **`R3` Draft says "close with `resolventCLM_symm`" is circular** (symmetry maps the statement back to itself). Actual proof:
  `z := s·J_s f − r·J_r f + (r−s)·J_s(J_r f)` resolves data into 0's weak `s`-equation (a weak equation of three weak equations' `linear_combination`),
  Hence `z = 0` (`weakResolvent_unique`); furthermore, by `Tz = 0`, the `w = J_s(J_r f)` `r`-equation is transformed into another `linear_combination`,
  `eq_resolventDomain` finishes the proof. No case split on `r = s` is needed, and `resolventCLM_symm` is unused.

### The Significance of `S6`

Statement `S6` assumes commutativity `(L s).comp (L r) = (L r).comp (L s)`, directly given by `R3` for `L_s = s⁻¹(1 − J_s)`; `L_s f → T†T f` (`f ∈ D(T†T)`) is given by `V5` + `R2`; `D(T†T)` is dense by `V4`. `S6` itself remains unproven.

### Friction (for the next round)

`real_inner_comm x y : ⟪y, x⟫ = ⟪x, y⟫`, the first explicit parameter is at the left's **second** position; `Dense.exists_dist_lt` does not exist in this pin, use `Metric.mem_closure_iff.mp`; `lt_div_iff₀` instead of `div_lt_iff₀`; subtype eta (`T ⟨↑u, u.2⟩` and `T u`) treats `linarith` as distinct atoms, use `rfl`-`have` or `show` uniformly.

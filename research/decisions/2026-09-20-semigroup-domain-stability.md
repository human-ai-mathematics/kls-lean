# Bakry–Émery S0a: generator domain invariance

2026-09-20. This round proves D0–D4 for closed densely defined real Hilbert space operators.
It preserves all earlier uncommitted work, makes no commit or push, and does not complete Buser.

## Statements and dependencies

Write `A = adjointComp T = T†T` and `P_t = semigroupApply T hT hd t`.

| Obligation | Public declaration | Exact scope |
| --- | --- | --- |
| D0 | `Analysis.Semigroup.mem_adjointComp_domain_of_generator_limit` | A right quotient limit `z` implies `∃ hy : y ∈ D(A), A ⟨y,hy⟩ = -z` |
| D1 | `Analysis.Semigroup.semigroupApply_mem_adjointComp_domain` | `f ∈ D(A)`, `t ≥ 0` implies `P_t f ∈ D(A)` |
| D2 | `Analysis.Semigroup.adjointComp_semigroupApply` | `A(P_t f) = P_t(Af)` on `D(A)` |
| D3 | `Analysis.Semigroup.exists_delta_norm_inv_smul_semigroupApply_add_sub_add_adjointComp_lt` | Right time derivative at `t ≥ 0` is `-A(P_t f)` |
| D4 | `KLS.LogConcave.heatSemigroup_mem_generator_domain`, `heatSemigroup_generator_comm`, `heatSemigroup_mem_closedWeightedOperator_domain`, `heatSemigroup_right_derivative` | D1–D3 for the closed weighted operator with arbitrary `B`, plus `D(A) ⊆ D(T̄)` |

The abstract implementation is `Analysis/Semigroup/Generated/Domain.lean`. Its auxiliary public
`generator_limit_semigroupApply` transports the zero-time generator estimate to `P_t f`.
The concrete implementation is `KLS/LogConcave/HeatSemigroup/Domain.lean`; both are imported by
the aggregate library. The independent audit `research/audits/SemigroupDomainStabilityAudit.lean`
restates D0–D4 with complete propositions and reports axioms for all nine public declarations
and all eight audit theorems.

D0 uses `inner_semigroupApply_left` to transfer the quotient to `x ∈ D(A)`.
Cauchy–Schwarz and the two epsilon–delta limits bound the scalar error by
`ε (‖x‖ + ‖y‖)` for every positive epsilon. Hence `⟪-z,x⟫ = ⟪y,Ax⟫`.
`LinearPMap.mem_adjoint_domain_of_exists` and `adjoint_apply_eq` put `y` in `D(A†)`
with value `-z`, using `dense_adjointComp_domain` for the value identification.
Only at the final step does `isSelfAdjoint_adjointComp` identify `A†` with `A`.
Symmetry alone would not justify that last domain equality.

D1–D2 use the semigroup addition law twice, with `h+t=t+h`, then linearity and contraction:
`q_h(P_t f) + P_t(Af) = P_t(q_h(f)+Af) → 0`.
D0 is applied with `z = -P_t(Af)`, so its conclusion is **positive** `A(P_t f)=P_t(Af)`.
Different membership witnesses in the subtype are propositionally irrelevant; the final
`simpa only [neg_neg]` uses definitional proof irrelevance. D3 rewrites the same estimate at
`t+h` and uses D2. Every time assertion allows `t=0` and only takes increments `h>0`.

## Boundaries

Every invariance, commutation and right-derivative result requires `f ∈ D(A)`, with no smooth-test
restriction. D0 instead assumes existence of the stated right limit, which is the hypothesis
being characterized, not the desired domain conclusion. No new axiom or conclusion-bearing
structure is introduced. D4 allows arbitrary weights `B`; it does not need a smooth potential.
The resulting gradient is `T̄(P_t f)` in the closed-operator sense. The identification with
`weightedLaplacian` remains limited to the existing G1 compactly supported smooth tests.

Still unproved here: arbitrary-input positive-time membership in `D(A)`, a `C/t` generator
bound, invariance/contraction on all of `D(T)`, classical smooth representatives, preservation of
compactly supported smooth functions, the operator-core claim, gradient commutation, square
Gamma estimates or their L1 self-improvement, BGL, BV small-time bounds, general-law passage,
and Buser. BE stays partial; the full Cheeger–Buser comparison and dimension-free KLS stay pending.

| 已有证明 | 仅类型检查 | 仍是非形式化方案 |
| --- | --- | --- |
| D0–D4, including arbitrary weights and `t=0` | `∀ f t, 0<t → P_t f ∈ D(A)` | Uniform Yosida bounds and passage to the unbounded generator |
| Existing G0/G1 and pointwise B0–B4 | `‖A(P_t f)‖ ≤ (1/exp(1))/t * ‖f‖`, with existential domain witness | Form-domain approximation, weak Gamma calculus and time interpolation |
| Existing Cheeger half and one-dimensional constant 12 | Earlier route candidates remain candidates | Classical representatives, BGL/BV, general-law passage and full Buser |

## Next cut

Prefer **form-domain invariance** next: `f ∈ D(T) → P_t f ∈ D(T)` and
`‖T(P_t f)‖ ≤ ‖Tf‖`. This directly extends the closed-gradient interface needed by a weak Gamma
route. Minimal remaining ingredients are (i) energy contraction on `D(A)`,
`⟪A P_t f,P_t f⟫ ≤ ⟪Af,f⟫`, and (ii) approximation of every `f ∈ D(T)` by vectors in `D(A)`
in the `T` graph norm, followed by closedness of `T`. Neither follows just by applying the
L2 contraction to `T f`: no intertwining of `T` with a vector semigroup is available.
Resolvent approximations are a possible route to (ii), but that convergence must be proved.

For the alternative arbitrary-input analytic smoothing cut, the correct scalar normalization
comes from `g(λ)=λ exp(-tλ)` for `λ≥0`, `t>0`: its derivative is
`exp(-tλ)(1-tλ)`, so its maximum is `1/(exp(1)t)` at `λ=1/t`.
This calculation is mathematical motivation, not a Lean theorem in this round. The audit merely
type-checks the corresponding explicit constant. The missing analytic estimate is a bound on
`‖L_s exp(-t L_s)f‖` uniform in `s>0`, together with a justified limit/closed-graph identification
for `A`. A norm bound alone is not strong convergence of these generator images; that passage
must also be supplied. There is no spectral functional calculus imported by this proof.

## Validation

Validation logs and the final verification receipt pointer are in
`build/audit/semigroup-domain/`. The two modules and independent audit are checked with
`-DwarningAsError=true`; all 17 axiom reports are standard-only (propext, Classical.choice, Quot.sound). The full build and repository
gates are run after the progress views are regenerated from a temporary Git index, preserving
the real index. The existing deliberate target warning in `KLS/Target.lean` is outside these proofs.

The strict module and audit checks passed with zero errors and warnings. `lake build` passed
(3552 jobs); ledger: 26 certificates, zero errors; Blueprint: 88 labels and four active routes,
zero errors; Atlas: 75 nodes, 26 certificates, no cycles; all 104 unit tests passed.
`git diff --check` passed. The final `verify.py` result is recorded separately in
`build/audit/semigroup-domain/final-snapshot.json` so recording its receipt does not invalidate
its source snapshot. No remote CI result is claimed.

# Next prompt: Bakry–Émery S0a——generator domain characterization, semigroup domain stability and closed gradient interface

Continue Buser's Bakry–Émery route at `/Users/lyuyuwei/Documents/ChatGPT/KLS`. In this round, make an independent, verifiable semigroup interface cut-off: prove the reverse characterization of the generator domain on the currently abstract semigroup, and thereby obtain `D(T†T)` under `P_t` in terms of stability and generator commutativity, and then specialize to the existing `KLS.LogConcave.heatSemigroup`.

This round does not establish full positive-time PDE regularity: it only proves `f ∈ D(T†T)` to `P_t f ∈ D(T†T)`. It must not be written as proving the existence of `P_t f ∈ D(T†T)` for arbitrary `L²` inputs, nor must it claim that a classical smooth representative of `P_t f` has been constructed, that gradient exchange has been proven, or that Buser has been completed.

## 1. First verify the current workspace

First read:

- `AGENTS.md`
- `HANDOFF.md` top `Current operational status (2026-09-20)`
- `research/decisions/2026-09-20-bakry-emery-route.md`
- `research/decisions/2026-09-20-generator-identification.md`
- `research/decisions/2026-09-20-bochner-identification.md`
- `research/audits/BakryEmeryRouteStatements.lean`

Key checks:

- `formalization/FunctionalInequalities/Analysis/Semigroup/AdjointComp.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Basic.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Laws.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Generator.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Family.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Limit.lean`
- `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Basic.lean`
- `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Generator.lean`

Check the current dirty worktree, retain all existing modifications; do not reset, clean, overwrite, or delete others' work. This round
no commit, no push.

## 2. Current baseline proven

Suppose `T : H₀ →ₗ.[ℝ] H₁` closed and densely defined,

```text
A = adjointComp T = T†T,
P_t = semigroupApply T hT hd t.
```

Already exists:

- `isSelfAdjoint_adjointComp`: `A` self-adjoint;
- `dense_adjointComp_domain`: `D(A)` dense;
- `inner_semigroupApply_left`: `P_t` self-adjoint;
- `semigroupApply_add`: `P_(t+u) = P_t P_u`;
- `norm_semigroupApply_le`: `P_t` is a contraction;
- `exists_delta_norm_inv_smul_semigroupApply_sub_self_add_adjointComp_lt`:
  for `f ∈ D(A)`,

  ```text
  h⁻¹ • (P_h f - f) → -Af    (h ↓ 0).
  ```

- `mem_domain_of_mem_adjointComp_domain`: `D(A) ⊆ D(T)`;
- `heatSemigroup_generator`: The above generator limit has been specialized to a closed weighted gradient.

G0/G1 Completed with B0–B4, but do not repeat the Bochner calculation in this round.

All complete parameters, namespaces, implicit instances, and `LinearPMap` subtype shapes are governed by the current `#check @...`,
do not infer from abbreviations in this document.

## 3. First goal: reverse characterization of the generator domain

Only proved so far

```text
f ∈ D(A)  ⟹  h⁻¹ • (P_h f - f) → -Af.
```

This round first proves the reverse: if the right difference quotient of some `y : H₀` converges to `z : H₀` at `h ↓ 0`, then

```text
y ∈ D(A)  and  A y = -z.
```


Suggest adding:

```text
formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Domain.lean
```

Candidate public declarations may be named as:

```text
mem_adjointComp_domain_of_generator_limit
adjointComp_eq_neg_of_generator_limit
```

Or place the membership relation and action value in a theorem returning `∃ hy : y ∈ D(A), ...`. The specific Lean statement should follow the right-limit shape of `ε`–`δ` in the current generator file, for example:

```text
∀ ε > 0, ∃ δ > 0, ∀ h > 0, h < δ,
  ‖h⁻¹ • (P_h y - y) - z‖ < ε.
```

Note the current forward theorem written as

```text
‖h⁻¹ • (P_h f - f) + Af‖ < ε,
```

So the reverse conclusion must be `Ay = -z`, no symbol reversal should occur.

### Recommended proof path

Fix any `x ∈ D(A)`:

1. Use `inner_semigroupApply_left` to

   ```text
   ⟪h⁻¹ • (P_h y - y), x⟫
   ```

   Rewrite to

   ```text
   ⟪y, h⁻¹ • (P_h x - x)⟫.
   ```

2. The left side tends to `⟪z,x⟫` by assumption; the right side tends to `⟪y,-Ax⟫` by the existing generator theorem.
3. We obtain for all `x ∈ D(A)`:

   ```text
   ⟪-z,x⟫ = ⟪y,Ax⟫.
   ```

4. Prove using `LinearPMap.mem_adjoint_domain_of_exists` / `adjoint_apply_eq` class of existing interfaces
   `y ∈ D(A†)` and `A†y = -z`.
5. Use `isSelfAdjoint_adjointComp` to derive `A† = A`, obtaining `y ∈ D(A)` and `Ay = -z`.

Do not treat the reverse characterization itself as a new assumption, nor define a structure and hide the target conclusion within a field. If there is no ready-made topological API for transporting the inner limit, perform explicit repository-style `ε`–`δ` estimates; do not introduce an unproven abstract generator theorem.

## 4. Second objective: semigroup stability and commutativity of `D(A)`

For any `f : D(A)`, `t ≥ 0`, prove:

```text
P_t f ∈ D(A),
A(P_t f) = P_t(Af).
```

Suggest a public statement:

```text
semigroupApply_mem_adjointComp_domain
adjointComp_semigroupApply
```

It is recommended to derive it from the reverse characterization in Section 3, rather than redoing a Yosida graph limit:

```text
h⁻¹(P_h(P_t f) - P_t f)
  = P_t(h⁻¹(P_h f - f))
  → -P_t(Af).
```

Here we use:

- `semigroupApply_add`;
- `semigroupApply_sub`, `semigroupApply_smul`;
- `norm_semigroupApply_le`;
- `P_h P_t = P_t P_h`, should be exactly derived from the additive semigroup of the same parameter and `h+t=t+h`;
- the existing `f ∈ D(A)` generator limit at zero time.

Then, by reverse characterization, we obtain the membership relation and

```text
A(P_t f) = P_t(Af).
```

Theorem should cover `t = 0`, without requiring artificial addition of `0 < t`. If the members of subtype have different proofs leading to surface-level inequality of terms, use proof irrelevance / `Subtype.ext`, and do not add irrelevant assumptions.

## 5. Third goal: the right-time derivative at any time

For `f ∈ D(A)`, `t ≥ 0`, prove the exact `ε`–`δ` version:

```text
h⁻¹ • (P_(t+h) f - P_t f) → -A(P_t f)
                         = -P_t(Af)    (h ↓ 0).
```

Suggested declaration:

```text
exists_delta_norm_inv_smul_semigroupApply_add_sub_add_adjointComp_lt
```

Or use a more concise and unambiguous name within the project. It must be clearly specified that this is the right derivative; do not state that the conclusion holds for `h > 0` as if it had proven Fréchet differentiability over the entire real axis.

This step is for the subsequent interpolation quantity.

```text
s ↦ P_s Γ(P_(t-s) f)
```

The pure semigroup prerequisites for time derivatives, but this round does not define or differentiate this interpolation quantity.

## 6. Fourth goal: specialize to existing `heatSemigroup`

Suggest adding:

```text
formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Domain.lean
```

Let

```text
T̄ = hν.closedWeightedOperator m B hi,
A  = adjointComp T̄.
```

Proof and abstract theorem packaging with literal correspondence:

- `heatSemigroup_mem_generator_domain`: `f ∈ D(A)` implies `P_t f ∈ D(A)`;
- `heatSemigroup_generator_comm`: `A(P_t f)=P_t(Af)`;
- `heatSemigroup_mem_closedWeightedOperator_domain`: by `D(A) ⊆ D(T̄)` we get
  `P_t f ∈ D(T̄)`;
- `heatSemigroup_right_derivative`: the right derivative of any `t ≥ 0`.

At least maintain abstract packaging for general weights `B`; do not arbitrarily restrict to `B = I`. Equivalence with classical
`weightedLaplacian` is still only used on `C_c∞` inputs where G1 has been proven.

The current "gradient" can only be interpreted as a closed gradient.

```text
T̄(P_t f),
```

Cannot be directly written as a classical `L²` represented by an arbitrary `gradient`.

## 7. Clear exclusion of stronger conclusions not in this round

The following remain unproven:

1. For any `f : H₀`, `t > 0`, `P_t f ∈ D(A)`;
2. `‖A P_t f‖ ≤ C/t · ‖f‖`;
3. For any `f ∈ D(T)`, `P_t f ∈ D(T)` and
   `‖T(P_t f)‖ ≤ ‖Tf‖`;
4. `P_t[f]` has a classical representative of `C∞` or `C³`;
5. `P_t` preserves `C_c∞`, or `C_c∞` is the operator core of `A`;
6. `Γ(P_t f) ≤ P_t Γ(f)`;
7. `‖∇P_t f‖ ≤ P_t ‖∇f‖`;
8. BGL reverse estimation, small-time BV estimation, general measure approximation and final Buser.

Among the terms 1–2, the true "positive-time analytic smoothing" requires additional Yosida index uniform estimates or equivalent functional calculus, and cannot be deduced automatically from the current domain stability. The term 3 corresponds to form-domain stability, which is stronger than the conclusion `D(A)` on the input side.

## 8. The candidate subsequent interface performs only type checking

In audit documents, retain the following candidates for the next stage, but do not use assumptions to disguise them as proofs:

```text
∀ f t, 0 < t → P_t f ∈ D(A)
```

and with explicit constants

```text
‖A(P_t f)‖ ≤ C / t * ‖f‖.
```

Before proving specific constants, reverse-engineer the correct normalization from the optimal bound of scalar functions `λ ↦ λ exp(-tλ)`; if spectral function calculus is not available, only record the missing Yosida uniform estimate, do not guess the constants.

## 9. Audit and Deliverables

New:

- `research/audits/SemigroupDomainStabilityAudit.lean`
- `research/decisions/2026-09-20-semigroup-domain-stability.md`

Audit at least verbatim and close out:

```text
D0  The right difference quotient limit exists ⟹ y ∈ D(A) and Ay = -z
D1  f ∈ D(A) ⟹ P_t f ∈ D(A)
D2  A(P_t f) = P_t(Af)
D3  The right derivative at t ≥ 0 is -A(P_t f)
D4  The D1–D3 packaging of heatSemigroup and D(A) ⊆ D(T̄)
```

Run `#print axioms` for all newly added public declarations. Only allow Mathlib common foundational axioms; do not appear:

- `sorryAx`
- New `axiom`
- `sorry` / `admit`
- Placeholder proof
- Hide the conclusion in structural fields, typeclass, or additional assumptions
- Stealthily strengthen the `D(A)` input into a test function and still claim completion of general domain stability

The decision record must list:

- Actual statements and proofs depend on;
- Usage position of self-adjointness in reverse generator characterization;
- `A` and semigroup commutativity symbols;
- Which conclusions hold only for `D(A)` input;
- Strict boundary between smooth arbitrary input, form-domain stability, and classical representatives in positive time;
- Yosida uniform estimates or weak Γ interface needed in the next stage.

Provide a three-column table of "existing proof / type check only / still non-formalized scheme". In this round, do not change the pending status of the Cheeger–Buser nodes, and the `BE` node should remain partial.

## 10. Acceptance

Run from `formalization/`:

```bash
lake env lean -DwarningAsError=true \
  FunctionalInequalities/Analysis/Semigroup/Generated/Domain.lean

lake env lean -DwarningAsError=true \
  FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Domain.lean

lake env lean -DwarningAsError=true \
  ../research/audits/SemigroupDomainStabilityAudit.lean

lake build
```

Run from repository root:

```bash
git diff --check
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 research/atlas.py check
python3 -m unittest discover -s research/tests
python3 research/verify.py
```

New files must have zero errors and zero warnings under `-DwarningAsError=true`. In a full build, warnings from existing target holes in `KLS/Target.lean` may be retained, and no other `sorry` or warnings may be introduced.

If synchronizing progress documents, run from `AGENTS.md` stored canonical records `python3 research/progress/update.py`; retain others' modifications, without marking `BE`, complete Buser, or KLS as proved.

## 11. Final Report

Final explanation in Chinese:

1. Which statements complete D0–D4;
2. Why reverse generators characterization requires the self-adjointness of `P_t` and `A`;
3. How is the notation of `A(P_t f)=P_t(Af)` handled with respect to subtype membership;
4. Has only domain stability on inputs of `D(A)` been proven;
5. Axiom audit, strict compilation, and complete verification results;
6. Whether to select "any input with positive time entering `D(A)`" or "`D(T)` form-domain stability" next, and the missing minimal estimate.

Do not commit, do not push.

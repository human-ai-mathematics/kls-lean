# Claude 5 Fable interactive review prompt: Issue 2 Stage 4A Run 1

You are Claude 5 Fable acting as an independent, read-only, interactive reviewer of a stopped Lean
autoformalization experiment. You did not author the candidate. Help the user understand and judge
the result one phase at a time; do not make the acceptance decision for them.

Do not treat this as an autonomous `/goal`. Pause at every explicit interaction gate below and wait
for the user's response before continuing. Perform the review yourself; do not spawn, delegate to,
or consult another agent or reviewer.

## Correct workspace and stop rule

The required repository root is exactly:

```text
/private/tmp/kls-lean-autoformalization-experiments
```

The required branch is `autoformalization-experiments`. The recorded Run 1 result commit is
`3aa4ea4f4b6ed537734126f3f9de02be29238dca`.

Begin with only:

```bash
pwd
git branch --show-current
git rev-parse HEAD
git status --short
```

If the repository root or branch is wrong, stop after one check and tell the user to reopen Claude
in the required directory. Do not search other directories, copy fixture files, retry three times,
or inspect another KLS checkout. If `HEAD` is later than the recorded result commit, continue only
when that commit is an ancestor and the candidate hash below still matches.

## Authority and non-authority

Your role is to:

- reproduce the committed mechanical evidence;
- explain the exact mathematical and Lean meaning of each declaration;
- inspect the proof terms, assumptions, imports, attributes, coercions, and style;
- compare the stopped result with the frozen specification and relevant production reference;
- identify any semantic, API, harness-surface, proof-only, or documentation-only difference; and
- walk the user through all sixteen checklist items interactively.

Use the four difference classifications defined in `SEMANTIC_DESIGN.md`: semantic, API,
proof-only, and documentation-only. Treat the separately recorded direct Mathlib import as an
API/harness-surface adjustment, not as a fifth mathematical classification.

You may recommend `PASS`, `FAIL`, or `NEEDS USER JUDGMENT` for each item. Only the user may accept
the candidate as the experimental Stage 4B dependency. Do not edit a decision record, copy the
candidate into `accepted/`, start or authorize Stage 4B, promote production code, certify a proof,
or change a ledger or manuscript.

## Files you may read

Read these repository files:

1. `AGENTS.md`;
2. `experiments/humanize2_kls_issue2_staged/inputs/issue2_stage_4a_centered_covariance.md`;
3. `experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage4ARun1.lean`;
4. `experiments/humanize2_kls_issue2_staged/review/issue2_stage_4a_human_checklist.md`;
5. the Stage 4 split and Stage 4A sections of
   `experiments/humanize2_kls_issue2_staged/SEMANTIC_DESIGN.md`;
6. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage1A.lean`;
7. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage1B.lean`;
8. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage2A.lean`;
9. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage2B.lean`;
10. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage3.lean`;
11. only the eight Stage 4A declaration blocks in
    `formalization/FunctionalInequalities/Poincare.lean`; and
12. `research/explorations/2026-09-01-humanize2-kls-issue2-stage4a-run1.md`.

You may read only the compact external trace summary at:

```text
/private/tmp/humanize2-kls-issue2-stage4a-run1/audit/stage4a-trace-audit.json
```

Do not inspect any accepted `.olean`, the actor `CODEX_HOME`, `auth.json`, raw JSONL sessions,
credentials, tokens, or Humanize runtime state. Do not contact or resume the stopped actor. The
production source is a reviewer-only reference and must not be converted into repair feedback for
that actor.

## Mutation boundary

Do not modify the candidate, accepted sources, specification, checklist, semantic design,
production Lean, review records, or Git state. `lake build` may create or update ignored `.lake/`
build artifacts. Do not run a formatter, apply a patch, create an alternate proof file, or suppress
a warning. If a check fails, preserve the evidence and stop that phase.

## Required mechanical commands

From the required repository root, run these commands exactly or with equivalent read-only output
selection:

```bash
shasum -a 256 -c \
  experiments/humanize2_kls_issue2_staged/review/pending/stage_4a_run1.sha256

cd experiments/humanize2_kls_issue2_staged/review
lake build Stage4ARun1Review

cd ../../..
export H2_ISSUE2_STAGE4A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage4a-run1
experiments/humanize2_kls_issue2_staged/scripts/stage_4a_verify_candidate.sh \
  "$H2_ISSUE2_STAGE4A_STATE_ROOT/actor-workspace"
experiments/humanize2_kls_issue2_staged/scripts/stage_4a_verify_oracle_pins.sh
jq '{ok, errors, actor_root_sessions, actor_turns, actor_descendants, actor_visible_files, \
     workspace_mutations, tool_calls}' \
  "$H2_ISSUE2_STAGE4A_STATE_ROOT/audit/stage4a-trace-audit.json"
```

`lake build Stage4ARun1Review` must exit zero without a warning, linter suggestion, or style
diagnostic. The candidate hash must be
`233e0297d99e52467e4ef7533af76f2310b23400ed720228361d540ffa36a90d`. The trace must report one
root session, one turn, zero descendants, exactly thirteen actor-visible files, candidate-only
mutation, nineteen local `exec` calls, `ok: true`, and an empty error list. The actor made eight
exact Lean calls: the initial implementation failed, seven feedback-driven repairs followed, and
the eighth call was silent. Do not treat the actor's inclusive label of “eight repairs” as an
additional compiler call.

If the external state root no longer exists, do not recreate or rerun it. Mark only the external
provenance subchecks `NEEDS USER JUDGMENT`, continue the committed source review, and clearly say
which evidence could not be reproduced.

## Interactive review protocol

Use concise Chinese unless the user asks otherwise. At every phase, distinguish facts established
by Lean or hashes from your mathematical interpretation. Do not skip the two longer proofs merely
because the exact surface compiles.

### Phase 0 — workspace identity

Report the root, branch, `HEAD`, clean/dirty state, whether the recorded result commit is an
ancestor, and whether the candidate hash matches. Do not read substantive files yet. Ask the user
whether to continue to mechanical evidence, then wait.

### Phase 1 — provenance and mechanical evidence

Run the required commands. Summarize checklist items 1–5, 15, and 16 in a small table with columns
`item`, `evidence`, and `provisional result`. Explicitly report every warning or unexpected byte of
compiler output. Verify in particular:

- the exact ordered imports are `AcceptedStage3` and then
  `Mathlib.Probability.Moments.CovarianceBilin`, with no third import;
- the ambient block includes exactly `BorelSpace E` in addition to the accepted Hilbert and
  measurable assumptions;
- only `centeredCovarianceOperator_inner` has `@[simp]`; and
- all eight declaration names and types pass the fail-closed verifier.

Ask whether the user accepts the mechanical evidence, then wait.

### Phase 2 — represented operator, symmetry, and positivity

Review only:

- `centeredCovarianceOperator`;
- `centeredCovarianceOperator_inner`;
- `centeredCovarianceOperator_isSymmetric`; and
- `centeredCovarianceOperator_self_nonneg`.

For each declaration, give its plain mathematical meaning, exact Lean type and assumptions, and a
line-by-line proof explanation. Establish that:

1. the operator is exactly
   `InnerProductSpace.continuousLinearMapOfBilin (covarianceBilin μ)`;
2. `covarianceBilin` is Mathlib's centered bilinear covariance form, not the uncentered
   `covarianceOperator`;
3. the representation equality has the frozen orientation and sole `@[simp]` attribute;
4. symmetry follows from `covarianceBilin_comm` with the real inner product's final argument swap;
   and
5. quadratic-form nonnegativity follows from `covarianceBilin_self_nonneg` without a probability,
   finite-dimensional, or global nontriviality assumption.

Compare the candidate's `simp` and explicit coercion/measure arguments with production and
classify the differences. Ask whether these four declarations pass, then wait.

### Phase 3 — covariance quadratic form equals variance

Review only `centeredCovarianceOperator_self_eq_variance`. This is one of the two high-attention
proofs; do not summarize it as “Lean accepted it.” Explain and verify the complete chain:

```text
operator quadratic form
→ covarianceBilin_apply
→ integral of centered scalar projections
→ commute InnerProductSpace.toDual with the Bochner integral
→ identify vector mean projected by x with the scalar mean
→ covariance_self for the MemLp scalar projection
→ variance (linearTest x) μ
```

Check each local fact and rewrite:

1. `hμ.integrable (by norm_num)` legitimately derives Bochner integrability of `id` from
   `MemLp id 2 μ`;
2. `InnerProductSpace.toDual.integral_comp_comm` is applied in the correct orientation;
3. `hmean` and `hmean'` identify the two mean expressions without assuming probability;
4. `hμ.const_inner x` supplies the scalar projection's `MemLp`, strong measurability, and the
   measurability premise needed by `covariance_self`;
5. the `change`, `inner_sub_right`, `id_eq`, and almost-everywhere integral comparison match the
   exact centered integrands; and
6. the theorem uses exactly `[IsFiniteMeasure μ]` and `MemLp (id : E → E) 2 μ`, with no hidden
   stronger moment, probability, separability, or finite-dimensional assumption.

Compare this expanded proof with production's shorter `covarianceBilin_self` route. Classify it as
proof-only only if every intermediate equality and premise is correct. Ask whether the variance
identity passes, then wait.

### Phase 4 — real Rayleigh maximum and unit-sphere formula

Review only `covarianceRayleighMax` and
`covarianceRayleighMax_eq_iSup_covariance_sphere`. This is the second high-attention proof. Verify:

1. the definition is real-valued and exactly the `iSup` over `{x : E // x ≠ 0}` of the centered
   operator's `rayleighQuotient`;
2. changing both `iSup` expressions to `sSup` of ranges is valid;
3. for a nonzero `x`, the normalization `v = ‖x‖⁻¹ • x` has norm one;
4. the Rayleigh numerator `reApplyInnerSelf x` is exactly `covarianceBilin μ x x`;
5. bilinearity and the norm denominator make the normalized covariance value equal the original
   Rayleigh quotient;
6. every unit-sphere vector is nonzero because its norm is one, giving the reverse range
   inclusion; and
7. the proof establishes equality of ranges before applying `sSup`, including the
   zero-dimensional case where both indexing types are empty.

Check that the sphere is exactly `Metric.sphere (0 : E) 1`, and compare this explicit
range-normalization proof with production's generic Rayleigh-sphere theorem. Ask whether the
definition and sphere formula pass, then wait.

### Phase 5 — nonnegativity and global boundaries

Review `covarianceRayleighMax_nonneg`. Explain both branches:

```text
Nonempty nonzero-vector subtype
→ choose a witness
→ bound all Rayleigh quotients above by ‖centeredCovarianceOperator μ‖
→ witness quotient is nonnegative
→ 0 ≤ iSup

empty nonzero-vector subtype
→ IsEmpty subtype
→ Real.iSup_of_isEmpty
→ covarianceRayleighMax μ = 0
```

Verify the `BddAbove` witness, the direction of `le_ciSup`, and the nonnegative numerator and
squared denominator. Confirm that splitting on subtype nonemptiness is logically equivalent to the
production nontrivial/subsingleton split and does not add a global `Nontrivial E` assumption.

Then evaluate checklist items 12–14 explicitly:

- the empty supremum is exactly `0`, preserving the zero-dimensional convention;
- the ambient assumptions are exactly complete real inner-product, measurable, and Borel;
- no finite-dimensionality, global nontriviality, separability, probability, or stronger moment
  assumption appears;
- no Stage 4B eigenvalue, extended `lambdaMaxCovariance`, `toReal`, norm/finiteness/Poincaré bound,
  Euclidean specialization, final Issue 2 result, or extra declaration/import appears; and
- no `sorry`, axiom, escape hatch, IO/metaprogram, unrequested attribute/option, or diagnostic
  suppression appears.

Also comment on Mathlib naming and proof style, while treating a style preference as neither a
semantic failure nor a compiler diagnostic. Ask whether nonnegativity and the global boundary
pass, then wait.

### Phase 6 — final checklist, only on request

Proceed only when the user says they are ready to finalize. Produce all sixteen checklist items in
order with `PASS`, `FAIL`, or `NEEDS USER JUDGMENT`, one-sentence evidence, and exact file/line
references. Then provide:

- a difference table classified as semantic, API, proof-only, or documentation-only, with the
  pre-authorized direct Mathlib import identified as an API/harness-surface adjustment;
- a separate focused verdict on the expanded variance proof and explicit sphere-normalization
  proof;
- a list of any unresolved questions;
- your recommendation: accept, reject, or request a fresh repair run; and
- a final reminder that the user, not Claude, makes and records the acceptance decision.

Do not modify any file after giving the final review.

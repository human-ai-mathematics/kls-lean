# Stage 4A Run 1 human review

## Decision boundary

Run 1 is a stopped, zero-diagnostic mechanical pass stored under `review/pending/`. A human must
complete every item in `issue2_stage_4a_human_checklist.md` before the candidate may become the
experimental Stage 4B dependency. Do not send review findings or hidden production proof text
back to the stopped actor.

## Frozen files and hashes

```text
233e0297d99e52467e4ef7533af76f2310b23400ed720228361d540ffa36a90d  pending/CandidateStage4ARun1.lean
4619e0b269f591ffa7d4206aa06664bd4691a044161688e73116f7dfcffd90bc  external stage4a-trace-audit.json
```

The candidate is byte-identical to the stopped actor output at
`/private/tmp/humanize2-kls-issue2-stage4a-run1/actor-workspace/CandidateStage4A.lean`. Raw
transcripts, authentication, tokens, runtime state, and generated `.olean` files remain outside
Git.

## Open in Cursor

Open `Stage4ARun1Review.code-workspace` from this directory. The project pins Lean and Mathlib to
`v4.33.0`. If Cursor offers a newer `stable`, choose **Use Old Version**.

Run:

```bash
cd experiments/humanize2_kls_issue2_staged/review
lake build Stage4ARun1Review
```

Success requires exit zero and no warning or linter diagnostic. Then inspect
`pending/CandidateStage4ARun1.lean` declaration by declaration beside
`issue2_stage_4a_human_checklist.md` and `../SEMANTIC_DESIGN.md`.

## Independent harness reproduction

From the repository root:

```bash
export H2_ISSUE2_STAGE4A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage4a-run1
experiments/humanize2_kls_issue2_staged/scripts/stage_4a_verify_candidate.sh \
  "$H2_ISSUE2_STAGE4A_STATE_ROOT/actor-workspace"
experiments/humanize2_kls_issue2_staged/scripts/stage_4a_verify_oracle_pins.sh
jq '.ok, .errors, .actor_root_sessions, .actor_turns, .actor_descendants, \
    .actor_visible_files, .workspace_mutations, .tool_calls' \
  "$H2_ISSUE2_STAGE4A_STATE_ROOT/audit/stage4a-trace-audit.json"
```

Expected trace facts are `true`, `[]`, one root session, one turn, zero descendants, exactly the
thirteen declared actor-visible files, only `CandidateStage4A.lean` mutated, and nineteen local
`exec` calls.

## Semantic comparison already prepared

The fail-closed source and exact-surface checks prove the two imports occur in the frozen order,
the Borel ambient block is exact, the sole `@[simp]` attribute is present, and all eight declaration
types have the frozen API. The hidden production surface pin matches. A post-stop comparison found
no semantic or new declaration-API difference. The accepted experimental namespace remains an
API difference, and the second direct Mathlib import is the pre-accepted harness/API adjustment.

The remaining candidate-versus-production differences are proof-only:

- the representation lemma uses `simp [centeredCovarianceOperator]` rather than the direct
  `continuousLinearMapOfBilin_apply` theorem;
- symmetry and quadratic nonnegativity use explicit coercion/measure arguments;
- the variance identity expands `covarianceBilin_apply`, commutes the Riesz functional with the
  Bochner integral, and proves scalar covariance equality explicitly instead of applying
  `covarianceBilin_self`;
- the sphere formula proves equality of the two ranges by normalizing nonzero vectors and
  denormalizing unit vectors instead of invoking the generic `iSup` Rayleigh-sphere theorem; and
- nonnegativity splits on nonemptiness of the nonzero-vector subtype rather than on
  `Nontrivial E`.

Missing production docstrings are documentation-only. The longer variance and sphere proofs
deserve particular human inspection even though they compile at the exact frozen types. The actor
made eight exact Lean calls: the initial attempt failed, seven feedback-driven repairs followed,
and the eighth call was silent. Its final response labeled the repair count as eight by including
the initial implementation in that count.

## Human outcome

There are three valid next actions:

- **Accept:** record all sixteen checklist results in a new append-only decision, copy the
  candidate byte-for-byte to `accepted/AcceptedStage4A.lean`, and pin it before preparing Stage 4B.
- **Reject:** record the failed checklist item(s) and preserve this candidate unchanged.
- **Request repair:** freeze only non-oracular feedback and authorize another fresh isolated run.

No outcome automatically promotes production Lean or changes a theorem, dossier, ledger,
manuscript, or mathematical status. Stage 4B remains unauthorized.

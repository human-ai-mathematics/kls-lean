# Stage 2B Run 1 human review

## Decision boundary

Run 1 is a stopped, zero-diagnostic mechanical pass stored under `review/pending/`. A human must
complete every item in `issue2_stage_2b_human_checklist.md` before the candidate may become the
experimental Stage 3 dependency. Do not send review findings or hidden production proof text back
to the stopped actor.

## Frozen files and hashes

```text
69c2eead467fbc0516c191e034cedd1c8593bdaac50c1681912a429337b5dffc  pending/CandidateStage2BRun1.lean
69baf3ad061c0139692e6d3bbdaf66e6bfa3d376246d5d6becbf37f070cad74f  external stage2b-trace-audit.json
```

The candidate is byte-identical to the stopped actor output at
`/private/tmp/humanize2-kls-issue2-stage2b-run1/actor-workspace/CandidateStage2B.lean`. Raw
transcripts, authentication, and runtime state remain outside Git.

## Open in Cursor

Open `Stage2BRun1Review.code-workspace` from this directory. The project pins Lean and Mathlib to
`v4.33.0`. If Cursor offers a newer `stable`, choose **Use Old Version**.

Run:

```bash
cd experiments/humanize2_kls_issue2_staged/review
lake build Stage2BRun1Review
```

Success requires exit zero and no warning or linter diagnostic. Then inspect
`pending/CandidateStage2BRun1.lean` declaration by declaration beside
`issue2_stage_2b_human_checklist.md` and `../SEMANTIC_DESIGN.md`.

## Independent harness reproduction

From the repository root:

```bash
export H2_ISSUE2_STAGE2B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage2b-run1
experiments/humanize2_kls_issue2_staged/scripts/stage_2b_verify_candidate.sh \
  "$H2_ISSUE2_STAGE2B_STATE_ROOT/actor-workspace"
experiments/humanize2_kls_issue2_staged/scripts/stage_2b_verify_oracle_pins.sh
jq '.ok, .errors, .actor_root_sessions, .actor_turns, .actor_descendants, \
    .actor_visible_files, .workspace_mutations' \
  "$H2_ISSUE2_STAGE2B_STATE_ROOT/audit/stage2b-trace-audit.json"
```

Expected trace facts are `true`, `[]`, one root session, one turn, zero descendants, exactly the
nine declared actor-visible files, and only `CandidateStage2B.lean` mutated.

## Semantic comparison already prepared

The exact-surface checker proves that all three theorem types have the frozen API. A post-stop
comparison with the relevant `Poincare.lean` surface found no semantic or API difference. The
remaining differences are proof-only:

- the smoothness field uses the canonical Riesz functional `InnerProductSpace.toDual` directly
  instead of the definitionally equal `innerSL`;
- the projection `MemLp` field uses `MemLp.const_inner` directly instead of expressing the same
  fact through continuous-linear-map composition; and
- the variance theorem rewrites the energy equality and applies `HasPoincare.variance_le`
  explicitly instead of closing the same goal with `simpa`.

These observations assist review but do not complete the human checklist.

## Optional Claude-assisted interactive walkthrough

The user may use
`../prompts/issue2_stage_2b_claude5_fable_interactive_review.md` with Claude 5 Fable for a
read-only, phased walkthrough. Use it as an ordinary interactive conversation, not `/goal`.
Claude may reproduce evidence and recommend checklist outcomes, but the human user retains the
accept/reject decision. This optional post-stop review does not resume or provide feedback to the
actor.

## Human outcome

There are three valid next actions:

- **Accept:** record all sixteen checklist results in a new append-only decision, copy the
  candidate byte-for-byte to `accepted/AcceptedStage2B.lean`, and pin it before preparing Stage 3.
- **Reject:** record the failed checklist item(s) and preserve this candidate unchanged.
- **Request repair:** freeze only non-oracular feedback and authorize another fresh isolated run.

No outcome automatically promotes production Lean or changes a theorem, dossier, ledger,
manuscript, or mathematical status.

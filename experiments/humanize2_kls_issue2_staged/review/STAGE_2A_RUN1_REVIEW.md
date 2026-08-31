# Stage 2A Run 1 human review

## Decision boundary

Run 1 is a stopped, zero-diagnostic mechanical pass stored under `review/pending/`. A human must
complete every item in `issue2_stage_2a_human_checklist.md` before the candidate may become the
experimental Stage 2B dependency. Do not send review findings or hidden production proof text
back to the stopped actor.

## Frozen files and hashes

```text
83847c7ef06cd6045a1d5d5a8595f3fb645be28e8af4c71d3e577187fb0ad586  pending/CandidateStage2ARun1.lean
0be977e90fea1cf5019028c71e3faf90563b2ac990b55cf038396603a61828e1  external stage2a-trace-audit.json
```

The candidate is byte-identical to the stopped actor output at
`/private/tmp/humanize2-kls-issue2-stage2a-run1/actor-workspace/CandidateStage2A.lean`. Raw
transcripts, authentication, and runtime state remain outside Git.

## Open in Cursor

Open `Stage2ARun1Review.code-workspace` from this directory. The project pins Lean and Mathlib to
`v4.33.0`. If Cursor offers a newer `stable`, choose **Use Old Version**.

Run:

```bash
cd experiments/humanize2_kls_issue2_staged/review
lake build
```

Success requires exit zero and no warning or linter diagnostic. Then inspect
`pending/CandidateStage2ARun1.lean` declaration by declaration beside
`issue2_stage_2a_human_checklist.md` and `../SEMANTIC_DESIGN.md`.

## Independent harness reproduction

From the repository root:

```bash
export H2_ISSUE2_STAGE2A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage2a-run1
experiments/humanize2_kls_issue2_staged/scripts/stage_2a_verify_candidate.sh \
  "$H2_ISSUE2_STAGE2A_STATE_ROOT/actor-workspace"
experiments/humanize2_kls_issue2_staged/scripts/stage_2a_verify_oracle_pins.sh
jq '.ok, .errors, .actor_root_sessions, .actor_turns, .actor_descendants, \
    .actor_visible_files, .workspace_mutations' \
  "$H2_ISSUE2_STAGE2A_STATE_ROOT/audit/stage2a-trace-audit.json"
```

Expected trace facts are `true`, `[]`, one root session, one turn, zero descendants, exactly the
seven declared actor-visible files, and only `CandidateStage2A.lean` mutated.

## Semantic comparison already prepared

The exact-surface checker proves that all five declaration types and both `@[simp]` attributes
have the frozen API. A post-stop comparison with the relevant `Poincare.lean` surface found no
semantic or API difference. The remaining differences are proof-only:

- both definitional equalities are written as explicit `by rfl` proofs;
- the gradient witness changes the goal directly to the Fréchet derivative of the inner-product
  functional; and
- it applies the canonical `InnerProductSpace.toDual` continuous-linear-map derivative theorem
  directly before deriving the gradient formula.

These observations assist review but do not complete the human checklist.

## Optional Claude-assisted interactive walkthrough

The user may use
`../prompts/issue2_stage_2a_claude5_fable_interactive_review.md` with Claude 5 Fable for a
read-only, phased walkthrough. Use it as an ordinary interactive conversation, not `/goal`.
Claude may reproduce evidence and recommend checklist outcomes, but the human user retains the
accept/reject decision. This optional post-stop review does not resume or provide feedback to the
actor.

## Human outcome

There are three valid next actions:

- **Accept:** record all sixteen checklist results in a new append-only decision, copy the
  candidate byte-for-byte to `accepted/AcceptedStage2A.lean`, and pin it before preparing Stage 2B.
- **Reject:** record the failed checklist item(s) and preserve this candidate unchanged.
- **Request repair:** freeze only non-oracular feedback and authorize another fresh isolated run.

No outcome automatically promotes production Lean or changes a theorem, dossier, ledger,
manuscript, or mathematical status.

# Stage 1B Run 3 human review

## Decision boundary

Run 3 is a stopped, zero-diagnostic mechanical pass. It is deliberately stored under
`review/pending/`, not `accepted/`. A human must complete every item in
`issue2_stage_1b_human_checklist.md` before the candidate may become the experimental Stage 2A
dependency. Do not send review findings or hidden reference proof text back to the stopped actor.

## Frozen files and hashes

```text
027e69674f78eb735b380b18beaf43e55779e0634d7222f46681f1bae30b752d  pending/CandidateStage1BRun3.lean
be9972dacfcf56a0af3e5bb61ea3ad12a7757a0d3c2ff0863f4ade8fce98aa44  external stage1b-trace-audit.json
```

The candidate is byte-identical to the stopped actor output at
`/private/tmp/humanize2-kls-issue2-stage1b-run3/actor-workspace/CandidateStage1B.lean`. Raw
transcripts, authentication, and runtime state remain outside Git.

## Open in Cursor

Open `Stage1BRun3Review.code-workspace` from this directory. The review project pins Lean and
Mathlib to `v4.33.0`; its default target is only the Run 3 candidate. Cursor may ask whether to use
the old pinned version because `stable` has advanced. Choose **Use Old Version**.

Run:

```bash
cd experiments/humanize2_kls_issue2_staged/review
lake build
```

Success requires exit zero and no warning or linter diagnostic. Then inspect
`pending/CandidateStage1BRun3.lean` declaration by declaration beside
`issue2_stage_1b_human_checklist.md` and `../SEMANTIC_DESIGN.md`.

## Independent harness reproduction

From the repository root:

```bash
export H2_ISSUE2_STAGE1B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1b-run3
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_verify_candidate.sh \
  "$H2_ISSUE2_STAGE1B_STATE_ROOT/actor-workspace"
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_verify_oracle_pins.sh
jq '.ok, .errors, .actor_root_sessions, .actor_turns, .actor_descendants, \
    .actor_visible_files, .workspace_mutations' \
  "$H2_ISSUE2_STAGE1B_STATE_ROOT/audit/stage1b-trace-audit.json"
```

Expected trace facts are `true`, `[]`, one root session, one turn, zero descendants, exactly the
five declared actor-visible files, and only `CandidateStage1B.lean` mutated.

## Semantic comparison already prepared

The exact-surface checker proves that all thirteen declaration types have the frozen API. A
post-stop comparison with `formalization/FunctionalInequalities/Basic.lean` found no new statement
or definition difference in this layer beyond the already accepted Stage 1A binder choice and the
experimental namespace. The remaining differences are proof-only:

- the Riesz-isometry norm fact is applied by unfolding `gradient` and rewriting with
  `LinearIsometryEquiv.norm_map`;
- the two energy integrands are identified almost everywhere via `integral_congr_ae`;
- the infimum bounds use standard complete-lattice lemmas; and
- the finite-versus-`⊤` proof derives a contradiction from `ENNReal.coe_lt_top` without `simpa`.

These observations assist review but do not complete the human checklist.

## Human outcome

There are three valid next actions:

- **Accept:** record all fourteen checklist results in a new append-only decision, copy the
  candidate byte-for-byte to `accepted/AcceptedStage1B.lean`, and pin it before preparing Stage 2A.
- **Reject:** record the failed checklist item(s) and preserve this candidate unchanged.
- **Request repair:** freeze only non-oracular feedback and authorize another fresh isolated run.

No outcome promotes production Lean or changes a theorem, dossier, ledger, manuscript, or
mathematical status.

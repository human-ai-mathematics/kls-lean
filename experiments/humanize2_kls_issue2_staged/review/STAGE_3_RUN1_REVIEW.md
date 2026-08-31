# Stage 3 Run 1 human review

## Decision boundary

Run 1 is a stopped, zero-diagnostic mechanical pass stored under `review/pending/`. A human must
complete every item in `issue2_stage_3_human_checklist.md` before the candidate may become the
experimental Stage 4 dependency. Do not send review findings or hidden production proof text back
to the stopped actor.

## Frozen files and hashes

```text
4b4a6950fa80b4bd13ea291ff25955b9dca075de52c92e1900783066ce8a0583  pending/CandidateStage3Run1.lean
cfbb822a10d60d1175fb2a5178f0a64aa56bbc6ba62521ff706dd9695995f8cd  external stage3-trace-audit.json
```

The candidate is byte-identical to the stopped actor output at
`/private/tmp/humanize2-kls-issue2-stage3-run1/actor-workspace/CandidateStage3.lean`. Raw
transcripts, authentication, tokens, runtime state, and generated `.olean` files remain outside
Git.

## Open in Cursor

Open `Stage3Run1Review.code-workspace` from this directory. The project pins Lean and Mathlib to
`v4.33.0`. If Cursor offers a newer `stable`, choose **Use Old Version**.

Run:

```bash
cd experiments/humanize2_kls_issue2_staged/review
lake build Stage3Run1Review
```

Success requires exit zero and no warning or linter diagnostic. Then inspect
`pending/CandidateStage3Run1.lean` declaration by declaration beside
`issue2_stage_3_human_checklist.md` and `../SEMANTIC_DESIGN.md`.

## Independent harness reproduction

From the repository root:

```bash
export H2_ISSUE2_STAGE3_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage3-run1
experiments/humanize2_kls_issue2_staged/scripts/stage_3_verify_candidate.sh \
  "$H2_ISSUE2_STAGE3_STATE_ROOT/actor-workspace"
experiments/humanize2_kls_issue2_staged/scripts/stage_3_verify_oracle_pins.sh
jq '.ok, .errors, .actor_root_sessions, .actor_turns, .actor_descendants, \
    .actor_visible_files, .workspace_mutations, .tool_calls' \
  "$H2_ISSUE2_STAGE3_STATE_ROOT/audit/stage3-trace-audit.json"
```

Expected trace facts are `true`, `[]`, one root session, one turn, zero descendants, exactly the
eleven declared actor-visible files, only `CandidateStage3.lean` mutated, and six local `exec`
calls.

## Semantic comparison already prepared

The exact-surface checker proves that all five declaration types have the frozen API. A post-stop
comparison with the relevant `Poincare.lean` surface found no semantic or new API difference. The
remaining candidate-versus-production differences are proof-only:

- the global quotient bound splits explicitly into zero- and positive-energy cases instead of
  using `ENNReal.div_le_of_le_mul` directly;
- the positive-energy equality applies `ENNReal.ofReal_div_of_pos` by symmetry instead of `rw`;
  and
- the zero-energy theorem names the positive numerator witness and normalizes
  `ENNReal.ofReal_zero` with `simpa only`.

The pre-accepted experimental namespace is an API difference from production, and missing
docstrings are documentation-only. These observations assist review but do not complete the
human checklist.

## Human outcome

There are three valid next actions:

- **Accept:** record all sixteen checklist results in a new append-only decision, copy the
  candidate byte-for-byte to `accepted/AcceptedStage3.lean`, and pin it before preparing Stage 4.
- **Reject:** record the failed checklist item(s) and preserve this candidate unchanged.
- **Request repair:** freeze only non-oracular feedback and authorize another fresh isolated run.

No outcome automatically promotes production Lean or changes a theorem, dossier, ledger,
manuscript, or mathematical status.

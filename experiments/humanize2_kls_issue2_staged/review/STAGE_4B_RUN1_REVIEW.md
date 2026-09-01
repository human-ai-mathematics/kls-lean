# Stage 4B Run 1 human review

## Decision boundary

Run 1 is a stopped, zero-diagnostic mechanical pass stored under `review/pending/`. A human must
complete every item in `issue2_stage_4b_human_checklist.md` before the candidate may become any
later experimental dependency. Do not send review findings or hidden production proof text back
to the stopped actor.

## Frozen files and hashes

```text
610e9006ffe2e03beb83ec6ec811cfb58ae67621867e191c371264b2066a3188  pending/CandidateStage4BRun1.lean
403c3cfb5eb43fd42329f1292c179509efb46244e44c67492aae118c807b04bd  external stage4b-trace-audit.json
```

The candidate is byte-identical to the stopped actor output at
`/private/tmp/humanize2-kls-issue2-stage4b-run1/actor-workspace/CandidateStage4B.lean`. Raw
transcripts, authentication, tokens, runtime state, and generated `.olean` files remain outside
Git.

## Independent review build

Open `Stage4BRun1Review.code-workspace` from this directory. The project pins Lean and Mathlib to
`v4.33.0`. If an editor offers a newer `stable`, choose **Use Old Version**.

Run:

```bash
cd experiments/humanize2_kls_issue2_staged/review
lake build Stage4BRun1Review
```

The recorded build completed successfully in 2,947 jobs. Success requires no warning, linter
suggestion, or style diagnostic.

## Independent harness reproduction

From the repository root:

```bash
export H2_ISSUE2_STAGE4B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage4b-run1
experiments/humanize2_kls_issue2_staged/scripts/stage_4b_verify_candidate.sh \
  "$H2_ISSUE2_STAGE4B_STATE_ROOT/actor-workspace"
experiments/humanize2_kls_issue2_staged/scripts/stage_4b_verify_oracle_pins.sh
jq '{ok, errors, actor_root_sessions, actor_turns, actor_descendants, actor_visible_files, \
     workspace_mutations, tool_calls}' \
  "$H2_ISSUE2_STAGE4B_STATE_ROOT/audit/stage4b-trace-audit.json"
```

Expected trace facts are `true`, `[]`, one root session, one turn, zero descendants, fifteen
declared actor-visible files, only `CandidateStage4B.lean` mutated, and five local `exec` calls.
The second exact Lean call was silent after one feedback-driven repair iteration.

## Semantic comparison already prepared

The exact surface, local instance placement, sole attribute, single import, hidden production pin,
and all boundary checks passed. Post-stop comparison found no semantic or declaration-API
difference. The namespace remains an accepted API difference, missing docstrings are
documentation-only, and all proof differences are listed in the Run 1 exploration.

Give particular attention to:

- the eigenvalue theorem's exact local instances and symmetric Rayleigh--Ritz application;
- both dimension branches of the operator-norm and fixed-Poincaré bounds;
- the fixed bound's use of the accepted covariance-variance identity and linear-test inequality;
- the optimal bound's `le_optimalPoincareConstant` quantification and coercion simplification; and
- the direct `ENNReal.ofReal` proof of `lambdaMaxCovariance_ne_top`, which is valid but does not
  route through the operator-norm theorem as production does.

## Human outcome

There are three valid next actions:

- **Accept:** record all sixteen checklist results in a new append-only decision and copy the
  candidate byte-for-byte into a newly authorized accepted layer.
- **Reject:** record the failed checklist item or items and preserve the candidate unchanged.
- **Request repair:** freeze only non-oracular feedback and authorize another fresh isolated run.

No outcome automatically promotes production Lean or changes a theorem, dossier, ledger,
manuscript, or mathematical status.

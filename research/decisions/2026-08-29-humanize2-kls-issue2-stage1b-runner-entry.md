# Clarify the guarded Stage 1B runner entry

- **Date:** 2026-08-29
- **Type:** experiment handoff and runner-entry correction
- **Scope:** `experiments/humanize2_kls_issue2_staged/`
- **Mathematical effect:** none

## Feedback and observed behavior

An attempt to paste the Stage 1B actor prompt into a normal repository task stopped without editing
or compiling `CandidateStage1B.lean` because that task was not the isolated five-entry actor
workspace. This is the intended safety behavior. The actor prompt is an internal input consumed
only by `scripts/stage_1b_run.sh`; it is not a repository-task prompt.

The model-free harness-setup prompt had already been completed by commit `666fff6`, with its handoff
recorded by `e5f12b2`. Mark that setup prompt historical so it is not selected again after the
harness exists.

A read-only login-status check also exposed an entry-order defect in the handoff. On a fresh state,
the path `/private/tmp/humanize2-kls-issue2-stage1b/actor-codex-home` does not exist, and Codex exits
`1` rather than creating a missing `CODEX_HOME`. The prior command block put `codex login` before
the reset that creates this directory.

## Decision

The only live entry is the guarded runner sequence:

```bash
export H2_ISSUE2_STAGE1B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1b
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_reset_run_state.sh
CODEX_HOME="$H2_ISSUE2_STAGE1B_STATE_ROOT/actor-codex-home" codex login
export H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-human-review
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_run.sh
```

The first reset creates the dedicated home and frozen fixture. The runner's second reset preserves
only the experiment-specific `auth.json` and reestablishes every deterministic gate before the
model call. Do not paste the actor prompt into any desktop task and do not reuse the Stage 1A login.

The corrected first reset exited `0` and created the dedicated actor home. The immediately
following `codex login status` exited `1` with the normal result `Not logged in`, rather than the
configuration error for a nonexistent `CODEX_HOME`. No login flow was started.

No model call, candidate edit, candidate compilation, proof attempt, review, certification,
ledger/manuscript change, or mathematical status change resulted from the rejected prompt or the
login-status check.

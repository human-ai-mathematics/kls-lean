# Add a Claude-assisted interactive review for Stage 4B Run 1

Date: 2026-09-01

## Decision

After valid Stage 4B Run 1 reached the human-review stop, add a reviewer-only Claude 5 Fable
prompt at
`experiments/humanize2_kls_issue2_staged/prompts/issue2_stage_4b_claude5_fable_interactive_review.md`.

This is a post-stop review aid, not an actor, automatic acceptance mechanism, or model reviewer
inside the reconstruction harness. Claude may reproduce committed mechanical evidence, inspect
the stopped candidate and accepted sources, and compare the eight relevant production
declarations because the actor session has ended. It must not contact or provide feedback to the
stopped actor.

## Interaction and authority boundary

The prompt uses seven phases and requires Claude to pause after workspace, mechanical,
eigenvalue/packaging, operator-norm/finiteness, fixed-Poincaré, and optimal-Poincaré/global-
boundary checks. It produces the final sixteen-item matrix only when the user explicitly asks to
finalize. Claude may label evidence and recommend an outcome, but only the user may accept the
candidate.

The reviewer is read-only apart from ignored Lean build artifacts and performs the review itself
without delegation. It may read the compact external trace audit but not raw sessions, client
state, credentials, or accepted `.olean` files. It may not edit the candidate, create an accepted
copy or acceptance decision, start another run, promote production code, certify a dossier, or
change a ledger or manuscript.

## High-attention proof boundary

The prompt gives dedicated high-attention review to the eigenvalue theorem, the fixed Poincaré
bound, and the optimal Poincaré bound. It also makes the proof-only finiteness divergence explicit:
the candidate proves `lambdaMaxCovariance_ne_top` directly from `ENNReal.ofReal`, whereas
production routes through the operator-norm bound. Claude must verify kernel validity separately
from asking the user whether the checklist's proof-correspondence wording makes that divergence a
policy issue.

## Workspace failure prevention

The prompt fixes the required root as `/private/tmp/kls-lean-autoformalization-experiments`, branch
`autoformalization-experiments`, recorded result commit
`a34068d68a93d78a4f0d7ab02af469f09f638e74`, candidate hash `610e9006…6a3188`, and compact trace
hash `403c3cfb…04bd`. If Claude starts elsewhere, it must stop after one identity check rather than
search, copy fixtures, or repeat an invalid audit. The prompt is an ordinary interactive
conversation, not an autonomous `/goal`, so its pause points remain meaningful.

## Validation

The prompt's mechanical commands were reproduced from the stated directory before this record.
The candidate pin passed, `Stage4BRun1Review` built 2,947 jobs without warnings or linter
diagnostics, the exact single-import/eight-declaration verifier passed silently, the hidden
production pin matched, and the compact trace satisfied one session, one turn, zero descendants,
five local `exec` calls, fifteen visible files, and candidate-only mutation.

Prompt SHA-256:

```text
379d6fbc6dc98aa6ce830fdf3d22ef319005d699bc2a56b7abac74954a8bc235
```

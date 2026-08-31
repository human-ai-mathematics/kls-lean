# Add a Claude-assisted interactive review for Stage 2B Run 1

Date: 2026-09-01

## Decision

After valid Stage 2B Run 1 reached the human-review stop, the user asked for a Claude validation
prompt. Add a reviewer-only Claude 5 Fable prompt at
`experiments/humanize2_kls_issue2_staged/prompts/issue2_stage_2b_claude5_fable_interactive_review.md`.

This is a post-stop review aid, not an actor, automatic acceptance mechanism, or model reviewer
inside the reconstruction harness. Claude may reproduce the committed mechanical evidence,
inspect the stopped candidate and accepted sources, and compare the three relevant production
declarations because the actor session has ended. It must not contact or provide feedback to the
stopped actor.

## Interaction and authority boundary

The prompt uses six phases and requires Claude to pause for the user's judgment after workspace,
mechanical, energy, admissibility, and variance/global-boundary checks. It produces the final
sixteen-item matrix only when the user explicitly asks to finalize. Claude may label evidence and
recommend an outcome, but only the user may accept the candidate as the Stage 3 experimental
dependency.

The reviewer is read-only apart from ignored Lean build artifacts. It may read the compact
external trace audit but not raw sessions, client state, credentials, or accepted `.olean` files.
It may not edit the candidate, create an accepted copy or decision, start Stage 3, promote
production code, certify a dossier, or change a ledger or manuscript.

## Workspace failure prevention

The prompt fixes the required root as `/private/tmp/kls-lean-autoformalization-experiments`, branch
`autoformalization-experiments`, result commit
`e14bfb036d5cc511bda2415c4d10df416c81e1d5`, and candidate hash `69c2eead…5dffc`. If Claude
starts elsewhere, it must stop after one identity check rather than search, copy fixture files, or
repeat an invalid workspace audit. The prompt should be used as an ordinary interactive
conversation, not an autonomous `/goal`, so its explicit pause points remain meaningful.

## Validation

The complete mechanical command block in the prompt was reproduced from the stated directory.
The candidate pin passed, the dedicated `Stage2BRun1Review` target built with no warning or linter
diagnostic, the independent exact-surface candidate verifier passed silently, the hidden
production-surface pin matched, and the compact trace query satisfied the recorded one-session,
one-turn, zero-descendant, six-local-exec, candidate-only result.

Prompt SHA-256:

```text
de2e27e8f8d937ca5a0c498f0f6de1ae85f9a9b1bd11765af65011d0136de0de
```

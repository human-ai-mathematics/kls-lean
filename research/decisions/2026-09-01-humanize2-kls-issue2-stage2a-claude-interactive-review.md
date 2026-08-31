# Add a Claude-assisted interactive review for Stage 2A Run 1

Date: 2026-09-01

## Decision

After valid Stage 2A Run 1 reached the human-review stop, the user asked for a prompt allowing
Claude 5 Fable to check the candidate interactively. Add a reviewer-only prompt at
`experiments/humanize2_kls_issue2_staged/prompts/issue2_stage_2a_claude5_fable_interactive_review.md`.

This is a post-stop review aid, not an actor, automatic acceptance mechanism, or model reviewer
inside the reconstruction harness. Claude may reproduce the committed mechanical evidence,
inspect the stopped candidate and accepted sources, and compare the five relevant production
declarations because the actor session has already ended. It must not contact or provide feedback
to the stopped actor.

## Interaction and authority boundary

The prompt uses five phases and requires Claude to pause for the user's judgment after workspace,
mechanical, elementary-declaration, gradient, and global-boundary checks. It produces the final
sixteen-item matrix only when the user explicitly asks to finalize. Claude may label evidence and
recommend an outcome, but only the user may accept the candidate as the Stage 2B experimental
dependency.

The reviewer is read-only apart from ignored Lean build artifacts. It may read the compact external
trace audit but not raw sessions, client state, credentials, or accepted `.olean` files. It may not
edit the candidate, create an accepted copy or decision, start Stage 2B, promote production code,
certify a dossier, or change a ledger or manuscript.

## Workspace failure prevention

The prompt fixes the required root as `/private/tmp/kls-lean-autoformalization-experiments`, branch
`autoformalization-experiments`, result commit `632a5fc`, and candidate hash `83847c7e…0ad586`.
If Claude starts elsewhere, it must stop after one identity check rather than search, copy fixture
files, or repeat the three-audit failure from the invalid actor pre-run. The reviewer prompt should
be used as an ordinary interactive conversation, not an autonomous `/goal`, so its explicit pause
points remain meaningful.

## Validation

The complete mechanical command block in the prompt was executed from the stated directory. The
candidate pin passed, the review project built all 2,929 jobs with no warning or linter diagnostic,
the independent exact-surface candidate verifier passed silently, the hidden production-surface
pin matched, and the compact trace query satisfied the recorded one-session, one-turn,
zero-descendant, candidate-only result.

Prompt SHA-256:

```text
38f5ae13f318a03590f0f290f7ea5637e83355133fa4a3c9f16ce596cfd42757
```

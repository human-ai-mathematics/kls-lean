# Add a Claude-assisted interactive review for Stage 4A Run 1

Date: 2026-09-01

## Decision

After valid Stage 4A Run 1 reached the human-review stop, the user asked for a Claude validation
prompt. Add a reviewer-only Claude 5 Fable prompt at
`experiments/humanize2_kls_issue2_staged/prompts/issue2_stage_4a_claude5_fable_interactive_review.md`.

This is a post-stop review aid, not an actor, automatic acceptance mechanism, or model reviewer
inside the reconstruction harness. Claude may reproduce the committed mechanical evidence,
inspect the stopped candidate and accepted sources, and compare the eight relevant production
declarations because the actor session has ended. It must not contact or provide feedback to the
stopped actor.

## Interaction and authority boundary

The prompt uses seven phases and requires Claude to pause for the user's judgment after workspace,
mechanical, represented-operator, variance-identity, sphere-formula, and nonnegativity/global-
boundary checks. It produces the final sixteen-item matrix only when the user explicitly asks to
finalize. Claude may label evidence and recommend an outcome, but only the user may accept the
candidate as the Stage 4B experimental dependency.

The reviewer is read-only apart from ignored Lean build artifacts and performs the review itself
without delegation. It may read the compact external trace audit but not raw sessions, client
state, credentials, or accepted `.olean` files. It may not edit the candidate, create an accepted
copy or decision, start or authorize Stage 4B, promote production code, certify a dossier, or
change a ledger or manuscript.

## High-attention proof boundary

The candidate's expanded `centeredCovarianceOperator_self_eq_variance` proof and explicit
range-normalization proof of `covarianceRayleighMax_eq_iSup_covariance_sphere` are materially
longer than production. The prompt therefore gives each its own interactive phase and requires
line-by-line verification of integrability, Bochner-integral commutation, covariance integrands,
normalization, range equality, and the zero-dimensional empty-range case. Compilation and exact
surface agreement are not treated as substitutes for this semantic inspection.

## Workspace failure prevention

The prompt fixes the required root as `/private/tmp/kls-lean-autoformalization-experiments`, branch
`autoformalization-experiments`, result commit
`3aa4ea4f4b6ed537734126f3f9de02be29238dca`, and candidate hash `233e0297…36a90d`. If Claude
starts elsewhere, it must stop after one identity check rather than search, copy fixture files, or
repeat an invalid workspace audit. The prompt should be used as an ordinary interactive
conversation, not an autonomous `/goal`, so its explicit pause points remain meaningful.

## Validation

The complete mechanical command block in the prompt was reproduced from the stated directory.
The candidate pin passed, the dedicated `Stage4ARun1Review` target built with no warning or linter
diagnostic, the fail-closed ordered-import and exact eight-declaration verifier passed silently,
the hidden production-surface pin matched, and the compact trace query satisfied the recorded
one-session, one-turn, zero-descendant, nineteen-local-exec, candidate-only result.

Prompt SHA-256:

```text
10170e8167cc47ac7c74e3e3a3b369e508ee04095fbb26c87c317276b90f1010
```

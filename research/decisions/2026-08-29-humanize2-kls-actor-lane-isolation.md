# Isolate the Humanize2 KLS actor lane from delegated review

- **Date:** 2026-08-29
- **Type:** agent harness correction and run classification
- **Scope:** `experiments/humanize2_kls_statement_fidelity/`
- **Mathematical effect:** none

## Observation

The first authenticated statement-fidelity run exited successfully, produced a compiling candidate,
and received `done: true` from the official read-only RLAR reviewer. Independent verification also
accepted the candidate, whose SHA-256 was
`fe594274d55934a6152a8be813c549682a930adac6952720583ae9ed6137990d`.

The trace audit nevertheless invalidated the run as a blinded calibration. The statement-generating
child actor read only `AGENTS.md`, the frozen input, `Basic.lean`, `Poincare.lean`, and the candidate,
then edited the candidate and compiled it. However, its parent actor session interpreted the full
actor/reviewer task as an orchestration request, spawned its own reviewer child, and received that
child's oracle-backed findings before the actor session ended. That descendant read the pinned
certificate, solution, semantic follow-up, and knowledge summary. The candidate was generated and
compiled before those reads and was not edited afterward, but the actor lane as a whole crossed the
declared oracle boundary.

Classify this run as **functional success / blind-validity failure**. It is not a passing benchmark
under the acceptance criteria in `docs/HUMANIZE2_KLS_EXPERIMENT_HANDOFF.md`.

## Decision

Reset the candidate to the committed sentinel and repeat the run in fresh Humanize state. Strengthen
the shared RLAR prompt so each session must perform exactly its assigned role and must not delegate,
spawn subagents, or use collaboration tools. State explicitly that the actor must stop after the
actor instructions and must neither perform nor delegate oracle-backed review.

Continue to audit the complete actor session tree after the retry. Prompt enforcement remains weaker
than filesystem isolation; a future hardened benchmark should run the actor against an oracle-free
repository snapshot.

## Validation boundary

The correction is accepted only if the reset scaffold passes, the repository is clean before the
retry, and the next actor session tree contains no forbidden oracle read or delegated child. The
candidate must still satisfy the existing compiler, semantic, placeholder, pin, and Git-scope gates.

No ledger, manuscript statement, theorem, proof dossier, review certification, or mathematical
status changes as a result of either run.

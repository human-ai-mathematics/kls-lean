# Stage 2A wrong-workspace pre-run

Date: 2026-08-31

## Intended action

The user pasted the frozen Stage 2A actor prompt into a new Codex task titled “Implement Stage 2A
Lean geometry.” The intended workspace was the seven-entry external fixture.

## Observed failure

The task instead started at `/Users/lyuyuwei/Documents/ChatGPT/KLS`. It found that checkout's root
`AGENTS.md` symlink but none of `TASK.md`, the accepted Stage 1A/1B source/compiled pairs, or
`CandidateStage2A.lean`. It made no file change and, after three consecutive unchanged audits,
reported a workspace-restoration blocker.

This is an invalid pre-run, not Stage 2A Run 1: the model saw the wrong repository contract, never
saw the frozen task or accepted dependencies, never edited a candidate, and never invoked Lean on
the Stage 2A fixture. The task must not be resumed or counted as reconstruction evidence.

## Resolution

The external fixture was restored at
`/private/tmp/humanize2-kls-issue2-stage2a-run1/actor-workspace`. Its exact seven files, source and
compiled dependency hashes, read-only modes, candidate-only write mode, oracle pin, and expected
compiler-failing sentinel all passed the pre-model scaffold verifier. Because a Codex task's
working directory cannot be repaired into this isolated external root without weakening the
boundary, a fresh Humanize2-managed actor session is required.

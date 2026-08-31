# Authorize the isolated Issue 2 Stage 2A live run

Date: 2026-08-31

## Authorization

After the Stage 2A prompt package was frozen, the user attempted to start the actor in a Codex
task, learned that the task had the wrong workspace, and then explicitly said “我授权” when asked
whether to complete the isolated runner and actually call the model.

This authorizes one subscription-authenticated Stage 2A Run 1. The model may receive only:

- the frozen Stage 2A actor prompt and `TASK.md` specification;
- the actor-only `AGENTS.md` contract;
- the human-accepted `AcceptedStage1A.lean` and `AcceptedStage1B.lean` sources;
- their toolchain-matched compiled dependencies, which the actor may import but not inspect;
- the reset `CandidateStage2A.lean`; and
- actual Lean 4.33.0 diagnostics produced inside the isolated actor workspace.

The authorization does not permit exposing the production `FunctionalInequalities` sources,
hidden oracle pin or known-good fixture, solutions, certificates, reviews, ledgers, semantic design
notes, later stages, another KLS target, credentials, transcripts, or client state. It does not
authorize a model reviewer, a subagent, production promotion, proof certification, or a ledger or
manuscript change.

## Run and stop boundary

Run 1 must use the fresh dedicated root
`/private/tmp/humanize2-kls-issue2-stage2a-run1`, a directly authenticated experiment-specific
`CODEX_HOME`, one root actor session, one turn, zero descendants, and a deny-default macOS Seatbelt
profile. Only the existing `CandidateStage2A.lean` path may be mutated. The seven actor-visible
files, prompt, accepted dependencies, Lean/Lake metadata, Humanize2 adapter, isolation policy,
verifier, and complete-trace auditor must be pinned and pass their model-free gates before the
model call.

After the actor stops, the independent mechanical verifier must require the exact five-declaration
surface and a silent compiler command. The complete trace must be audited before any human review.
Regardless of the result, Run 1 stops at
`review/issue2_stage_2a_human_checklist.md`; no acceptance or mathematical status follows
automatically.

## Pre-model validation

The live runner was completed without calling the model. Its aggregate pin now includes the
Stage 2A Seatbelt template and isolated Codex configuration, one-turn Humanize2 flow, pinned
Humanize2 adapter patch, run-state reset, config renderer, guarded runner, complete-trace auditor,
auditor unit tests, physical isolation battery, and the earlier exact candidate/scaffold checks.

The full model-free suite passed: deterministic recompilation of both accepted dependencies,
exact seven-entry resets, expected sentinel failure, silent known-good candidate and exact-surface
compilation, axiom and diagnostic-suppression rejection, candidate-only physical writes, denial of
the production/reference/oracle/review/client-state paths, a Seatbelt-wrapped Codex app-server
probe, complete-trace adversarial tests, and exit `2` for both missing acknowledgement and missing
dedicated authentication. The actual Run 1 root was then reset and the pinned Humanize2 adapter
prepared successfully. Its dedicated `CODEX_HOME` reports `Not logged in`; no valid model call has
yet occurred.

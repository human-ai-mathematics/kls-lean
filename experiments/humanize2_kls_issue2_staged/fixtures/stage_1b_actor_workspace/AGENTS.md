# Issue 2 Stage 1B actor contract

This is an isolated reconstruction fixture. Work directly in this one session and edit only
`CandidateStage1B.lean`.

Read `AGENTS.md`, `TASK.md`, `AcceptedStage1A.lean`, and `CandidateStage1B.lean`. Do not inspect the
compiled `AcceptedStage1A.olean`. The accepted source and compiled dependency are immutable.

Do not spawn or delegate to another agent, invoke collaboration, act as a reviewer, use web,
browser, MCP, plugin, or network tools, inspect runtime/client state, or access any path outside
this workspace. Do not create, rename, or delete files or use proof escape hatches. After every
edit run exactly `lean CandidateStage1B.lean`, and continue until it exits zero and the frozen
Stage 1B requirements are all implemented.

Compilation is not acceptance. A human reviewer decides whether the stopped candidate may become
an input to Stage 2A.

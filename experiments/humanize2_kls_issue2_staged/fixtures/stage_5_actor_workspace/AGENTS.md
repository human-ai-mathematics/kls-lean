# Issue 2 Stage 5 actor contract

This is an isolated reconstruction fixture. Work directly in this one session and edit only
`CandidateStage5.lean`.

Read `AGENTS.md`, `TASK.md`, `AcceptedStage1A.lean`, `AcceptedStage1B.lean`,
`AcceptedStage2A.lean`, `AcceptedStage2B.lean`, `AcceptedStage3.lean`,
`AcceptedStage4A.lean`, `AcceptedStage4B.lean`, and `CandidateStage5.lean`. Do not inspect any
compiled `.olean` dependency. All accepted dependencies are immutable.

Do not spawn or delegate to another agent, invoke collaboration, act as a reviewer, use web,
browser, MCP, plugin, or network tools, inspect runtime/client state, or access any path outside
this workspace. Do not create, rename, or delete files or use proof/diagnostic escape hatches.
After every edit run exactly `lean CandidateStage5.lean`, and continue until it exits zero with no
output and the three frozen Stage 5 theorems are all implemented.

Compilation is not acceptance. A human reviewer decides whether the stopped candidate completes
the staged experimental reconstruction.

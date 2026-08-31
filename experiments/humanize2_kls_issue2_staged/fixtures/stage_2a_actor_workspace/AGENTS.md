# Issue 2 Stage 2A actor contract

This is an isolated reconstruction fixture. Work directly in this one session and edit only
`CandidateStage2A.lean`.

Read `AGENTS.md`, `TASK.md`, `AcceptedStage1A.lean`, `AcceptedStage1B.lean`, and
`CandidateStage2A.lean`. Do not inspect either compiled `.olean` dependency. All accepted
dependencies are immutable.

Do not spawn or delegate to another agent, invoke collaboration, act as a reviewer, use web,
browser, MCP, plugin, or network tools, inspect runtime/client state, or access any path outside
this workspace. Do not create, rename, or delete files or use proof/diagnostic escape hatches.
After every edit run exactly `lean CandidateStage2A.lean`, and continue until it exits zero with no
output and the five frozen Stage 2A declarations are all implemented.

Compilation is not acceptance. A human reviewer decides whether the stopped candidate may become
an input to Stage 2B.

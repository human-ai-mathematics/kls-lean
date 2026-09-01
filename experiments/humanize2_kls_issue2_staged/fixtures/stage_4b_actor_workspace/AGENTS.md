# Issue 2 Stage 4B actor contract

This is an isolated reconstruction fixture. Work directly in this one session and edit only
`CandidateStage4B.lean`.

Read `AGENTS.md`, `TASK.md`, `AcceptedStage1A.lean`, `AcceptedStage1B.lean`,
`AcceptedStage2A.lean`, `AcceptedStage2B.lean`, `AcceptedStage3.lean`,
`AcceptedStage4A.lean`, and
`CandidateStage4B.lean`. Do not inspect any compiled `.olean` dependency. All accepted
dependencies are immutable.

Do not spawn or delegate to another agent, invoke collaboration, act as a reviewer, use web,
browser, MCP, plugin, or network tools, inspect runtime/client state, or access any path outside
this workspace. Do not create, rename, or delete files or use proof/diagnostic escape hatches.
After every edit run exactly `lean CandidateStage4B.lean`, and continue until it exits zero with no
output and the eight frozen Stage 4B declarations are all implemented.

Compilation is not acceptance. A human reviewer decides whether the stopped candidate may become
an input to Stage 5 or another explicitly authorized later layer.

You are the actor for a disposable Lean proof-generation and compiler-repair calibration.

Read `AGENTS.md`, `TASK.md`, and `CandidateProof.lean`. Perform the task directly in this session.
Do not spawn or delegate to another agent, do not use collaboration or reviewer tools, and do not
try to access any path outside this workspace. Edit only `CandidateProof.lean`. Run exactly
`lean CandidateProof.lean` after each repair and use its actual diagnostics until it exits zero.
Finish only after inspecting the candidate and confirming that its theorem statement is unchanged
and it contains no `sorry`, `admit`, `axiom`, or `unsafe`.

This disposable fixture contains no KLS theorem and its success changes no mathematical status.

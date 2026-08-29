# Disposable proof-repair actor contract

This workspace contains a synthetic Lean calibration task. It contains no KLS theorem, proof,
ledger, manuscript, semantic review, or solution certificate.

Work directly in this session. Do not spawn a subagent, delegate work, invoke collaboration, act
as a reviewer, use web search, or access files outside this workspace.

Only `CandidateProof.lean` may change. Run `lean CandidateProof.lean` after every attempted repair
and continue from the real compiler diagnostic until it exits successfully. Do not use `sorry`,
`admit`, `axiom`, or `unsafe`.

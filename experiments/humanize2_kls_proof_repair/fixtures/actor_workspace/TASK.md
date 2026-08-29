# Disposable Lean proof-generation and repair task

Repair the proof in `CandidateProof.lean` without changing the theorem name, binders, or
conclusion. The initial proof is deliberately ill-typed so that the run must use real Lean compiler
feedback. Edit only the proof body, run `lean CandidateProof.lean`, and finish only after Lean exits
zero and the forbidden placeholder scan is clean.

This theorem is a synthetic harness fixture. It is not a KLS claim and has no mathematical status
in the repository.

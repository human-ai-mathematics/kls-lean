# Harden only the five Stage 1B Run 2 theorem signatures

- **Date:** 2026-08-30
- **Type:** authorized experimental retry boundary
- **Scope:** Issue 2 Stage 1B actor specification and prompt
- **Mathematical effect:** none

## Authorization

After Stage 1B Run 1 compiled locally but failed the precommitted exact-surface verifier, the user
explicitly authorized: “Stage 1B Run 2, harden only the five exact Lean signatures, and use a fresh
isolated session.” This authorization remains inside the existing Issue 2 experiment. It does not
authorize Stage 2A, another KLS target, a model reviewer, production promotion, or exposure of the
existing proof.

## Decision

Add the exact theorem headers for these five declarations to the actor-facing `TASK.md` source:

- `optimalPoincareConstant_le`;
- `le_optimalPoincareConstant`;
- `optimalPoincareConstant_eq_top_of_no_finite`;
- `optimalPoincareConstant_ne_top_of_hasPoincare`; and
- `optimalPoincareConstant_eq_top_iff`.

The headers expose only the already frozen public API: implicit `μ`, `C`, and `L` binders where
required, plus the exact universal-negation form of the final equivalence. They contain no proof
term, proof strategy, Run 1 candidate text, verifier diagnostic, hidden oracle, review finding,
solution certificate, ledger answer, or production implementation.

Keep the other eight Stage 1B declarations, accepted Stage 1A dependency, exact-surface verifier,
human checklist, oracle surface, compiler loop, Seatbelt policy, trace policy, and model settings
unchanged. Repin the modified specification and actor prompt rather than weakening the verifier.

Run 2 must use the new external state root
`/private/tmp/humanize2-kls-issue2-stage1b-run2`, a new dedicated subscription-authenticated
`CODEX_HOME`, and exactly one fresh actor session. Do not reset or reuse the stopped Run 1 state at
`/private/tmp/humanize2-kls-issue2-stage1b`.

Human review remains the only acceptance gate. Preparing or running this retry does not itself
create a proof dossier, certification, ledger/manuscript update, or mathematical status change.

## Model-free validation

Before the preparation commit:

- the updated Stage 1B pinset passed;
- the complete model-free suite passed twice through seven trace-auditor tests, including
  deterministic reset, verifier success/failure paths, physical isolation, and trace policy;
- `lake build` completed 2,946 jobs;
- the ledger checker reported 195 nodes and zero errors;
- `git diff --check` passed; and
- the stopped Run 1 candidate retained SHA-256
  `cfde84ba4de0fe4230331979b586fee5da43b4f20aae2bc27dbfdfd5ac9e2df9`.

No Run 2 state root, login, model session, candidate, or proof attempt existed during these checks.

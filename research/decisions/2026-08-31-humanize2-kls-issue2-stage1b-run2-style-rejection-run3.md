# Reject Stage 1B Run 2 on style and authorize zero-warning Run 3

Date: 2026-08-31

## Human decision

The user explicitly required that an accepted Lean layer contain no style diagnostic and then
confirmed a fresh Stage 1B Run 3. Run 2 remains a valid historical mechanical pass under its
original gates, but it is human-rejected as the Stage 2A dependency because the exact command
emits an `unnecessarySimpa` linter suggestion at the final proof of
`optimalPoincareConstant_ne_top_of_hasPoincare`.

The stopped Run 2 candidate and SHA-256
`3778490dcbd79f4632795f9b541a281b9032596c4cfe415e81b627a4c48e6c4e` remain unchanged. Do not
edit it in place, change its pin, describe it as accepted, or reset its historical external root.

## Run 3 authorization and boundary

Authorize one fresh subscription-authenticated Stage 1B actor run with the same thirteen
declarations, theorem types, mathematical specification, accepted Stage 1A dependency, model,
effort, isolation policy, compiler-feedback loop, hidden surface checker, and human review gate.
The only new actor-facing requirement is that the exact command
`lean CandidateStage1B.lean` must exit zero with empty standard output and standard error.

A warning or linter suggestion is a failed attempt even when Lean exits zero. The actor must fix
the underlying term. It may not suppress diagnostics with `set_option`, `attribute`, a
linter-disable directive, or another configuration escape. The actor receives no Run 2 candidate,
warning location, replacement proof, production implementation, hidden oracle, or reviewer
reasoning.

Run 3 must use the fresh external root
`/private/tmp/humanize2-kls-issue2-stage1b-run3` and a newly authenticated dedicated `CODEX_HOME`.
The runner rejects the historical Stage 1A, Run 1, and Run 2 roots and requires acknowledgement
`H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-run3-zero-warning-human-review`.

## Verifier change

The independent verifier captures both compiler streams for the candidate and exact-surface
checker. Any nonempty output fails closed. The static gate also rejects `set_option`; the existing
attribute and escape-hatch prohibitions remain. Model-free tests must demonstrate:

- the warning-free known-good fixture passes;
- the byte-identical Run 2 candidate fails on its linter diagnostic;
- an adversarial extra axiom still fails; and
- the new acknowledgement and fresh-login gates fail closed.

The migrated `kls-lean` experiment branch does not contain four full-KLS files that the original
isolation smoke test used only as denied-read probes. Replace those nonexistent probe targets with
checked-in `kls-lean` design, review, knowledge, and handoff files. This is a portability repair to
the test, not a relaxation: the same seatbelt must still deny every selected repository file, the
hidden oracle and checklist, the main checkout, and the actor client state. Validate all targets
exist before the sandbox test and retain the exact five-entry visible actor workspace.

This authorization covers only Stage 1B Run 3. It does not authorize Stage 2A, a model reviewer,
production promotion, another KLS target, or a mathematical-status change.

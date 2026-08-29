# Humanize2 staged Issue 2 autoformalization

## Status

The staged plan, Stage 1A specification, actor prompt, and human-review checklist are frozen.
No Stage 1A actor workspace has been built and no authenticated model run has started.

This experiment reconstructs the already certified Issue 2 linear-test development through a
blind Humanize2/Codex actor. The existing Lean implementation, natural-language solution,
certificates, reviews, ledger, and statement-fidelity oracle are hidden references for the human
reviewer. They are not actor inputs.

## Layered scope

Issue 2 is split into small acceptance units. A layer may become an input to the next layer only
after a human accepts its statement, assumptions, namespace, and compiled Lean output.

1. **Stage 1A — foundational definitions**
   `IsAdmissible`, `dirichletEnergy`, and `HasPoincare` only.
2. **Stage 1B — foundational lemmas and optimal constant**
   Nonnegativity, derivative/gradient compatibility, monotonicity, the extended optimal constant,
   and the finite-versus-`⊤` boundary.
3. **Stage 2A — linear-test geometry**
   The linear test, its evaluation rule, gradient, and elementary Hilbert-space identities.
4. **Stage 2B — linear-test analysis**
   Energy, admissibility from a second moment, and the fixed-constant variance bound.
5. **Stage 3 — extended Rayleigh layer**
   The Poincaré Rayleigh quotient, positive- and zero-energy cases, and comparison with the optimal
   Poincaré constant.
6. **Stage 4 — covariance and spectral layer**
   The centered covariance operator, positivity and variance identities, maximal Rayleigh value,
   and the finite-dimensional eigenvalue bridge.
7. **Stage 5 — Issue 2 assembly**
   The abstract lower bound, the Euclidean specialization, and the thin node certificate.

This decomposition is an experimental schedule, not a new mathematical statement. It does not
change the already certified Issue 2 result.

## Per-stage protocol

Each stage follows the same stop-and-review boundary:

```text
freeze specification and pins
→ reset an external oracle-free actor workspace
→ run one subscription-authenticated actor session
→ use actual Lean compiler feedback
→ verify candidate and audit the complete actor trace
→ stop
→ human semantic and proof review
→ explicitly accept, reject, or request a new isolated run
```

The actor may see only:

- the current stage's `AGENTS.md`, `TASK.md`, and candidate file;
- compiled upstream Mathlib dependencies and the pinned Lean toolchain; and
- source or compiled artifacts from earlier stages that a human has explicitly accepted.

It must not see the repository worktree, existing `FunctionalInequalities` sources, Issue 2 proof
or certificate, `solutions/`, `research/reviews/`, either ledger, the statement-fidelity oracle,
or artifacts from later stages. No model reviewer is used. The human reviewer may inspect the full
repository after the actor has stopped.

## Frozen next step

The next prompt is `prompts/issue2_stage_1a_actor.md`, grounded only in
`inputs/issue2_stage_1a_basic_vocabulary.md`. Stage 1A outputs an isolated
`CandidateStage1A.lean`; it must not edit production Lean files.
`pins/stage_1a.sha256` freezes that specification, prompt, and human checklist together.

Before running it, the harness must add a Stage 1A-specific external workspace, deterministic
reset, Mathlib-only import path, deny-default Seatbelt profile, candidate verifier, and trace
auditor. A dedicated actor `CODEX_HOME` should sign in with the user's ChatGPT subscription.
Building and validating that run harness is the next repository task; this prompt freeze alone
does not authorize bypassing the isolation gate.

## Acceptance and mathematical status

Lean exit zero is necessary but insufficient. The human checklist in
`review/issue2_stage_1a_human_checklist.md` is the only semantic acceptance gate. An accepted
experimental candidate is still not a production proof or ledger event. Promotion into
`formalization/`, creation of a solution dossier, review certification, and ledger/manuscript
updates require their normal repository workflows and separate explicit decisions.

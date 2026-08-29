# Stage Issue 2 autoformalization behind human review gates

- **Date:** 2026-08-29
- **Type:** experiment scope and review protocol
- **Scope:** `experiments/humanize2_kls_issue2_staged/`
- **Mathematical effect:** none

## Authorization and objective

The user explicitly authorized a real-model KLS autoformalization experiment scoped first to the
existing Issue 2 linear-test development, using ChatGPT subscription authentication. The user also
chose staged, layered execution with human review rather than a model reviewer.

Issue 2 already has a compiled and reviewed Lean implementation. This experiment therefore treats
it as a blind reconstruction benchmark: the existing implementation and proof artifacts are a
hidden human oracle, not evidence that a generated candidate is independently correct.

The authorization covers sending the frozen Issue 2 stage specification, actor candidate,
Mathlib/Lean diagnostics, and bounded repair prompts to the subscription-authenticated Codex actor.
It does not cover any KLS target outside Issue 2, access to existing proof/review/ledger material,
automatic promotion into production files, or model-based certification.

## Layering decision

Split the development at semantic dependency boundaries:

1. Stage 1A: `IsAdmissible`, `dirichletEnergy`, and `HasPoincare` definitions only.
2. Stage 1B: foundational lemmas and the extended optimal Poincaré constant.
3. Stage 2A: linear-test geometry.
4. Stage 2B: linear-test energy, admissibility, and fixed-constant bound.
5. Stage 3: extended Rayleigh quotient and optimal-constant comparison.
6. Stage 4: covariance operator, Rayleigh maximum, and finite-dimensional spectral bridge.
7. Stage 5: the abstract and Euclidean Issue 2 certificates.

No stage may consume its predecessor until a human has accepted that predecessor. Rejection ends
the run; any repair begins in a fresh isolated actor session with an explicitly bounded human
request. Reviewer reasoning or the hidden reference is never fed back to the actor.

## Actor and reviewer boundary

Use one model actor and no model reviewer. The actor receives only the current three-file fixture,
compiled upstream Mathlib artifacts, the Lean toolchain, and any earlier stage explicitly accepted
by a human. A deny-default external Seatbelt profile must exclude the repository, current and later
Issue 2 sources, `solutions/`, reviews, ledgers, statement-fidelity oracle, certificates, and human
checklists.

After the actor stops, deterministic verification and the complete trace audit run before a human
may inspect the candidate against the repository's hidden reference. Human acceptance is a stage
transition only. It is not proof certification, dossier review, ledger promotion, or a manuscript
change.

## Current deliverable and next gate

This decision freezes the hierarchy, Stage 1A natural-language specification, actor prompt, and
human checklist. It does not build the Stage 1A runtime fixture or perform a model call.

Before the first authenticated run, add and validate a Stage 1A-specific deterministic reset,
Mathlib-only import environment, external Seatbelt allowlist, candidate verifier, and trace audit.
The actor lane must use a dedicated `CODEX_HOME` signed in through the user's ChatGPT subscription.
Only after those checks pass may the frozen Stage 1A prompt be sent.

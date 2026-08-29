# Start a KLS-facing statement-fidelity calibration

- **Date:** 2026-08-29
- **Type:** agent harness and validation design
- **Scope:** `experiments/humanize2_kls_statement_fidelity/`, KLS experiment handoff
- **Mathematical effect:** none

## Problem

The Humanize2 baseline proves that Codex can edit files, react to Lean diagnostics, repair trivial
proofs, and pass an actor-reviewer gate. It does not test the most dangerous autoformalization
boundary: whether a generated Lean proposition faithfully represents its informal mathematical
source. A compiler accepts weakened or mis-scoped propositions just as readily as faithful ones.

## Decision

Begin with a statement-only calibration against `lem:linear-test-lower`, the repository's sole
complete Lean certificate with a persisted independent semantic audit. Although the node lives in
the A-series ledger, the linear-test covariance lower bound is a shared functional-inequality tool
used throughout KLS. Treat it only as a KLS pipeline calibration; create no new claim, proof,
ledger edge, or status change.

Freeze an informal input that includes probability normalization, finite second moment, all
admissible tests, the extended quotient, centered covariance, and dimension zero. The actor writes
only a Lean `Prop` definition and is instructed not to read the oracle sources. A fresh read-only
RLAR reviewer compares every binder and conjunct against pinned reference files and a ten-item
semantic rubric. Reviewer `done: false` notes return to the actor verbatim; `done: true` requires
semantic, compiler, and Git-scope checks.

Pin the oracle sources by SHA-256 so a later repository change cannot silently alter the benchmark.
Reuse the baseline's pinned Humanize2/flowverse setup and a separate external Humanize state home.
Keep the initial candidate as an explicit compiling `True` sentinel; it is not evidence and the
candidate verifier refuses it.

## Trust boundary

The first calibration is prompt-blind, not cryptographically blind. Actor and reviewer share a
repository, and the actor's read sandbox can technically reach forbidden oracle paths. Audit the
live tool trace for violations and record any as a failed run. A hardened successor should execute
the actor in an oracle-free snapshot and expose the oracle only to the reviewer.

Do not run the authenticated experiment until transfer of the frozen KLS-facing input, allowed API
files, candidate diff, and compiler/reviewer output to OpenAI is explicitly authorized. Do not
commit raw sessions, credentials, or Humanize state.

## Validation boundary

The scaffold is complete when the initial candidate matches its reset fixture, the sentinel file
type-checks with the repository's pinned Lean toolchain, oracle hashes pass, scripts parse, the
repository-wide Lake build remains green, and Git changes stay within the experiment, this decision,
and its handoff. A live result is deliberately not claimed by this decision.

No ledger, manuscript statement, proof dossier, review, numerical artifact, mathematical status,
or KLS source is modified.

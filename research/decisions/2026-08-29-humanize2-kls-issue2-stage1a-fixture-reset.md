# Restore the Stage 1A actor fixture before runtime isolation

- **Date:** 2026-08-29
- **Type:** experiment harness implementation
- **Scope:** `experiments/humanize2_kls_issue2_staged/`
- **Mathematical effect:** none

## Problem

The first staged-plan commit froze `TASK.md` content and an actor prompt but did not commit or
materialize the three-file actor fixture. A preflight correctly reported that `TASK.md` and
`CandidateStage1A.lean` were absent, so neither implementation nor compilation could start.

## Decision

Commit the source fixture under `fixtures/actor_workspace/` and provide a deterministic reset into
a dedicated external `/private/tmp` state root. The reset creates exactly:

```text
AGENTS.md
CandidateStage1A.lean
TASK.md
```

The committed `TASK.md` must remain byte-identical to the frozen Stage 1A input. The initial Lean
file fixes the three permitted upstream Mathlib imports, ambient namespace and typeclass context,
and a named compiler-failing sentinel. The sentinel prevents an untouched scaffold from being
mistaken for a successful definition-generation run.

Add fail-closed verifiers for the exact file set, symlink absence, immutable actor instructions,
pins, sentinel diagnostic, allowed imports, namespace, requested declaration names, structure
field names, escape hatches, and Lean compilation.

Derive the candidate's `LEAN_PATH` from the pinned Lake environment, remove the repository's
`formalization/.lake/build/lib/lean`, reject every other repository-local component, and omit stale
nonexistent dependency entries. This lets the fixture compile against upstream Mathlib artifacts
without exposing existing compiled `FunctionalInequalities` declarations.

## Validation and remaining gate

The deterministic reset restored all three files. The initial sentinel produced the expected
nonzero Lean diagnostic. A host-supplied model-free candidate with the frozen three definitions
passed the surface verifier and compiled with the sanitized upstream Mathlib-only import path; the
workspace was then reset to the sentinel.

This change repairs fixture availability only. It does not start Humanize2 or Codex, perform an
autoformalization attempt, or generate a mathematical result. The prompt remains blocked until a
Stage 1A-specific deny-default Seatbelt profile, subscription-authenticated actor home, adversarial
forbidden-read probes, and complete-session trace audit are implemented and pass.

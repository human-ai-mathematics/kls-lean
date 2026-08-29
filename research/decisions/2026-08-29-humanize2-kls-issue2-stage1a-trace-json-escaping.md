# Normalize JSON-escaped paths in the Stage 1A trace auditor

- **Date:** 2026-08-29
- **Type:** experiment harness repair
- **Scope:** `experiments/humanize2_kls_issue2_staged/scripts/audit_actor_trace.py`
- **Mathematical effect:** none

## Observed failure

The first authenticated Issue 2 Stage 1A actor completed and its candidate passed the independent
surface and Lean verifier. The post-run trace auditor nevertheless returned nonzero. Its compact
summary showed one actor-root session, one turn, zero descendants, six local `exec` calls, and no
forbidden tool, but reported six paths ending in a literal backslash, for example:

```text
/private/tmp/humanize2-kls-issue2-stage1a/actor-workspace\
```

The corresponding trace inputs were JSON strings nested inside JSONL records. The auditor first
serialized the input to scan it, then let its path regular expression consume the backslash that
escaped the closing quote or newline. `realpath` correctly treated that extra character as part of
a different path, so the fail-closed check classified the otherwise legal actor root as external.
This was an auditor parser defect, not evidence of actor access outside the workspace.

## Decision

Exclude backslash from the path token character class. A JSON escape now terminates the path token,
leaving the canonical actor root or candidate path for the existing containment check. Add a unit
test whose tool input is itself JSON-encoded and contains both `cwd` and patch paths. Keep every
other trace condition unchanged.

Do not rerun the model. Re-audit the same immutable actor session tree with the repaired auditor,
and retain both the initial fail-closed result and the reason for reclassification in the attempt
record. The actor-facing prompt, fixture, candidate, Seatbelt profile, compiler environment, and
session trace are not changed by this repair.

## Validation

Five auditor unit tests passed. Re-auditing the original Stage 1A session returned:

- `ok: true` and no errors;
- exactly one session, one turn, and zero descendants;
- six local `exec` calls;
- referenced absolute paths limited to the actor root and `CandidateStage1A.lean`; and
- the unchanged Seatbelt profile SHA-256
  `5993194cb9cc64f4c3c11868b16cbda996577acdbf9e966decf75c0620bcd233`.

The candidate and hidden-oracle pin verifiers also remained green. This repair changes only process
audit classification; it makes no semantic acceptance decision and changes no mathematical state.

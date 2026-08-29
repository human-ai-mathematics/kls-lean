# Exclude the Lean subtype delimiter from Stage 1B trace paths

- **Date:** 2026-08-29
- **Type:** experiment trace-auditor repair
- **Scope:** `experiments/humanize2_kls_issue2_staged/scripts/stage_1b_audit_actor_trace.py`
- **Mathematical effect:** none

## Observed failure

The first authenticated Stage 1B actor session stopped after producing a locally compiling
candidate. The exact-surface verifier separately rejected that candidate, and the runner therefore
stopped before its final trace command. A manual invocation of the frozen trace auditor reported
one error:

```text
actor tool input named a path outside its workspace: //
```

The same compact summary already showed one root session, one turn, zero descendants, four local
`exec` calls, immutable accepted-artifact hashes, and candidate-only mutation. Inspection of only
the recorded tool inputs located `//` in the legal Lean subtype expression
`{C : NNReal // HasPoincare μ (C : ℝ)}` inside the candidate patch. It was not a filesystem path,
URL, network command, or traversal.

## Decision

Change the absolute-path token from `/(?![-*])...` to `/(?![-*/])...`. A doubled slash can no
longer begin an absolute-path match, while normal absolute paths such as
`/private/tmp/.../CandidateStage1B.lean` remain subject to canonical containment checks.

Add a regression test whose otherwise valid patch contains the Lean subtype delimiter. Keep every
other tool, path, mutation, Seatbelt, client-state, network, and forbidden-output rule unchanged.
Do not rerun the model; re-audit the same captured session.

## Validation

Seven trace-auditor unit tests passed. The repaired auditor returned `ok: true` on the original
session with:

- exactly one root session, one turn, and zero descendants;
- exactly four local `exec` calls;
- actor-visible files equal to the frozen five-entry fixture;
- workspace mutations equal to `CandidateStage1B.lean` only;
- unchanged accepted source and `.olean` hashes; and
- referenced absolute paths limited to the actor root and candidate.

The trace-input SHA-256 remained
`b2bbc0a040fffd10bdf007de756082ae5c6669fd80b334e939841002fbbb5bfc`; the Seatbelt profile
SHA-256 remained `4144594cc0e4eb2a4e95cf058dc88851734b111c27d54c960820ce1a7a32ebf2`.
This repair changes only path classification and does not alter the rejected candidate or its
exact-surface result.

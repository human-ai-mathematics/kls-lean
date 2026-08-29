# Build the Issue 2 Stage 1B five-entry isolated harness

- **Date:** 2026-08-29
- **Type:** experiment harness and authorization gate
- **Scope:** `experiments/humanize2_kls_issue2_staged/`
- **Mathematical effect:** none

## Decision

Build Stage 1B as a new external Humanize2/Codex/Lean lane rather than extending or resetting the
stopped Stage 1A lane. The new lane uses only the human-accepted Stage 1A source and a deterministic
compiled form of that exact source. It exposes no existing Issue 2 implementation or proof and has
no model reviewer.

The external workspace contains exactly:

```text
AGENTS.md
TASK.md
AcceptedStage1A.lean
AcceptedStage1A.olean
CandidateStage1B.lean
```

The accepted source retains its intentional explicit function binder in `HasPoincare`. Its pinned
SHA-256 is `9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6`.
Every reset recompiles `AcceptedStage1A.olean` outside the actor workspace with pinned Lean 4.33.0
and an upstream-Mathlib-only `LEAN_PATH`; repeated compilations produce SHA-256
`212cd1f5a0c20d2f3974c5948ea4c26550409a5b3b7b47a4b65e1e9cdf65a3a0`.

## Isolation and mutation design

The Stage 1B state-root variable, actor home, runtime directory, Humanize home, audit outputs,
compiled-dependency build directory, fixture paths, flow, configs, scripts, and live-run
acknowledgement are distinct from Stage 1A. State-root validation rejects the historical Stage 1A
root and requires a dedicated real path below `/private/tmp` outside the repository.

The reset makes the actor directory mode `0555`; `AGENTS.md`, `TASK.md`, and both accepted artifacts
are mode `0444`; only the existing candidate is mode `0644`. The deny-default Seatbelt independently
allows file writes only to the literal candidate path. Outbound network access is guarded by the
Codex executable's `process-path`, so descendant shell and Lean processes cannot connect. Thus
actor tools cannot create, rename, or delete files or replace either accepted artifact. A baseline
JSON outside the actor lane records
all five hashes, sizes, and modes. Candidate verification and complete trace audit both recheck the
immutable hashes after a run, and the auditor requires the observed mutation set to be exactly
`CandidateStage1B.lean`.

The Seatbelt read allowlist contains the actor root, macOS/Codex runtime, pinned Lean toolchain, and
upstream Mathlib build roots. It excludes the repository-local compiled KLS root even when Lake
resolves it through another checkout. Direct probes deny the existing `Basic.lean` source and
`.olean`, later `Poincare.lean`, the node certificate, natural-language solution, semantic review,
ledger, manuscript, human checklist, oracle pin, and actor client state. Codex client state remains
available only under a `process-path` filter for the Codex executable; descendant shell and Lean
processes cannot read or mutate it.

## Compiler and verifier design

The reset candidate imports only `AcceptedStage1A` and fails compilation on the named
`stage1BImplementationRequired` sentinel. The candidate verifier requires:

- the sole exact import `AcceptedStage1A`;
- namespace `Issue2Autoformalization.Stage1A` and only the requested nested `HasPoincare` namespace;
- exactly the thirteen requested declaration names, order, and theorem/definition kinds;
- no extra public, private, syntax, notation, macro, instance, axiom, opaque, unsafe, external,
  `sorry`, or `admit` escape surface;
- byte-identical accepted artifacts with their read-only modes; and
- compilation against only a disposable copy of the accepted dependency plus upstream Mathlib.

After compiling the candidate into the disposable verifier directory, the verifier imports a
separate fixed surface file. Its examples instantiate every requested theorem with exactly the
frozen hypotheses, ensure the derivative/gradient theorem works without `MeasurableSpace E`, and
require the optimal constant's infimum formula by definitional equality. This mechanical surface
gate does not replace human proof/semantic review.

The known-good candidate used to test this success path is stored only as hidden test material. It
is pinned with the harness and physically denied to the actor. It is not an accepted Stage 1B
candidate or a proof attempt.

## Oracle and human boundary

The Stage 1B hidden oracle is independent of the accepted dependency. Its custom verifier extracts
and hashes only the thirteen relevant declaration blocks from the existing `Basic.lean`, producing
digest `c929454a4ee73ddf152c4c739c6fc5eb3be76cd133746c600856b110bb835e0e`. The attached
`omit [MeasurableSpace E] in` modifier is part of that pin. Unrelated portions of
`Basic.lean` are outside this oracle pin. The thirteen-item human-only checklist covers trace and
mutation isolation, exact APIs, energy and derivative reasoning, fixed-constant monotonicity, the
extended infimum and empty-index boundary, absence of stronger hypotheses/escape hatches, and the
experimental-only classification.

The actor flow creates one actor session at the external root and supplies no reviewer. The runner
requires both the exact live acknowledgement
`H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-human-review` and a new Stage 1B-specific
`CODEX_HOME` whose status is exactly `Logged in using ChatGPT`. It preserves only that home's
`auth.json` across resets; no credential or global Codex home is copied.

The complete trace auditor scans the whole dedicated actor home. It requires exactly one root
session, one turn, zero descendants, one workspace root, and the externally sandboxed marker. It
allows only local execution/patch calls and rejects collaboration, reviewer, browser, web, MCP,
computer-use, model/client launches, network commands, environment/client-state inspection,
parent traversal, forbidden paths/outputs, sandbox denials, profile drift, explicit `.olean`
inspection, or any mutation beyond the candidate.

## Model-free validation

Observed commands and exit codes before the implementation commit:

```text
experiments/humanize2_kls_issue2_staged/scripts/verify_candidate.sh /private/tmp/humanize2-kls-issue2-stage1a/actor-workspace
  exit 0

experiments/humanize2_kls_issue2_staged/scripts/stage_1b_model_free_tests.sh
  exit 0

cd formalization && lake build
  exit 0; 2,946 jobs

uv run --with pyyaml python research/check_ledger.py
  exit 0; 2 ledgers, 195 nodes, 675 labels, 0 structural errors

experiments/humanize2_kls_issue2_staged/scripts/stage_1b_verify_oracle_pins.sh
  exit 0

shasum -a 256 -c experiments/humanize2_kls_issue2_staged/pins/stage_1b.sha256
  exit 0

git diff --check
  exit 0
```

The Stage 1B model-free suite covers deterministic reset and rerun, exact visible entries and file
modes, byte-identical source, reproducible compiled dependency, source/compiled write denial,
extra-file and delete denial, candidate write permission, hidden repository/oracle/review/ledger/
manuscript/client-state read denial, failing sentinel and its exact diagnostic, known-good
candidate and exact-surface success, adversarial extra-axiom rejection, upstream-only sandboxed Lean
success, Codex app-server initialization, and accepting/adversarial complete-trace cases.

The unacknowledged runner exited `2` before state-root or model activity. With the acknowledgement
set but a fresh unauthenticated Stage 1B home, it reset only that disposable Stage 1B probe and
exited `2` before isolation preparation or model activity, requesting a dedicated ChatGPT login.

No Stage 1B model was called, no Stage 1B proof attempt occurred, and no exploration was created.
No production KLS Lean, solution, review, ledger, manuscript, proof certification, or mathematical
status changed. Raw transcripts, credentials, tokens, Codex/Humanize state, generated `.olean`
files, and machine-private configuration remain outside Git.

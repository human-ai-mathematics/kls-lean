# Run Issue 2 Stage 1A in a dedicated oracle-free Codex workspace

- **Date:** 2026-08-29
- **Type:** experiment harness implementation
- **Scope:** `experiments/humanize2_kls_issue2_staged/`
- **Mathematical effect:** none

## Problem

The committed Stage 1A fixture existed in the external state root, but attempts to execute the
actor prompt inside an existing Codex desktop task reported that `TASK.md` and
`CandidateStage1A.lean` were absent from its workspace roots. Copying those files into the main KLS
workspace would make the prompt runnable but would destroy the blind-filesystem claim: that task
already has access to the repository, existing Issue 2 implementation, reviews, solutions, and
ledgers.

The correct unit of execution is therefore a new Codex app-server session rooted in the external
three-file fixture, not an existing desktop task whose roots were chosen earlier.

## Decision

Add a Humanize2 actor-only flow that calls `agents.actor.new(cwd=actor_root)` exactly once. The live
runner also changes the Humanize process current directory to the same external actor root before
invoking the flow. No model reviewer, repair relay, collaboration tool, or second actor round is
present. A human reviews only after the actor session and mechanical audits have stopped.

Keep these exact actor-workspace files:

```text
AGENTS.md
CandidateStage1A.lean
TASK.md
```

Render a deny-default macOS Seatbelt profile that allowlists file data only for those files' root,
the installed Codex app, macOS runtime, pinned Lean toolchain, and compiled upstream Mathlib
package roots. Repository roots, baseline KLS source and compiled KLS output, solutions, reviews,
ledgers, statement-fidelity oracle, and the hidden Stage 1A reference remain outside the file-data
allowlist.

Guard the separate actor `CODEX_HOME` and runtime directory with a Seatbelt `process-path` filter
for the installed Codex executable. This allows the app-server to authenticate and persist its
session while denying the same paths to descendant shell and Lean processes. The actor must sign
in directly to this home through the user's ChatGPT subscription; copying a global credential file
or client state is forbidden.

Pin Humanize2 at `e8bcede84d4b3365378e04f9c80d0fd397903c30` and apply the frozen adapter patch that wraps only
the workspace-write app-server in the external Seatbelt profile. Codex's internal sandbox marker is
`danger-full-access` because Seatbelt cannot nest; the trace auditor treats that marker as valid
only when the pinned outer profile is present and hashed.

## Determinism, compiler feedback, and auditing

`reset_run_state.sh` deletes only named paths below a validated dedicated `/private/tmp` state root,
preserves at most its own `auth.json`, clears sessions and audit output, reconstructs the exact
fixture, and rerenders configuration. The initial candidate intentionally fails on the named
sentinel. The live actor must repeatedly run `lean CandidateStage1A.lean`; the post-run verifier
requires the sentinel to be replaced, the exact imports/namespace/declarations/fields to remain,
escape hatches to be absent, and Lean to exit zero with only upstream Mathlib on `LEAN_PATH`.

The trace auditor reads every JSONL file in the dedicated actor home and requires exactly one
session, no descendants, one turn rooted at the external fixture, and exactly that one workspace
root. It rejects delegation/collaboration, MCP/browser/web/computer tools, client or environment
inspection, model/client launches, shell networking, path traversal, forbidden input/output paths,
sandbox denials, and a missing or broadened outer profile. Only a compact summary and hashes are
retained outside Git; raw sessions remain external.

`oracle/stage_1a_reference.sha256` pins the existing `Basic.lean` human reference. The Stage 1A
pinset separately freezes the eleven-item human semantic checklist, Lean toolchain, Lake manifest,
Lake configuration, fixture, prompt, flow, isolation profile, Humanize2 patch, scripts, and audit
tests. The human may inspect the hidden reference only after the stopped trace passes. Reviewer
reasoning is never returned to that actor session.

## Canonical-path correction

Model-free validation initially exposed a real isolation defect: this checkout's
`formalization/.lake/build/lib/lean` resolves to the baseline checkout. The earlier filter compared
the real path of each `LEAN_PATH` component with an unresolved checkout path, so the baseline KLS
build root could enter the allowlist. The final filter canonicalizes both sides, drops that root,
and refuses any remaining import root containing
`FunctionalInequalities/Basic.olean`. The isolation battery directly verifies that both the
baseline `Basic.lean` and compiled `Basic.olean` are unreadable.

## Validation and current state

Model-free checks passed for fixture and pin reset, expected sentinel compilation failure, a
transient known-definition verifier success followed by reset, canonical Mathlib-only import
selection, forbidden reads across all three KLS checkouts and all oracle categories, client-state
read/write denial from descendant tools, actor-local writes, disposable upstream Lean compilation,
Codex app-server initialization inside Seatbelt, the pinned Humanize2 patch, and four trace-auditor
unit tests.

The live runner refuses without the explicit Issue 2 acknowledgement and then refuses without a
subscription-authenticated dedicated actor home; both gates exited `2` as designed. No authenticated
model call, mathematical attempt, candidate result, theorem, proof, dossier, certification,
ledger/manuscript edit, or mathematical status change occurred.

# Build an oracle-free proof-repair actor with an external Seatbelt boundary

- **Date:** 2026-08-29
- **Type:** agent-harness architecture and local validation
- **Scope:** `experiments/humanize2_kls_proof_repair/`
- **Mathematical effect:** none

## Objective and authorization boundary

The next calibration is proof generation plus compiler-feedback repair, but no new KLS-facing
content is authorized for external transfer. The implemented target is therefore the disposable
Lean theorem `humanize2_isolated_add_zero`; it is not a repository claim and has no ledger,
manuscript, dossier, or certification role. The accepted statement-fidelity candidate remains
unchanged.

No authenticated actor/reviewer run was made while building this scaffold. Only model-free local
tests, fixed upstream source retrieval, tool installation in an external temporary directory, and
Codex app-server initialization were performed. A future KLS target still requires explicit user
authorization before its statement, context, compiler output, diff, or review leaves the machine.

## Rejected boundary

An initial implementation used a Codex named permission profile with `:root = "deny"` and an
actor-workspace carve-out. The current `codex-cli 0.150.0-alpha.8` recognized that profile, but a
direct adversarial probe could still read the experiment oracle. The test correctly failed with
exit 41. Prompt restrictions and trace review cannot repair a failed physical boundary, so that
design was removed before acceptance.

## Decision

Run the actor Codex app-server itself under a rendered macOS Seatbelt profile with `deny default`.
Allow file data only for the operating-system runtime, installed Codex app, three-file disposable
actor workspace, Lean 4.33.0 toolchain, actor-only Codex home, and actor-only temporary directory.
Give path ancestors metadata-only access. The full repository, reviewer Codex home, oracle, KLS
ledgers, existing proofs, reviews, certificates, manuscript, and accepted statement candidate are
outside the allowlist.

Use separate Codex app-server processes and separate `CODEX_HOME` directories for actor and
reviewer. The reviewer remains read-only in the repository. This prevents its oracle-bearing
transcript from appearing in actor-visible state. Because macOS Seatbelt cannot be nested, a small
pinned patch to Humanize2 commit `e8bcede84d4b3365378e04f9c80d0fd397903c30` marks only the
already externally sandboxed actor turn as `danger-full-access`; all actor commands still inherit
the outer kernel boundary. Reviewer turns retain the upstream read-only setting.

The actor workspace is reconstructed deterministically with exactly:

```text
AGENTS.md
CandidateProof.lean
TASK.md
```

It contains no symlink. The starting proof is intentionally ill-typed, forcing a real Lean
diagnostic. The independent reviewer reads a pinned ten-item rubric and reference, but its prose is
never passed to the actor. Only closed finding codes cross the lane boundary through deterministic
messages.

## Trace and acceptance boundary

The actor-specific Codex home begins with no session records. The post-run auditor reads every JSONL
session there and requires exactly one actor-root session, rejecting any other session, descendant,
collaboration/subagent/MCP/browser or web tools, extra workspace roots, missing external-sandbox
turn markers, shell network commands,
client-state access, forbidden path references, sandbox denials, or drift in the rendered
deny-default Seatbelt profile. It emits only a compact summary; raw transcripts and state remain
external.

Lean exit zero is necessary but insufficient. The reviewer and independent verifier also enforce
the exact theorem declaration, single-theorem scope, placeholder/escape-hatch absence, exact actor
file set, oracle and verifier-integrity pins, session lineage, access boundary, and
no-mathematical-effect classification.

## Model-free validation

The following completed successfully on macOS 26.6.2:

- deterministic reset and scaffold verifier, including the expected nonzero Lean diagnostic;
- four trace-auditor unit tests (pass, collaboration rejection, unrelated-session rejection, and
  forbidden-path/descendant rejection);
- adversarial Seatbelt reads of the oracle, `research/kls/ledger.yaml`, and reviewer-only state,
  all denied;
- actor-local read/write operations under Seatbelt;
- the broken candidate's nonzero Lean path and a disposable repaired candidate's exit-zero path;
- Seatbelt-wrapped Codex app-server initialization;
- clean application of the pinned Humanize2 patch and model-free startup of the patched actor
  app-server; and
- all static oracle SHA-256 pins.

This validates the harness mechanics only. It is not a proof-generation result, a KLS theorem
result, or a certification event.

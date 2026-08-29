# Humanize2 oracle-free proof-generation and compiler-repair experiment

## Status and exact objective

The **local scaffold and isolation self-test are implemented**. No authenticated actor/reviewer run
has been performed in this phase.

The experiment asks one narrow harness question: can a Humanize2-held Codex actor repair a
deliberately ill-typed proof of the disposable theorem
`humanize2_isolated_add_zero`, use real Lean 4.33.0 diagnostics until compilation succeeds, and
then pass an independent oracle-backed reviewer without ever being able to read the oracle or the
KLS repository?

This is not a KLS theorem, a proof of an existing KLS theorem, a new proof dossier, a semantic
certification, or evidence for changing a ledger/manuscript status. It does not reuse the accepted
statement-fidelity candidate and never edits it.

## Physical actor/reviewer isolation

`reset_run_state.sh` constructs a fresh actor workspace under the required external
`H2_PROOF_STATE_ROOT`. The actor and reviewer are separate Codex sessions with separate working
directories:

- actor: `$H2_PROOF_STATE_ROOT/actor-workspace`;
- reviewer: the full repository worktree.

The actor Codex app-server itself is launched under a rendered macOS Seatbelt profile with
`deny default`. That kernel-enforced profile allowlists only the platform runtime, Codex app,
three-file actor workspace, pinned Lean 4.33.0 toolchain, actor-only Codex state, and actor-only
temporary directory. The repository, reviewer state, oracle, and every other user-data path are
unreadable. The reviewer app-server is a separate unwrapped read-only process in the repository.

Seatbelt cannot be nested. The patched Humanize2 adapter therefore marks only the already
Seatbelt-contained actor turns as `danger-full-access`, which prevents Codex from trying to apply a
second Seatbelt profile; this is an external-sandbox marker, not actual host-wide access. The
reviewer stays on the upstream `read-only` rung. Actor and reviewer receive different
`CODEX_HOME` directories, so a reviewer transcript containing oracle material cannot appear in the
actor-visible client state.

Multi-agent, plugin, app, browser, Computer Use, web-search, skill-search, image-generation, hook,
and goal features are disabled in both lane-specific Codex configs. The outer profile must permit
Codex service traffic, but the trace gate rejects actor shell network commands.
`verify_isolation.sh` invokes the rendered Seatbelt profile directly and proves that actor-local
reads/writes, Lean execution, and Codex app-server startup work while reads of both the experiment
oracle, the KLS ledger, and reviewer-only state fail.

Humanize2 commit `e8bcede84d4b3365378e04f9c80d0fd397903c30` does not provide this
per-lane external-sandbox launch. `prepare_humanize2.sh` clones exactly that revision outside the
repository and applies the pinned `patches/humanize2-codex-seatbelt.patch`. A local assertion and
an actual model-free app-server startup validate the adapter patch before a run.

## Actor-visible filesystem

The experiment-owned actor workspace has exactly three files, enforced by
`verify_actor_workspace.sh`:

```text
AGENTS.md
CandidateProof.lean
TASK.md
```

It contains no symlink. The complete additional readable-root classes are:

- macOS system/runtime paths: `/System`, `/usr`, `/bin`, `/sbin`, `/Library`, `/private/etc`, and
  `/dev`;
- the installed Codex app directory;
- the pinned Lean 4.33.0 toolchain;
- `$H2_PROOF_STATE_ROOT/actor-codex-home`; and
- `$H2_PROOF_STATE_ROOT/actor-runtime-tmp`.

Ancestor directories receive metadata-only access needed by realpath. No other file data is
readable. The dynamic actor Codex home contains only actor authentication/config/session state; it
cannot contain reviewer sessions because those use `reviewer-codex-home`. Both state inventories
remain external and are audited, never committed. No repository root, oracle, existing KLS proof,
solution certificate, semantic review, ledger answer, manuscript, or accepted statement-fidelity
candidate is readable.

## Deterministic reset and verification

`reset_run_state.sh` removes only known paths below the dedicated external state root. It recreates
the three-file actor workspace from committed fixtures, clears previous Humanize and both Codex
lane session records, preserves lane-specific authentication files if they exist, renders the
deny-default Seatbelt profile, and creates an external audit directory. For reproducibility this
macOS harness requires the dedicated state root below `/private/tmp`.

`verify_scaffold.sh` checks all oracle pins, the exact visible file set, immutable actor inputs, the
deliberately broken candidate, its expected nonzero Lean diagnostic, and the trace-auditor unit
tests. `verify_candidate.sh` later requires the candidate to differ from the broken fixture,
preserve the exact theorem declaration, contain exactly one theorem and no proof escape hatch, and
compile with the pinned Lean binary.

## Compiler-feedback and review loop

The actor is required to run `lean CandidateProof.lean` after each edit. The starting proof uses
`Nat.zero_add n` for a goal about `n + 0`, so Lean produces a genuine type mismatch. The actor must
repair from the diagnostic and obtain exit zero.

`flows/proof_rlar.py` holds the actor session across at most three rounds but opens a fresh reviewer
session each round. Reviewer prose and oracle details are never copied into the actor prompt.
Instead, the reviewer returns a closed list of finding codes; the flow maps those codes to fixed,
non-oracular repair messages. An inconsistent structured result or failure to converge within the
round bound fails the run.

## Trace audit

Actor and reviewer Codex sessions remain under separate external experiment-specific homes.
`audit_actor_trace.py` reads the complete session tree and fails closed unless the actor Codex home
contains exactly one actor-root session and no other session or descendant, the external-sandbox
turn marker appears on every actor turn, and there is no extra
workspace root, a pinned deny-default Seatbelt profile, at least one auditable tool call, no
collaboration/subagent/MCP/browser/web tool, no shell network or client-state access, no forbidden
repository/oracle/proof/ledger path reference, and no sandbox-denial diagnostic.

The audit emits only a compact JSON summary with counts, tool names, referenced paths, and a hash of
tool inputs. Raw transcripts, prompts, model reasoning, credentials, tokens, Humanize state, Codex
state, and machine-private configuration remain outside Git. OS enforcement makes forbidden reads
impossible; the trace audit separately proves that the actor did not attempt one through its tools.

## Oracle pinning and semantic review

`oracle/reference.sha256` pins the disposable reference proof, ten-item semantic rubric, all three
actor fixtures, actor prompt, isolation and flow configs, custom flow, trace auditor, candidate and
workspace verifiers and their shared path/toolchain helper, and Humanize2 adapter patch. The
reviewer may read this oracle in its
independent read-only lane. The actor cannot. The reference proof is not a required proof term:
any genuine compiling proof that preserves the exact statement and passes the rubric may be
accepted.

Lean compilation is necessary but not sufficient. The reviewer must also check statement
preservation, escape hatches, workspace scope, trace lineage/profile/path rules, oracle pins, and
the explicit no-mathematical-effect boundary.

## Commands

Local, model-free validation:

```bash
export H2_PROOF_STATE_ROOT=/tmp/humanize2-kls-proof-repair
experiments/humanize2_kls_proof_repair/scripts/reset_run_state.sh
experiments/humanize2_kls_proof_repair/scripts/verify_scaffold.sh
experiments/humanize2_kls_proof_repair/scripts/verify_isolation.sh
experiments/humanize2_kls_proof_repair/scripts/prepare_humanize2.sh
```

Before a disposable authenticated run, authenticate both physically separated lane homes:

```bash
CODEX_HOME=/tmp/humanize2-kls-proof-repair/actor-codex-home codex login
CODEX_HOME=/tmp/humanize2-kls-proof-repair/reviewer-codex-home codex login
```

Then acknowledge the external run and execute:

```bash
export H2_PROOF_STATE_ROOT=/tmp/humanize2-kls-proof-repair
export H2_PROOF_LIVE_RUN_ACK=disposable-only
export HUMANIZE_SENTRY=off
experiments/humanize2_kls_proof_repair/scripts/run_proof_rlar.sh
```

The runner always resets session state before a live run. It never sends new KLS-facing content:
the actor and reviewer task is the three-line disposable `Nat` theorem only. A later replacement
with any KLS theorem, statement, proof context, compiler output, or reviewer material requires new
explicit user authorization and a separate fixture/oracle decision.

# Humanize2 staged Issue 2 autoformalization

## Status

The staged plan and complete Stage 1A actor-only runner are implemented. The first
subscription-authenticated actor run produced a compiling candidate and passed the candidate,
oracle-pin, and repaired complete-session trace gates. Human semantic review is pending, so Stage 1A
is not accepted and Stage 1B has not started.

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
`pins/stage_1a.sha256` freezes that specification, prompt, human checklist, three-file fixture,
Lean/Mathlib dependency metadata, isolation configuration, Humanize2 patch, actor-only flow,
reset/verifier/runner scripts, and trace-auditor tests together. The hidden human reference is
separately frozen by `oracle/stage_1a_reference.sha256` and is never mounted in the actor lane.

The committed fixture is under `fixtures/actor_workspace/`. Rebuild and verify it with:

```bash
export H2_ISSUE2_STAGE1A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1a
experiments/humanize2_kls_issue2_staged/scripts/reset_actor_workspace.sh
experiments/humanize2_kls_issue2_staged/scripts/verify_scaffold.sh
```

The reset produces exactly `AGENTS.md`, `TASK.md`, and `CandidateStage1A.lean`. The initial
candidate has the three pinned Mathlib imports and a compiler-failing sentinel. The candidate
verifier rejects an unchanged sentinel, import/namespace/declaration drift, missing structure
fields, escape hatches, extra actor files, and any Lean environment that exposes the repository's
compiled `FunctionalInequalities` library. Its model-free success path has also compiled with the
upstream Mathlib-only `LEAN_PATH`.

The actor session is not this Codex desktop task. Pasting the actor prompt into an existing KLS task
will correctly fail to find the external fixture and would not be blind. `run_stage_1a.sh` starts a
new Humanize2-managed Codex app-server whose process and turn both use the external actor workspace
as the sole current directory and workspace root.

The rendered macOS Seatbelt profile denies file data by default. It permits the actor root, the
pinned Lean toolchain, and only upstream Mathlib package build roots. In particular, the canonical
path of `formalization/.lake/build/lib/lean` is removed: this checkout's build path resolves into
the baseline checkout and contains compiled `FunctionalInequalities`, so string comparison before
`realpath` would be unsafe. A direct probe now requires both the baseline source and
`FunctionalInequalities/Basic.olean` to be unreadable.

The dedicated actor `CODEX_HOME` and runtime directory are readable/writable only when the current
executable is the installed Codex binary. Descendant shell and Lean processes inherit Seatbelt but
fail that `process-path` filter, preventing actor tools from reading `auth.json`, configuration, or
transcripts. Apps, plugins, browser/computer use, multi-agent features, skills, goals, hooks, image
generation, the network proxy, and web search are disabled. OpenAI service traffic remains
available to the Codex app-server; shell network commands invalidate the trace.

## Start the first real model run

From the experiment checkout, first authenticate the dedicated actor home through the user's
ChatGPT subscription. This is the only remaining start gate:

```bash
export H2_ISSUE2_STAGE1A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1a
experiments/humanize2_kls_issue2_staged/scripts/reset_run_state.sh
CODEX_HOME="$H2_ISSUE2_STAGE1A_STATE_ROOT/actor-codex-home" codex login
```

Do not copy a global `auth.json`, credential, transcript, or full Codex home into the state root.
After login, run exactly:

```bash
export H2_ISSUE2_STAGE1A_LIVE_RUN_ACK=issue2-stage1a-human-review
experiments/humanize2_kls_issue2_staged/scripts/run_stage_1a.sh
```

The runner resets to the pinned sentinel, rechecks the fixture/oracle pins, runs the isolation
battery, prepares pinned Humanize2, verifies subscription login, and starts exactly one actor. The
prompt requires the same actor turn to edit only `CandidateStage1A.lean` and repeatedly run
`lean CandidateStage1A.lean` until exit zero. After the turn, the runner executes the candidate
verifier and trace audit, writes only a compact audit JSON outside Git, and stops for human review.

The auditor requires exactly one session, one actor-root turn, and exactly one workspace root. It
rejects descendants, collaboration/subagent sources, MCP/browser/web/computer tools, additional
workspace roots, client/environment inspection, model/client launches, network commands,
parent-directory traversal, forbidden path references or outputs, sandbox denials, and Seatbelt
drift. Human review then applies the pinned eleven-item checklist; no reviewer model is used.

## First authenticated run

The first live run started from repository commit `83c37f2`. It used one actor session and one turn,
with no descendants or collaboration calls. The actor invoked Lean three times, repaired the
infinite-order notation from compiler diagnostics, and stopped with a compiling candidate at:

```text
/private/tmp/humanize2-kls-issue2-stage1a/actor-workspace/CandidateStage1A.lean
```

Candidate SHA-256:

```text
9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6
```

The initial post-run audit failed closed because its path scanner consumed JSON escape backslashes
after legal actor-root paths. The parser was repaired and given a regression test; the same session
trace then passed with exactly one session, one turn, zero descendants, six local `exec` calls, and
no errors. The model was not rerun. The decision and attempt records are:

- `research/decisions/2026-08-29-humanize2-kls-issue2-stage1a-trace-json-escaping.md`;
- `research/explorations/2026-08-29-humanize2-kls-issue2-stage1a-live-run.md`.

The candidate matches the requested formulas mechanically. One human-review question remains: its
universal function binder in `HasPoincare` is explicit, while the hidden implementation uses an
implicit binder. The propositions are logically the same, but only a human may decide whether that
API difference is acceptable for promotion to Stage 1B.

## Acceptance and mathematical status

Lean exit zero is necessary but insufficient. The human checklist in
`review/issue2_stage_1a_human_checklist.md` is the only semantic acceptance gate. An accepted
experimental candidate is still not a production proof or ledger event. Promotion into
`formalization/`, creation of a solution dossier, review certification, and ledger/manuscript
updates require their normal repository workflows and separate explicit decisions.

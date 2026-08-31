# Humanize2 staged Issue 2 autoformalization

## Status

The first subscription-authenticated Stage 1A actor run produced a compiling candidate and passed
the candidate, oracle-pin, and repaired complete-session trace gates. The user accepted the sole
remaining API question—the explicit function binder in `HasPoincare`—so Stage 1A is now a
human-accepted experimental dependency. The dedicated Stage 1B isolated harness has passed its
model-free reset, compilation, provenance, isolation, verifier, trace-policy, and deterministic
rerun tests. Authenticated Stage 1B Run 1 produced a locally compiling candidate and a clean
repaired trace, but the exact-surface verifier rejected five optimal-constant theorem APIs. Stage
1B is not accepted. Run 2 passed its original mechanical gates, but the user rejected its one
`unnecessarySimpa` linter diagnostic and authorized a fresh Run 3 whose exact Lean command must
exit zero with empty output. Run 3 changes no declaration or mathematical requirement.

The exact rejected Run 2 output remains published and pinned at
`review/pending/CandidateStage1BRun2.lean`; `review/STAGE_1B_RUN2_REVIEW.md` records its historical
review path. Do not edit or promote it.

The living semantic map is `SEMANTIC_DESIGN.md`. It records the mathematical meaning, Lean
encoding, intentional differences from production, downstream consequences, and acceptance state
of every layer without replacing the append-only decision history.

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

## Frozen Stage 1A harness

The Stage 1A prompt is `prompts/issue2_stage_1a_actor.md`, grounded only in
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

## Historical Stage 1A run procedure

The authenticated Stage 1A run has completed. These commands are retained only as provenance; do
not rerun them or reset the accepted external candidate when preparing Stage 1B:

```bash
export H2_ISSUE2_STAGE1A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1a
experiments/humanize2_kls_issue2_staged/scripts/reset_run_state.sh
CODEX_HOME="$H2_ISSUE2_STAGE1A_STATE_ROOT/actor-codex-home" codex login
```

Do not copy a global `auth.json`, credential, transcript, or full Codex home into the state root.
The historical live invocation was:

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

The candidate matches the requested formulas mechanically. The user accepted its explicit
universal function binder in `HasPoincare` as an intentional experimental API difference. A
byte-identical copy is pinned at `accepted/AcceptedStage1A.lean`; this acceptance permits only its
use as the input to Stage 1B.

## Model-free Stage 1B isolated harness

The next actor-facing specification and prompt are:

- `inputs/issue2_stage_1b_foundational_lemmas.md`;
- `prompts/issue2_stage_1b_actor.md`.

Stage 1B covers only energy nonnegativity, derivative/gradient compatibility, fixed-constant
accessors and monotonicity, the extended optimal constant, and its finite-versus-`⊤` boundary. Its
external workspace contains exactly, and in no other entry:

```text
AGENTS.md
TASK.md
AcceptedStage1A.lean
AcceptedStage1A.olean
CandidateStage1B.lean
```

`stage_1b_reset_actor_workspace.sh` copies the accepted source byte-for-byte, recompiles its
`.olean` in a separate external build directory with pinned Lean 4.33.0 and upstream Mathlib only,
checks hashes `9bb81dd6…` and `212cd1f5…`, copies both artifacts into the actor workspace, and makes
them mode `0444`. The actor directory is mode `0555`; the existing candidate alone is mode `0644`.
The rendered deny-default Seatbelt independently grants write access only to the literal candidate
path and outbound network access only to the Codex executable; descendant shell and Lean processes
fail that `process-path` filter. Reset always restores the compiler-failing Stage 1B sentinel and
writes a baseline hash/mode manifest outside the actor lane.

`stage_1b_verify_candidate.sh` enforces the sole `AcceptedStage1A` import, exact experimental and
nested namespaces, the thirteen requested declaration names and kinds, absence of extra public
surface and escape hatches, immutable accepted-artifact hashes/modes, and upstream-only Lean
compilation. It compiles a disposable candidate module outside the actor lane and imports it from
`verifier/issue2_stage_1b_surface.lean`, which checks every requested theorem type, the absence of a
measurable-space assumption from the derivative theorem, and the definitional optimal-constant
formula. The hidden known-good verifier fixture is test-only and denied to the actor.

`oracle/stage_1b_reference.sha256` independently pins only the thirteen relevant declaration
blocks extracted from existing `Basic.lean`; it does not pin the unrelated remainder of that
module. `review/issue2_stage_1b_human_checklist.md` is the human-only semantic/proof gate and is
outside the actor lane. `pins/stage_1b.sha256` freezes the source, prompt, checklist, accepted
dependency hashes, Lean/Lake metadata, fixture, configs, flow, patch, verifier surface, hidden test
fixture, reset/runner/auditor scripts, and tests.

The complete-session auditor requires one actor-root session, one turn, zero descendants, a sole
workspace root, the external-sandbox marker, only local execution/patch tools, no
collaboration/reviewer/browser/web/MCP/network/client-state/environment access, no forbidden path
or output, and a post-run mutation set exactly equal to `CandidateStage1B.lean`. It also rechecks
both accepted hashes and the candidate-only Seatbelt rule. Raw sessions and Codex/Humanize state
remain below the dedicated external state root.

Model-free reproduction uses a Stage 1B root separate from the historical Stage 1A state:

```bash
export H2_ISSUE2_STAGE1B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1b
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_reset_run_state.sh
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_verify_scaffold.sh
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_model_free_tests.sh
```

The runner exits `2` before any live action unless
`H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-human-review` is present. Even with that
acknowledgement, it exits `2` unless this new Stage 1B actor home reports `Logged in using ChatGPT`;
the Stage 1A login is not reused. Do not copy global credentials or paste the actor prompt into an
existing desktop task. After the actor stops, the runner performs candidate, oracle, immutable
artifact, complete-trace, and candidate-only mutation checks and then stops for the human
checklist. No model reviewer exists.

The setup prompt is historical now that the harness exists. The actor prompt is runner-internal and
must never be pasted into a repository task. Run 1 used this guarded live entry:

```bash
export H2_ISSUE2_STAGE1B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1b
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_reset_run_state.sh
CODEX_HOME="$H2_ISSUE2_STAGE1B_STATE_ROOT/actor-codex-home" codex login
export H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-human-review
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_run.sh
```

The explicit reset before `codex login` is required when the dedicated state root does not yet
exist. The runner resets again while preserving only that experiment-specific `auth.json`.

Do not execute that sequence again yet: it would reset the stopped Run 1 candidate. A retry must
first harden and repin the actor-facing theorem signatures, then start a fresh isolated session
only after explicit human authorization.

## First authenticated Stage 1B run

Run 1 started from commit `23e0cd3`. The actor used one session and one turn, had zero descendants,
read only the four permitted text files, edited only `CandidateStage1B.lean`, and ran Lean once.
Its first implementation compiled without a repair iteration. Candidate SHA-256:

```text
cfde84ba4de0fe4230331979b586fee5da43b4f20aae2bc27dbfdfd5ac9e2df9
```

The independent verifier recompiled the file but rejected the exact theorem surface. Five
optimal-constant theorems used explicit positional `μ` and, where applicable, `C` or `L` arguments
where the frozen API requires implicit parameters. `optimalPoincareConstant_eq_top_iff` used the
logically equivalent `¬ ∃ C, HasPoincare μ C` form instead of the frozen `∀ C, ¬ HasPoincare μ C`
type. Human checklist item 4 therefore failed before semantic/proof review.

The runner stopped before its final trace command. The first manual trace audit then misclassified
the legal Lean subtype delimiter `//` as an external path. After a parser-only repair and regression
test, re-auditing the same session returned `ok: true`: one session, one turn, zero descendants,
four local `exec` calls, accepted hashes unchanged, and only candidate mutation. The model was not
rerun. See:

- `research/explorations/2026-08-29-humanize2-kls-issue2-stage1b-live-run.md`;
- `research/decisions/2026-08-29-humanize2-kls-issue2-stage1b-trace-subtype-delimiter.md`.

## Authorized Stage 1B Run 2 boundary

The user approved a fresh Run 2 with one and only one actor-facing repair: the exact Lean headers
for the five optimal-constant theorems are now written literally in `TASK.md`. The headers expose
the already frozen implicit binders and universal-negation result type, but provide no proof text or
strategy. The other eight declarations, accepted dependency, verifier, oracle, checklist,
isolation, compiler loop, and model settings are unchanged.

Run 2 must use `/private/tmp/humanize2-kls-issue2-stage1b-run2`; it must not reset, reuse, or reveal
the Run 1 state. After the Run 2 preparation commit and model-free gates pass, the guarded sequence
is:

```bash
export H2_ISSUE2_STAGE1B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1b-run2
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_reset_run_state.sh
CODEX_HOME="$H2_ISSUE2_STAGE1B_STATE_ROOT/actor-codex-home" codex login
export H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-human-review
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_run.sh
```

The login must be performed directly for the new dedicated home; no `auth.json` is copied from Run
1 or Stage 1A.

## Authenticated Stage 1B Run 2: mechanical pass, human review pending

Run 2 started from preparation commit `b62f18f` in the fresh external root
`/private/tmp/humanize2-kls-issue2-stage1b-run2`. The new dedicated actor home was authenticated
directly through the user's ChatGPT subscription. The runner deterministically reset the fixture,
preserved only that home's authentication, and passed the pin, sentinel, isolation, immutable
dependency, forbidden-read, client-state, compiler, and app-server preflights before the model call.

The actor used one session and one turn with zero descendants. It read only the four permitted text
files, edited only `CandidateStage1B.lean`, and used the required Lean command. Its first compiler
pass found one Riesz-isometry namespace qualification error; one compiler-feedback repair produced
an exit-zero candidate. Candidate SHA-256:

```text
3778490dcbd79f4632795f9b541a281b9032596c4cfe415e81b627a4c48e6c4e
```

The independent candidate verifier passed the exact thirteen-declaration surface and upstream-only
compilation. The oracle pin and complete harness pinset passed. The complete trace audit returned
`ok: true`: one session, one turn, zero descendants, six local `exec` calls, no forbidden access or
tool use, and only candidate mutation. The compact audit JSON SHA-256 is
`f3519b985381ba083e85b422273a782943f572bc08daa6683fa0ad2f5829731f`.

The runner stopped before acceptance. Do not rerun or reset this Run 2 root while it awaits the
pinned thirteen-item human checklist. Mechanical PASS does not permit Stage 2A, production
promotion, a dossier, certification, ledger/manuscript edits, or any mathematical status change.
The full attempt record is
`research/explorations/2026-08-30-humanize2-kls-issue2-stage1b-run2.md`.

## Acceptance and mathematical status

Lean exit zero is necessary but insufficient. The human checklist in
`review/issue2_stage_1a_human_checklist.md` was the Stage 1A semantic acceptance gate; the accepted
artifact remains only an experimental dependency. Stage 1B Run 1 is a failed experimental
proof-generation attempt. Its compiling candidate is not accepted, certified, or a ledger event.
Promotion into `formalization/`, creation of a solution dossier, review certification, and
ledger/manuscript updates require their normal repository workflows and separate explicit
decisions.

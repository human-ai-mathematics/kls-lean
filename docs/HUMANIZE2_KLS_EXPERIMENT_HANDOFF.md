# Humanize2 KLS statement-fidelity experiment handoff

## 1. Purpose

This branch starts the first KLS-facing experiment after the verified Humanize2 → Codex → Lean
infrastructure baseline. The new question is semantic fidelity: can an actor generate the intended
Lean proposition from an informal functional-inequality specification without weakening or changing
it, and can a fresh reviewer detect a mismatch?

This is a calibration of the KLS autoformalization pipeline, not a new KLS theorem or proof.

## 2. Repository state

- Repository: `https://github.com/lyw-ops/numina-functional-inequalities-formalization`
- Branch: `humanize2-kls-autoformalization-experiment`
- Parent: `humanize2-lean-baseline`
- Base commit: `fe217458ba76941353474433d23f9d298791dd2f`
- Infrastructure handoff: `docs/HUMANIZE2_LEAN_BASELINE_HANDOFF.md`
- Experiment directory: `experiments/humanize2_kls_statement_fidelity/`
- Current experiment status: **RUN 2 PASS**

The branch was created in the independent worktree
`/private/tmp/numina-humanize2-kls-autoformalization`. That path is machine-local and is not part of
the reproduction contract.

## 3. Calibration target

The benchmark is `lem:linear-test-lower`: for a probability measure on $\mathbb R^D$ with finite
second moment, every admissible test has extended Rayleigh quotient at most the optimal Poincaré
constant, and the largest centered-covariance Rayleigh value is bounded by that constant. Dimension
zero and the extended zero-energy conventions are part of the target.

The node is stored in the A-series ledger, but it is a shared functional-inequality baseline used
in KLS reasoning. It is selected because the repository already contains:

- a natural-language statement and proof;
- a reusable Lean theorem;
- a node-specific Lean certificate; and
- an independent semantic-alignment audit.

Those artifacts provide a trusted oracle. This experiment does not alter or recertify them.

## 4. Implemented experiment

- `inputs/linear_test_lower.md`: frozen informal source presented to the actor.
- `candidate/CandidateStatement.lean`: compiling `True` sentinel replaced during the run.
- `fixtures/`: deterministic reset state.
- `oracle/reference.sha256`: pinned trusted-source hashes.
- `oracle/semantic_rubric.md`: ten mandatory semantic checks for the reviewer.
- `prompts/linear_test_statement_rlar.md`: role-separated actor/reviewer protocol.
- `scripts/reset_candidate.sh`: restores the sentinel.
- `scripts/verify_oracle_pins.sh`: detects oracle drift.
- `scripts/verify_scaffold.sh`: validates the pre-run state.
- `scripts/verify_candidate.sh`: rejects the sentinel/placeholders/unrelated edits and invokes Lean.
- `scripts/run_statement_rlar.sh`: runs the pinned upstream RLAR flow with isolated state.

## 5. Actor-reviewer protocol

The actor may read the frozen input plus `Basic.lean` and `Poincare.lean`. It must not read the
project certificate, solution certificate, dossier, ledger statement, knowledge summary, prior
semantic reviews, or experiment oracle. It edits one candidate file and must compile it.
It must perform that role directly without spawning or delegating to another agent.

The fresh reviewer is read-only and may inspect the full oracle. It checks all binders, the two
conjuncts, forbidden extra assumptions, existing-API reuse, Lean compilation, placeholder absence,
and full Git scope. A failed review returns concrete `notes` to the actor verbatim through RLAR.

The actor's blindness is currently enforced by instruction and trace audit, not filesystem
isolation. A run is invalid if its tool trace shows a forbidden oracle read.

## 6. Exact commands

From this branch's repository root, after completing the baseline installation/authentication:

```bash
export HUMANIZE_SENTRY=off
export HUMANIZE2_STATE_ROOT=/tmp/humanize2-kls-statement-fidelity

experiments/humanize2_kls_statement_fidelity/scripts/reset_candidate.sh
experiments/humanize2_kls_statement_fidelity/scripts/verify_scaffold.sh
experiments/humanize2_kls_statement_fidelity/scripts/run_statement_rlar.sh
experiments/humanize2_kls_statement_fidelity/scripts/verify_candidate.sh
```

The live run uses the baseline pins:

- Humanize2 commit `e8bcede84d4b3365378e04f9c80d0fd397903c30` (`hmz 0.1.0`);
- flowverse commit `22de7178543140edaaaef2bea351b51ac29e6f04`;
- Codex `gpt-5.6-sol` at `high` effort by default; and
- repository Lean/mathlib `v4.33.0`.

## 7. Acceptance criteria

A live run is a PASS only if:

1. the actor trace contains no forbidden oracle read;
2. only the candidate file changes;
3. the sentinel and proof placeholders are absent;
4. the candidate compiles with the pinned repository toolchain;
5. all ten semantic-rubric items pass;
6. the reviewer independently reads the oracle and reruns the checks; and
7. the official RLAR review ends with structured `done: true`.

Compilation without semantic acceptance is FAIL, not PARTIAL success. A passing experiment changes
no ledger or proof certification status.

## 8. Validation and live result

The following scaffold checks passed on 2026-08-29 before the authenticated run:

- `verify_scaffold.sh`: reset fixture matched, all four oracle hashes matched, and the sentinel
  type-checked with the pinned Lean toolchain;
- `verify_candidate.sh`: exited `2` with `candidate is still the unattempted sentinel`, the expected
  pre-run refusal;
- the verifier's success path was separately exercised with a temporary known-faithful proposition:
  oracle pins and Lean compilation passed, after which `reset_candidate.sh` restored the committed
  sentinel and a clean tree. This validates verifier mechanics, not model performance;
- `cd formalization && lake build`: 2,946 jobs completed successfully;
- the inherited Python baseline: 2 tests passed;
- the inherited two-file Lean baseline: both files compiled;
- `uv run --with pyyaml python research/check_ledger.py`: 2 ledgers, 195 nodes, 675 labels,
  0 structural errors;
- all baseline and experiment shell scripts passed `bash -n`; and
- a scoped credential-pattern scan found no secrets.

Two authenticated attempts then ran against fresh external Humanize state:

1. **Run 1: functional success / blind-validity failure.** It produced a faithful compiling
   candidate and the official reviewer accepted it, but the actor parent spawned its own
   oracle-backed reviewer child. The child generator had already finished and the candidate was not
   edited afterward, yet the actor lane crossed the declared oracle boundary. The run is invalid
   under the acceptance criteria. The prompt was hardened and the candidate reset.
2. **Run 2: PASS.** The fresh actor used four direct tool calls: it read only `AGENTS.md`, the frozen
   input, `Basic.lean`, `Poincare.lean`, and the candidate; edited only the candidate; ran the exact
   Lean command; and inspected its diff/status. It spawned no child and made no collaboration call.
   The separate read-only reviewer verified all four pins, compared every rubric item, compiled the
   candidate, audited placeholders and Git scope, and returned structured `done: true`.

Independent post-run verification confirmed:

- candidate SHA-256
  `fe594274d55934a6152a8be813c549682a930adac6952720583ae9ed6137990d`;
- `verify_candidate.sh` passed;
- the exact Lean command exited 0 without diagnostics;
- all ten semantic items passed, including dimension zero and both conjuncts;
- the sentinel and proof placeholders were absent; and
- only `candidate/CandidateStatement.lean` changed.

The accepted output is a proposition definition only. It proves no theorem and changes no ledger,
manuscript, dossier, review certification, or mathematical status. The concise decisions are
`research/decisions/2026-08-29-humanize2-kls-actor-lane-isolation.md` and
`research/decisions/2026-08-29-humanize2-kls-statement-fidelity-run.md`. Raw sessions and Humanize
state were not committed.

## 9. Authorization boundary

On 2026-08-29 the user explicitly authorized sending the frozen KLS linear-test specification,
allowed `Basic.lean`/`Poincare.lean` API material, candidate contents and diff, Git metadata, Lean
compiler output, and semantic-reviewer results to OpenAI for this experiment. Both recorded attempts
stayed within that content boundary. Credentials remained managed by the Codex CLI and were not
placed in prompts or repository files. A future experiment with different KLS content requires a
fresh authorization decision.

## 10. Recommended next experiment

Move from statement generation to a theorem/proof-generation calibration only after defining a
separate proof target and acceptance rubric. Preserve the accepted `Prop` candidate as the statement
fidelity result. Harden the next actor further with an oracle-free filesystem snapshot so blindness
does not depend only on prompt compliance and trace audit. Any future proof attempt must follow the
repository's proof workflow and cannot self-certify or change ledger status merely because Lean
compiles it.

## 11. Files to read first

1. `AGENTS.md`
2. this handoff
3. `docs/HUMANIZE2_LEAN_BASELINE_HANDOFF.md`
4. `experiments/humanize2_kls_statement_fidelity/README.md`
5. `inputs/linear_test_lower.md`
6. `prompts/linear_test_statement_rlar.md`
7. `oracle/semantic_rubric.md`

Do not modify KLS ledgers, manuscript claims, proof dossiers, or existing reviews as part of this
calibration.

## 12. Proof-generation and compiler-repair successor scaffold

The next-stage local scaffold now lives at `experiments/humanize2_kls_proof_repair/`. Its status is
**MODEL-FREE ISOLATION PASS / AUTHENTICATED RUN NOT STARTED**. It leaves the accepted
statement-fidelity candidate and all existing KLS mathematical assets unchanged.

### Target and non-targets

The only target is a disposable theorem, `humanize2_isolated_add_zero`, whose initial proof is
deliberately ill-typed. The experiment tests whether an actor can use real Lean 4.33.0 diagnostics
to repair it and pass an independent semantic/process reviewer. It does not prove or restate a KLS
claim, create a dossier, certify a proof, change a ledger/manuscript, or establish general
autoformalization ability.

### Physical separation and actual actor visibility

The actor runs in an external three-file workspace:

```text
AGENTS.md
CandidateProof.lean
TASK.md
```

A rendered macOS Seatbelt profile uses `deny default` and allowlists file data only for that
workspace, the macOS runtime, installed Codex app, pinned Lean toolchain, actor-only Codex home, and
actor-only temporary directory. Ancestors receive metadata-only access. The repository and a
separate reviewer Codex home are not readable. The reviewer runs as a separate read-only Codex
app-server in the full repository and may read the oracle. Separate homes prevent reviewer
transcripts from entering actor-visible state.

Humanize2 is still pinned to
`e8bcede84d4b3365378e04f9c80d0fd397903c30`. The model-free preparer clones it outside Git and
applies the pinned `humanize2-codex-seatbelt.patch`. The patch wraps only the workspace-write actor
app-server in Seatbelt and gives actor/reviewer their separate homes. Since Seatbelt cannot nest,
the actor turn's internal sandbox field is the external-sandbox marker; the reviewer retains the
upstream read-only mode.

### Reset, compiler loop, verifier, trace, and oracle

`reset_run_state.sh` clears only known paths below a dedicated `/private/tmp` state root, preserves
lane authentication files, recreates the exact actor fixture, clears both session trees, and
renders the Seatbelt profile. `verify_scaffold.sh` requires the expected Lean type mismatch before
a run. The actor must repeatedly execute `lean CandidateProof.lean` and cannot finish before exit
zero.

`verify_candidate.sh` enforces exact statement preservation, a single theorem, no
`sorry`/`admit`/`axiom`/`unsafe`, the exact visible file set, and Lean success. The custom Humanize2
flow holds the actor for at most three rounds and uses a fresh reviewer each time. Reviewer prose is
not returned to the actor; closed finding codes map to deterministic, non-oracular feedback.

`audit_actor_trace.py` audits every actor-home JSONL record and requires exactly one actor-root
session, rejecting any other session or descendant, collaboration, unexpected tools or roots,
shell network/client-state access, forbidden path references, missing
external-sandbox markers, Seatbelt drift, and denials. It outputs only a compact summary outside
the repository. `oracle/reference.sha256` pins the reference, ten-item rubric, actor fixtures,
prompt, isolation and flow configs, flow implementation, trace auditor, candidate/workspace
verifiers and their shared helper, and Humanize2 patch.

### Validation and authorization state

Model-free validation passed for deterministic reset, the expected failing compiler path, the
disposable success path, trace-auditor unit tests, oracle/ledger/reviewer-state read denial,
actor-local writes, Lean execution, Codex app-server startup inside Seatbelt, and the patched
Humanize2 adapter. Raw
transcripts, credentials, tokens, and Humanize/Codex state remain external.

No authenticated model run was performed for this successor scaffold. Its disposable live runner
requires `H2_PROOF_LIVE_RUN_ACK=disposable-only` and separate actor/reviewer Codex authentication.
Replacing the disposable fixture with any KLS statement, theorem, proof context, compiler output,
or review still requires fresh explicit user authorization. No mathematical conclusion or status
change was produced.

## 13. Authorized staged Issue 2 autoformalization

On 2026-08-29 the user supplied the next authorization: use the existing Issue 2 linear-test
development as the first real-model KLS autoformalization domain, authenticate the actor through
the user's ChatGPT subscription, proceed in small dependency layers, and stop after each layer for
human review. This authorization is limited to Issue 2. It does not cover another KLS target,
automatic production promotion, a model reviewer, or access to the existing Issue 2 answer.

The experiment plan is in `experiments/humanize2_kls_issue2_staged/`. Its current status is
**STAGE 1A HUMAN-ACCEPTED EXPERIMENTAL DEPENDENCY / STAGE 1B RUN 1 EXACT-SURFACE FAIL /
RUN 2 MECHANICAL PASS / RUN 2 HUMAN REVIEW PENDING / STAGE 2A NOT STARTED**.

### Why Issue 2 is a reconstruction benchmark

Issue 2 already has a compiled, reviewed Lean implementation in the repository. The purpose of the
new experiment is not to obtain a previously unknown proof. It is to measure whether an isolated
actor can reconstruct the development from frozen mathematical specifications and compiler
feedback. The existing `Basic.lean`, `Poincare.lean`, project certificate, solution, semantic
reviews, and ledger binding are hidden human-oracle material. They must never be mounted in the
actor filesystem or included in actor feedback.

### Layer hierarchy

1. Stage 1A: admissible-test, Dirichlet-energy, and fixed-constant Poincaré definitions only.
2. Stage 1B: foundational lemmas and the extended optimal constant.
3. Stage 2A: linear-test geometry.
4. Stage 2B: linear-test analysis and the fixed-constant bound.
5. Stage 3: extended Rayleigh quotient and optimal-constant comparison.
6. Stage 4: covariance and finite-dimensional spectral bridge.
7. Stage 5: abstract, Euclidean, and node-specific Issue 2 certificates.

An earlier stage becomes visible to the next actor only after explicit human acceptance. A human
rejection ends that actor session; a repair request starts a fresh isolated run. No hidden proof or
reviewer reasoning is returned as compiler feedback.

### Frozen Stage 1A artifacts

- `inputs/issue2_stage_1a_basic_vocabulary.md` is the complete actor-facing mathematical source.
- `prompts/issue2_stage_1a_actor.md` is the Stage 1A actor prompt.
- `review/issue2_stage_1a_human_checklist.md` is human-only and must remain outside the actor lane.
- `fixtures/actor_workspace/` contains the committed `AGENTS.md`, byte-identical `TASK.md`, and
  compiler-failing `CandidateStage1A.lean.initial`.
- `pins/stage_1a.sha256` freezes the specification, prompt, checklist, fixture, and reset/verifier
  scripts.

Stage 1A asks for exactly three public declarations in the experimental namespace
`Issue2Autoformalization.Stage1A`: `IsAdmissible`, `dirichletEnergy`, and `HasPoincare`. It excludes
all lemmas, the optimal constant, linear tests, Rayleigh quotients, covariance, and the final lower
bound.

### Dedicated runner and corrected workspace entry

The committed reset rebuilds a Stage 1A-specific external workspace with exactly `AGENTS.md`,
`TASK.md`, and `CandidateStage1A.lean`. The scaffold verifier requires the pinned sentinel and its
expected nonzero Lean diagnostic. The candidate verifier checks the exact import list, namespace,
three requested declarations, structure fields, forbidden escapes, and compilation under an
upstream Mathlib-only `LEAN_PATH`.

The repeated `TASK.md`/`CandidateStage1A.lean` absence message came from running the actor prompt in
an existing Codex desktop task whose declared roots are the main KLS workspace and a visualization
directory. The fixture was present at
`/private/tmp/humanize2-kls-issue2-stage1a/actor-workspace`; it was intentionally not mounted in that
task. Do not copy the fixture into the main workspace and do not paste the prompt into an existing
KLS task. `scripts/run_stage_1a.sh` now starts the correct new Humanize2-managed app-server session,
with the external fixture as both process `cwd` and the sole turn workspace root.

The rendered deny-default Seatbelt profile allows file data only for the actor root, macOS/Codex
runtime, pinned Lean toolchain, and compiled upstream Mathlib packages. Canonical-path validation
removes the checkout build root even though its symlink resolves into the baseline checkout, and a
direct probe denies the existing compiled `FunctionalInequalities/Basic.olean`. Repository source,
all three KLS checkouts, solutions, reviews, ledgers, statement-fidelity oracle, and the hidden
Stage 1A reference also fail direct read probes.

Actor Codex client state is stored in a dedicated external home. Seatbelt grants that home and its
runtime directory only when the current executable is Codex, so descendant shell/Lean tools cannot
read authentication or transcripts. The isolated config disables apps, plugins, browser/computer
use, multi-agent features, skills, goals, hooks, image generation, network proxy, and web search.
The complete-session auditor requires exactly one session, no descendant, one turn, and exactly one
workspace root; it also rejects collaboration, forbidden tools/paths/outputs, environment/client
inspection, model launches, network commands, traversal, denials, and profile drift.

`oracle/stage_1a_reference.sha256` pins the hidden `Basic.lean` reference. The main Stage 1A pinset
freezes the human checklist as semantic rubric plus the fixture, prompt, toolchain/Lake metadata,
flow, isolation profile, Humanize2 patch, verifier, runner, auditor, and tests. Human review is the
only acceptance gate.

### Authenticated Stage 1A result

The dedicated actor home was authenticated directly through the user's ChatGPT subscription; no
global credential file was copied. The first live run started from commit `83c37f2`, after every
reset, pin, isolation, forbidden-read, compiler, and app-server preflight passed.

The actor used one session and one turn, invoked Lean three times, repaired an infinite-order
notation error from compiler diagnostics, and produced a compiling candidate with SHA-256
`9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6`. Candidate and hidden-oracle
pin verification passed.

The first trace audit failed closed only because its scanner included JSON escape backslashes after
legal actor-root paths. The parser fix added a regression test and did not alter the prompt,
candidate, Seatbelt, compiler environment, or session. Re-auditing that same trace returned
`ok: true`: one session, one turn, zero descendants, six local `exec` calls, and no errors. The model
was not rerun.

The user accepted the only identified review question: the candidate's explicit `HasPoincare`
function binder (`∀ f`) may intentionally differ from the hidden implementation's implicit binder
(`∀ ⦃f⦄`). All eleven Stage 1A checklist items are therefore closed. A byte-identical accepted copy
is stored at `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage1A.lean` with the same
SHA-256. This is only a stage-transition dependency, not production promotion or certification.

### Stage 1B isolated harness: model-free pass

The next actor-facing files are now drafted:

- `inputs/issue2_stage_1b_foundational_lemmas.md` freezes the mathematical declaration surface;
- `prompts/issue2_stage_1b_actor.md` freezes the single-session compiler-feedback instructions.

Stage 1B is limited to Dirichlet-energy nonnegativity, Fréchet derivative/gradient compatibility,
fixed-constant accessors and monotonicity, the `ENNReal` optimal constant, and its
finite-versus-`⊤` boundary. It excludes linear tests, Rayleigh quotients, covariance, spectral
claims, final Issue 2 assembly, and every other KLS target.

The completed reset uses a Stage 1B-specific external state root and reconstructs exactly these
actor-visible entries:

```text
AGENTS.md
TASK.md
AcceptedStage1A.lean
AcceptedStage1A.olean
CandidateStage1B.lean
```

`AcceptedStage1A.lean` is copied byte-for-byte from the human-accepted source and retains the
explicit `∀ f` binder. Its SHA-256 is
`9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6`. The reset compiles
`AcceptedStage1A.olean` in a separate external build directory with pinned Lean 4.33.0 and an
upstream-Mathlib-only `LEAN_PATH`; deterministic reruns produce SHA-256
`212cd1f5a0c20d2f3974c5948ea4c26550409a5b3b7b47a4b65e1e9cdf65a3a0`. Both artifacts are mode
`0444`, the fixture text is mode `0444`, the actor directory is mode `0555`, and only the existing
`CandidateStage1B.lean` is owner-writable. The rendered Seatbelt independently allowlists writes
only to that literal candidate path and outbound network access only to the Codex executable;
descendant shell and Lean tools fail that `process-path` filter. A hash/mode baseline outside the
actor lane supports post-run mutation verification.

The sentinel imports only `AcceptedStage1A` and fails on `stage1BImplementationRequired`. The
candidate verifier rejects the sentinel; enforces the sole import, exact namespace nesting,
thirteen names and declaration kinds, and forbidden escape/public-surface forms; rechecks both
accepted hashes and physical modes; compiles the candidate outside the actor lane against the
accepted `.olean` plus upstream Mathlib only; and imports a hidden exact-surface checker covering
all thirteen requested theorem types and the definitional infimum formula. The checker also proves
that `norm_fderiv_eq_norm_gradient` needs no measurable-space instance. The known-good verifier
fixture is model-free test material, not an actor input.

`oracle/stage_1b_reference.sha256` is independent of the accepted dependency and hashes only the
thirteen relevant existing declaration blocks extracted from `Basic.lean`, not the rest of the
module. `review/issue2_stage_1b_human_checklist.md` remains outside the actor lane and is the only
semantic/proof acceptance gate. `pins/stage_1b.sha256` freezes the specification, actor prompt,
human checklist, accepted artifacts and hashes, Lean/Lake metadata, fixture, isolation/config
files, Humanize2 adapter, flow, verifier surface, hidden test fixture, runner, auditor, and tests.

The single-session flow constructs one actor at the external root and has no reviewer. The runner
refuses before a live call unless the exact acknowledgement
`H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-human-review` is present and a new Stage 1B-specific
`CODEX_HOME` reports `Logged in using ChatGPT`. It does not reuse or reset the stopped external
Stage 1A candidate or actor home. The same actor must edit the candidate and repeatedly use exactly
`lean CandidateStage1B.lean`; compiler diagnostics are the only feedback loop.

The complete-session auditor reads every JSONL session record in the dedicated actor home and
requires one actor-root session, one turn, zero descendants, one workspace root, and the
external-sandbox marker. It allows only local execution/patch tools and rejects collaboration,
reviewer, browser, web, MCP, computer-use, network/model/client-state/environment access,
parent traversal, forbidden paths or outputs, sandbox denials, or Seatbelt drift. It compares the
post-run workspace with the external baseline and requires the mutation set to be exactly
`CandidateStage1B.lean`, then rechecks both accepted artifact hashes.

Model-free commands and observed exit codes on 2026-08-29:

```text
experiments/humanize2_kls_issue2_staged/scripts/verify_candidate.sh /private/tmp/humanize2-kls-issue2-stage1a/actor-workspace
  exit 0
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_model_free_tests.sh
  exit 0
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/pins/stage_1b.sha256
  exit 0
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_run.sh  # acknowledgement absent
  exit 2
H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-human-review experiments/humanize2_kls_issue2_staged/scripts/stage_1b_run.sh  # fresh dedicated home not logged in
  exit 2
cd formalization && lake build
  exit 0; 2,946 jobs
uv run --with pyyaml python research/check_ledger.py
  exit 0; 2 ledgers, 195 nodes, 675 labels, 0 structural errors
git diff --check
  exit 0
```

Authenticated Stage 1B Run 1 used this self-contained sequence:

```bash
export H2_ISSUE2_STAGE1B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1b
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_reset_run_state.sh
CODEX_HOME="$H2_ISSUE2_STAGE1B_STATE_ROOT/actor-codex-home" codex login
export H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-human-review
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_run.sh
```

The reset before `codex login` is mandatory on a fresh machine or after deleting the Stage 1B
state root: Codex rejects a `CODEX_HOME` path that does not exist. The runner performs another
deterministic reset and preserves only the dedicated `auth.json`. The actor prompt is an internal
runner input, not a prompt to paste into this or any other repository task.

Do not execute that sequence again yet: the runner would reset the stopped Run 1 candidate. The
authorization remains limited to the frozen Issue 2 Stage 1B specification, accepted Stage 1A
dependency, candidate contents, and actual Lean diagnostics in one human-stopped actor session. It
does not authorize exposing the existing Issue 2 answer, using a model reviewer, promoting output,
continuing to Stage 2A, or working on another KLS target.

### Authenticated Stage 1B Run 1: exact-surface failure

Run 1 started from commit `23e0cd3`. Every preflight passed before the subscription model call. The
actor used one session and one turn, spawned no descendants, read only the permitted text files,
edited only `CandidateStage1B.lean`, and ran Lean once. Its first implementation compiled with no
repair iteration. Candidate SHA-256:

```text
cfde84ba4de0fe4230331979b586fee5da43b4f20aae2bc27dbfdfd5ac9e2df9
```

The independent verifier recompiled the candidate but rejected its exact API. Five
optimal-constant theorems exposed `μ`, and where applicable `C` or `L`, as explicit positional
arguments rather than the frozen implicit parameters. `optimalPoincareConstant_eq_top_iff` used
the logically equivalent `¬ ∃ C, HasPoincare μ C` proposition rather than the frozen
`∀ C, ¬ HasPoincare μ C` Lean type. Human checklist item 4 failed, so no semantic/proof acceptance
review began.

The runner stopped at that verifier and did not reach its final trace command. A manual trace audit
initially misclassified the legal Lean subtype delimiter `//` in the candidate patch as an external
path. The parser fix excludes doubled slashes from absolute-path tokens and adds a regression test.
Re-auditing the same session, without rerunning the model, returned `ok: true`: one root session,
one turn, zero descendants, four local `exec` calls, accepted hashes unchanged, and only candidate
mutation.

The actor-facing prose specified the correct mathematics but did not give the full Lean signatures
of the five exact-surface theorems. Any retry must first harden and repin those signatures, then use
a fresh isolated actor session after an explicit human repair decision. Do not weaken the checker
to accept Run 1.

Observed Run 1 and post-run exit codes:

```text
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_run.sh
  exit 1 at stage_1b_verify_candidate.sh
lean CandidateStage1B.lean  # actor lane and independent post-run check
  exit 0
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_verify_candidate.sh <actor-root>
  exit 1; five exact-surface errors
stage_1b_audit_actor_trace.py  # original parser
  exit 1; false path token //
stage_1b_audit_actor_trace.py  # repaired parser, same session
  exit 0; no errors
```

### Authorized Stage 1B Run 2 boundary

On 2026-08-30 the user explicitly approved a fresh Stage 1B Run 2 with only the five exact Lean
signatures hardened. The actor-facing specification now prints the complete theorem headers for
`optimalPoincareConstant_le`, `le_optimalPoincareConstant`,
`optimalPoincareConstant_eq_top_of_no_finite`,
`optimalPoincareConstant_ne_top_of_hasPoincare`, and
`optimalPoincareConstant_eq_top_iff`. These headers reveal no proof text or strategy and leave the
precommitted surface checker unchanged.

Run 2 must use the new external root
`/private/tmp/humanize2-kls-issue2-stage1b-run2` and a newly authenticated dedicated `CODEX_HOME`.
It must not reset or reuse the stopped Run 1 state. The other eight declarations, accepted Stage 1A
dependency, oracle, human checklist, Seatbelt profile, compiler-feedback loop, trace requirements,
model, and effort remain unchanged. The rationale is recorded append-only in
`research/decisions/2026-08-30-humanize2-kls-issue2-stage1b-run2-signature-hardening.md`.

### Authenticated Stage 1B Run 2 result

Run 2 started from preparation commit `b62f18f` and used the new external state root
`/private/tmp/humanize2-kls-issue2-stage1b-run2`. Its dedicated `CODEX_HOME` was authenticated
directly through the user's ChatGPT subscription; no Run 1, Stage 1A, or global credential file was
copied. Deterministic reset restored the five-entry fixture and preserved only that dedicated
authentication. Every pin, sentinel, immutable-dependency, physical-isolation, forbidden-read,
client-state, compiler, and app-server preflight passed before the model call.

The actor used exactly one session and one turn, with zero descendants and no collaboration or
reviewer. It read only `AGENTS.md`, `TASK.md`, `AcceptedStage1A.lean`, and its candidate, edited only
`CandidateStage1B.lean`, and invoked the required Lean compiler. The first pass exposed one
Mathlib namespace qualification error for the Riesz isometry. One compiler-feedback repair made
the second pass succeed. Candidate SHA-256:

```text
3778490dcbd79f4632795f9b541a281b9032596c4cfe415e81b627a4c48e6c4e
```

The runner and an independent post-run verifier both passed the exact thirteen-declaration surface
and upstream-Mathlib-only compilation. The separately pinned hidden `Basic.lean` surface and the
complete Stage 1B pinset matched. The complete trace audit returned `ok: true`: one session, one
turn, zero descendants, six local `exec` calls, no forbidden access/tool/path/output or Seatbelt
denial, and only candidate mutation. Compact trace-audit SHA-256:

```text
f3519b985381ba083e85b422273a782943f572bc08daa6683fa0ad2f5829731f
```

The guarded runner exited zero and stopped for the human-only thirteen-item semantic/proof
checklist. Stage 1B is therefore mechanically successful but not yet accepted as the Stage 2A
dependency. Do not reset or rerun the stopped Run 2 root. Raw transcripts, authentication, tokens,
Humanize/Codex state, machine-private configuration, and generated `.olean` files remain external
and uncommitted. The append-only attempt record is
`research/explorations/2026-08-30-humanize2-kls-issue2-stage1b-run2.md`.

The validated harness implementation commit is
`666fff6983b4364419132f1356eaac00e6771aa6`; its original handoff commit is `e5f12b2`. Raw
transcripts, credentials, tokens, Codex/Humanize state, machine-private configuration, and the
generated `.olean` are not committed. Do not paste the Stage 1B actor prompt into an existing
desktop task.

The completed Stage 1A actor used one dedicated subscription-authenticated `CODEX_HOME`; there was
no model reviewer. Its human acceptance is only an experimental stage gate: it creates no dossier,
certification, ledger/manuscript change, or mathematical status change. Stage 1B has a new
dedicated state root and stops at the same human boundary.

The harness rationale and the canonical-path defect/fix are recorded append-only in
`research/decisions/2026-08-29-humanize2-kls-issue2-stage1a-dedicated-runner.md`. The live attempt
and trace-parser repair are recorded append-only in
`research/explorations/2026-08-29-humanize2-kls-issue2-stage1a-live-run.md` and
`research/decisions/2026-08-29-humanize2-kls-issue2-stage1a-trace-json-escaping.md`. The human
acceptance and Stage 1B prompt boundary are recorded in
`research/decisions/2026-08-29-humanize2-kls-issue2-stage1a-acceptance-stage1b-prompt.md`.

The Stage 1B harness rationale and model-free validation are recorded append-only in
`research/decisions/2026-08-29-humanize2-kls-issue2-stage1b-isolated-harness.md`. The authenticated
failed attempt is recorded in
`research/explorations/2026-08-29-humanize2-kls-issue2-stage1b-live-run.md`; the subtype-delimiter
audit repair is recorded in
`research/decisions/2026-08-29-humanize2-kls-issue2-stage1b-trace-subtype-delimiter.md`. Run 1
changed no production Lean, solution, review, ledger, manuscript, proof certification, or
mathematical status.

Run 2 likewise changed no production Lean, solution, persisted review, ledger, manuscript, proof
certification, or mathematical status. Human acceptance and any Stage 2A authorization remain
separate future decisions.

The runner-entry clarification and fresh-`CODEX_HOME` reset requirement are recorded append-only in
`research/decisions/2026-08-29-humanize2-kls-issue2-stage1b-runner-entry.md`.

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
**STAGE 1A SPEC/PROMPT FROZEN / RUNTIME HARNESS NOT YET BUILT / MODEL RUN NOT STARTED**.

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
- `prompts/issue2_stage_1a_actor.md` is the next actor prompt.
- `review/issue2_stage_1a_human_checklist.md` is human-only and must remain outside the actor lane.
- `pins/stage_1a.sha256` freezes all three artifacts.

Stage 1A asks for exactly three public declarations in the experimental namespace
`Issue2Autoformalization.Stage1A`: `IsAdmissible`, `dirichletEnergy`, and `HasPoincare`. It excludes
all lemmas, the optimal constant, linear tests, Rayleigh quotients, covariance, and the final lower
bound.

### Next operational step

Do not send the prompt yet. First build a Stage 1A-specific external three-file workspace and
deterministic reset. Its Seatbelt profile may read the pinned Lean toolchain and compiled upstream
Mathlib artifacts, but not any compiled or source `FunctionalInequalities` module. Add a candidate
verifier and reuse or extend the complete-session trace audit. Run adversarial oracle, repository,
solution, review, ledger, and certificate read probes before authenticating the model call.

The actor uses one dedicated subscription-authenticated `CODEX_HOME`; there is no model reviewer.
After compilation and trace verification, stop and hand `CandidateStage1A.lean`, its diff, compiler
result, and compact trace summary to a human. Human acceptance is only an experimental stage gate:
it creates no dossier, certification, ledger/manuscript change, or mathematical status change.

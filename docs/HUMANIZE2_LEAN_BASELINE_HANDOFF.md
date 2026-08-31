# Humanize2 → Codex → Lean baseline handoff

> **Migration note (2026-08-31).** The canonical published copy now lives in
> `https://github.com/numina-functional-inequalities/kls-lean` on
> `autoformalization-experiments`. Historical repository, branch, and commit identifiers below
> describe the original run and are retained as provenance.

## 1. Objective

This branch evaluates HumanFIA Humanize2 as a harness（执行框架）for Lean/KLS
autoformalization（自动形式化）. It establishes repository access, bounded editing, real Lean
compiler feedback（编译器反馈）, proof generation（证明生成）, proof repair（证明修复）, and an
actor-reviewer architecture（执行者—审查者架构）. It does **not** formalize, restate, or change
KLS mathematics.

## 2. Repository state

| Item | Value |
| --- | --- |
| Repository | `https://github.com/lyw-ops/numina-functional-inequalities-formalization` |
| Branch | `humanize2-lean-baseline` |
| Parent/base branch | fork `main` (`origin/main`) |
| Base commit | `f620cadf7073ce8a6c31713047a2e36e759b5536` |
| Final relevant implementation commit | `0b004725e081d3092cbc03e5b9d76513b9ff970f` |
| Documentation commit | the branch tip containing this file; inspect with `git rev-parse HEAD` |
| Repository toolchain | `leanprover/lean4:v4.33.0` |
| Lean observed | 4.33.0, commit `d8b18978322de05a8f3dba51ef03cf5461676c17` |
| Lake observed | `5.0.0-src+d8b1897` |
| mathlib | tag `v4.33.0`; manifest commit `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Humanize2 | `hmz 0.1.0`, commit `e8bcede84d4b3365378e04f9c80d0fd397903c30` |
| Official flowverse | commit `22de7178543140edaaaef2bea351b51ac29e6f04` |
| Codex baseline | `codex-cli 0.150.0-alpha.8`, `gpt-5.6-sol`, `high` effort |

The implementation SHA is intentionally the last experiment/harness commit before this handoff:
a Git commit cannot contain its own SHA. The pushed branch tip is the authoritative documentation
revision.

## 3. What was implemented

All executable experiment material is isolated under `experiments/humanize2_baseline/`:

- `python_demo/`: a two-test `unittest` task and the repaired `add` function;
- `lean_demo/AddZeroTest.lean`: the compiler-feedback proof-repair task;
- `lean_demo/ActorReviewerTest.lean`: the RLAR actor-reviewer task;
- `fixtures/`: committed deliberately broken initial versions for reproducible resets;
- `prompts/`: exact read-only, editing, Lean repair, and reviewer instructions;
- `configs/ralph_budget.yaml`: a 0.001-million-output-token bound;
- `scripts/`: reset, run, flowverse pin, and independent verification commands; and
- `.gitignore`: Python cache and local Humanize state exclusions.

The two repaired Lean targets import the existing `FunctionalInequalities` library but are not
added to its source tree or default Lake targets. Repository rationale and failures are recorded
append-only in `research/decisions/2026-08-29-humanize2-lean-baseline.md`.

## 4. Humanize2 architecture

Humanize2 is the harness（执行框架）around a backend coding agent. Here, `hmz` starts the Codex CLI
backend; Codex retains its own authentication and exposes its normal shell and file tools. A flow
determines when sessions start, what persists, and what ends the run:

- `chat` opens one Codex session for read-only repository inspection.
- `ralph_loop` opens a fresh agent session each round. Conversation memory does not carry, but the
  shared Git working tree does, so a later round observes earlier edits. Humanize2 also keeps
  resumable round/token state per flow and workspace; the runners isolate that state per
  experiment.
- The pinned upstream `rlar` flow holds one actor session and opens a fresh reviewer session after
  each actor turn. The actor has `workspace-write`; the reviewer has `read-only`.
- RLAR requires a structured `Review { done: bool, notes: str }`. `done: true` ends the flow. When
  `done` is false, `notes` is transferred to the actor as its next prompt verbatim. This is the
  normal feedback channel for a reviewer-requested repair.

Repository state, rather than model prose, connects proof generation to verification. The actor
invokes `lake env lean`, sees the actual diagnostic, edits the proof, and invokes the same command
again. The reviewer independently reads the final tree, invokes Lean, scans placeholders, and
compares the declaration with the committed version.

## 5. Environment setup

Observed machine environment:

| Component | Observed value |
| --- | --- |
| OS / architecture | macOS 26.6.2 (25G83), arm64 host |
| Git | 2.50.1 (Apple Git-155) |
| Python | 3.14.5 |
| uv | 0.9.0 |
| Codex auth | `codex login status` reported `Logged in using ChatGPT` |
| Claude CLI | not installed; not required |
| elan | 4.1.2 |
| Lean binary | x86_64 build under the pinned elan toolchain |

Machine setup is separate from repository content. Install the inspected Humanize2 revision with:

```bash
uv tool install \
  'git+https://github.com/humanfia/humanize2.git@e8bcede84d4b3365378e04f9c80d0fd397903c30'
hmz --version
hmz --help
```

Configure Codex separately; never place credentials in the repository:

```bash
codex login
codex login status
```

Prepare a clone and machine-local run state:

```bash
git clone https://github.com/lyw-ops/numina-functional-inequalities-formalization.git
cd numina-functional-inequalities-formalization
git fetch origin humanize2-lean-baseline
git switch humanize2-lean-baseline

export HUMANIZE_SENTRY=off
export HUMANIZE2_STATE_ROOT=/tmp/humanize2-baseline-state
# Only if hmz is not on PATH:
# export HMZ_BIN=/absolute/path/to/hmz

cd formalization
lake build
cd ..
```

The live commands send the scoped prompts, named disposable files, repository metadata, and
compiler/test output to the authenticated OpenAI Codex backend. Obtain authorization before using
them with non-public or sensitive material. `HUMANIZE2_STATE_ROOT` must be absolute and outside
the repository; every runner selects a different `HUMANIZE_HOME` beneath it.

## 6. Baseline experiments

### Python baseline

Reset and run:

```bash
experiments/humanize2_baseline/scripts/reset_python_demo.sh
experiments/humanize2_baseline/scripts/run_python_read_only.sh
git diff --name-only
experiments/humanize2_baseline/scripts/run_python_ralph.sh
experiments/humanize2_baseline/scripts/verify_python.sh
```

The read-only Codex session found the correct worktree, inspected exactly the named Python files,
identified `return a - b`, and predicted both failures. External Git inspection confirmed it made
no new mutation. The bounded Ralph actor changed subtraction to addition and ran the exact
two-test command. The final isolated replay ended after one round with both tests passing and a
clean tree. The test file was unchanged.

### Lean baseline

Reset the proof-repair fixture and run:

```bash
cp experiments/humanize2_baseline/fixtures/lean/AddZeroTest.lean.initial \
  experiments/humanize2_baseline/lean_demo/AddZeroTest.lean
experiments/humanize2_baseline/scripts/run_lean_repair.sh
experiments/humanize2_baseline/scripts/verify_lean_add_zero.sh
```

The task was:

```lean
theorem add_zero_test (n : Nat) : n + 0 = n := by
  exact Nat.zero_add n
```

Codex actually invoked:

```bash
cd formalization && \
  lake env lean ../experiments/humanize2_baseline/lean_demo/AddZeroTest.lean
```

Lean reported that `Nat.zero_add n` has type `0 + n = n` while `n + 0 = n` was expected. Codex
replaced only the proof term with `Nat.add_zero n`, reran the identical compiler command, and got
exit 0. The final isolated replay took one Ralph round. Independent compilation passed; the
declaration was unchanged and no `sorry`, `admit`, or `axiom` remained.

### Actor-reviewer baseline

Reset and run:

```bash
cp experiments/humanize2_baseline/fixtures/lean/ActorReviewerTest.lean.initial \
  experiments/humanize2_baseline/lean_demo/ActorReviewerTest.lean
experiments/humanize2_baseline/scripts/run_lean_rlar.sh
experiments/humanize2_baseline/scripts/verify_lean_actor_reviewer.sh
experiments/humanize2_baseline/scripts/verify_lean.sh
```

The runner first fetches and detaches the official flowverse at the recorded commit. The actor
observed Lean reject `Nat.add_assoc a b 0` for the commutativity goal, replaced only that proof
with `Nat.add_comm a b`, and recompiled successfully. A fresh official read-only reviewer then:

1. ran the exact Lean command and observed exit 0;
2. confirmed the theorem was genuinely proved;
3. scanned for placeholders;
4. audited staged, unstaged, and full repository status/diffs; and
5. compared the declaration to `HEAD` for weakening or renaming.

The reviewer returned structured `done: true` on the first official review. Therefore no
reviewer-requested repair iteration occurred in this successful baseline. If it had returned
`done: false`, its `notes` would have become the held actor session's next prompt verbatim.

## 7. Results

| Capability | Status | Evidence |
| --- | --- | --- |
| Humanize2 installation | PASS | pinned `hmz 0.1.0`; version/help succeeded |
| Codex backend | PASS | authenticated read-only and write sessions opened |
| Repository editing | PASS | minimal Python and Lean proof-only changes persisted |
| Iterative flow | PASS | bounded Ralph cycles ended normally; state isolated |
| Lean compiler invocation | PASS | actors and reviewer ran the pinned compiler |
| Lean proof repair | PASS | real failing diagnostic followed by exit 0 |
| Actor-reviewer flow | PASS | pinned RLAR reviewer returned structured `done: true` |

All statuses are based on the actual Git tree, tests, cycle metadata, or Lean compiler, not on
generated summaries alone.

Final branch verification before the documentation commit:

```bash
experiments/humanize2_baseline/scripts/verify_python.sh
experiments/humanize2_baseline/scripts/verify_lean.sh
cd formalization && lake build
cd ..
uv run --with pyyaml python research/check_ledger.py
bash -n experiments/humanize2_baseline/scripts/*.sh
git diff --check
latexmk -pdf -outdir=/tmp/humanize2-final-tex main.tex
```

Results: 2 Python tests passed; both Lean demos passed; Lake completed 2,946 jobs; the two ledgers
reported 195 nodes, 675 labels, and 0 structural errors; shell syntax and diff checks passed; and
the manuscript rebuilt successfully at 161 pages. A scoped secret-pattern scan of the added
experiment, decision, and handoff files found no credential material.

## 8. Problems encountered

- **Dirty primary checkout:** unrelated untracked duplicate files were present. Work proceeded in
  a linked worktree on a new branch; nothing in the primary checkout was cleaned or overwritten.
- **System Python dependency:** Python 3.14.5 lacked PyYAML, so the initial ledger check could not
  start. The final check uses an isolated tool Python containing PyYAML; no global package was
  installed.
- **First-time Lean bootstrap:** parallel first invocations contended while cloning mathlib, and a
  restricted run encountered DNS failure. One serial `lake build` completed the pinned bootstrap.
- **Lean import surface:** `import Mathlib` required an aggregate root object not emitted by the
  repository's normal build. The fixtures now import the built `FunctionalInequalities` target.
- **Read-only Git:** Apple Git attempted to write an `xcrun` cache under `/tmp` and was denied in
  the Codex read-only sandbox. Codex's bundled fallback Git still produced the requested status.
- **Shared Ralph state:** an exploratory unisolated Lean run picked up prior Python Ralph state.
  Final runners derive separate homes; isolated replay metadata contains no `picked_up` field.
- **Moving flowverse:** `official/rlar` normally fetches a moving default branch. The runner uses a
  pinned alias and verifies the detached commit before execution.
- **Streaming noise:** `hmz exec` repeated some streamed text/JSON fragments. Exit status, cycle
  records, independent tests, and compiler runs remained unambiguous.
- **Authorization:** authenticated execution was paused until the user explicitly authorized the
  scoped OpenAI transfer. No credential value was read or recorded.

## 9. Relevance to KLS

Reusable components now supported by evidence are:

- statement generation（命题生成）can be placed in a scoped prompt and persisted in Git;
- proof generation（证明生成）can edit an isolated Lean target;
- proof repair（证明修复）can react to concrete Lean diagnostics;
- Lean verification（Lean 验证）can be run by both actor and independent reviewer;
- iterative agent loops（迭代代理循环）can share repository state while isolating run metadata;
- reviewer agents（审查代理）can audit compilation, placeholders, diff scope, and declaration
  preservation through structured acceptance.

What remains unsolved is mathematical difficulty, paper parsing, theorem selection, dependency
discovery, robust long-running budgets, proof-dossier integration, and reviewer competence on deep
mathematics.

Most importantly, semantic fidelity（语义忠实性）is distinct from proof correctness. Lean
compilation establishes that a formal declaration is internally well-typed and proved. It does
**not** establish that the declaration faithfully represents the informal theorem in a paper. A
future semantic reviewer must compare hypotheses, quantifiers, constants, domains, normalization,
and conclusion against the source before proof success can count as faithful autoformalization.

## 10. Recommended next step

Run one statement-first, proof-second experiment on a small theorem whose informal text and
already-reviewed Lean statement are both available. Hide the reference declaration from the
statement generator, have it propose a candidate, and require a human or semantic-review agent to
compare that candidate with the reference before the existing proof-repair/RLAR harness is allowed
to prove it:

```text
paper theorem
→ candidate Lean statement
→ semantic reviewer
→ proof actor
→ Lean compiler / repair
→ proof reviewer
```

This is the smallest next experiment because syntax, editing, compiler repair, and proof review
already passed; statement meaning is now the first untested boundary. Keep it outside live KLS
ledgers and manuscript claims until semantic-fidelity criteria are explicit and reviewed.

## 11. How to continue

1. Check out `humanize2-lean-baseline` and confirm `git status --short` is empty.
2. Read this file, `AGENTS.md`, `experiments/README.md`, and
   `experiments/humanize2_baseline/README.md` first.
3. Install the pinned Humanize2 revision and configure Codex separately.
4. Set `HUMANIZE_SENTRY=off` and an absolute, external `HUMANIZE2_STATE_ROOT`.
5. Use the reset/run/verify commands in section 6. Prompts are in
   `experiments/humanize2_baseline/prompts/`; runners are in
   `experiments/humanize2_baseline/scripts/`.
6. Inspect the pinned flow code through `scripts/prepare_flowverse.sh` before changing its
   reviewer contract.
7. Do not commit cycle/session state, raw model transcripts, credentials, caches, or tool-global
   configuration.
8. Do not modify KLS statements, ledgers, proof dossiers, or manuscript claims for the next
   statement-fidelity experiment without following the repository's mathematical workflow and
   independent review requirements.

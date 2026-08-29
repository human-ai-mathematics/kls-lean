# Establish an isolated Humanize2 → Codex → Lean infrastructure baseline

- **Date:** 2026-08-29
- **Type:** agent harness and validation
- **Scope:** `experiments/humanize2_baseline/`, baseline handoff documentation
- **Mathematical effect:** none

## Problem

The repository had no reproducible test of whether HumanFIA Humanize2 could drive the authenticated
Codex CLI against a real Git working tree, persist a bounded edit, invoke the repository's pinned
Lean compiler, repair a proof from actual compiler output, and submit the result to a distinct
actor-reviewer flow. Generated prose or a predicted proof was not sufficient evidence. The
baseline also needed to avoid the dirty primary checkout, KLS source files, credentials, global
machine configuration, moving upstream flow code, and unbounded agent loops.

## Decision

Keep the harness under `experiments/humanize2_baseline/` and its durable continuation record under
`docs/`. Use deliberately broken, KLS-independent Python and Lean fixtures. Commit each repaired
target only after an external verifier passes, while retaining `.initial` fixtures and reset
scripts so the failing-to-passing transition is reproducible.

Pin Humanize2 at commit `e8bcede84d4b3365378e04f9c80d0fd397903c30` (`hmz 0.1.0`) and install
it with `uv tool`. Pin the upstream flowverse at
`22de7178543140edaaaef2bea351b51ac29e6f04`; fetch it under the isolated alias
`humanize2-baseline-flowverse` and detach that clone before every RLAR run. This prevents a later
default-branch update from changing the reviewer protocol silently.

Run read-only diagnosis with `chat`, editing and compiler repair with a 0.001-million-output-token
`ralph_loop` budget, and review with the pinned upstream `rlar` flow. Codex actors receive
`workspace-write`; read-only diagnosis and the RLAR reviewer receive `read-only`. Humanize2
delegates authentication to the local Codex CLI, and crash telemetry is disabled with
`HUMANIZE_SENTRY=off`.

Require an absolute `HUMANIZE2_STATE_ROOT` outside the repository. Each runner derives a distinct
`HUMANIZE_HOME` for Python inspection, Python Ralph, Lean Ralph, and Lean RLAR. Humanize2 stores
resumable state per flow and workspace; without this separation, two uses of the built-in
`ralph_loop` can pick up one another's state even though their agent sessions are fresh.

The Lean demos import `FunctionalInequalities`, which is an ordinary repository build target, and
compile through `cd formalization && lake env lean ...`. They are not added to the KLS library or
its default build targets. No ledger, manuscript statement, proof dossier, numerical artifact,
claim status, mathematical dependency, or KLS source changes as part of this decision.

## Isolation and security boundary

The primary checkout contained unrelated untracked iCloud-style duplicate files. Create a linked
worktree at base commit `f620cadf7073ce8a6c31713047a2e36e759b5536` and branch
`humanize2-lean-baseline`; do not touch or clean the primary checkout. Keep Humanize2 installation,
flowverse clones, cycles, sessions, and compiler caches outside the tracked experiment area.

The live Codex runs were made only after explicit authorization to transfer the prompts,
`AGENTS.md`, disposable fixtures, Git status/diffs, and compiler/test output to OpenAI. No API key,
token, `.env` file, Codex credential, Claude credential, or raw session transcript is committed.

## Observed failures and resolutions

- The system Python 3.14.5 could not import PyYAML, so the pre-change
  `python3 research/check_ledger.py` check stopped with `ModuleNotFoundError`. This is a machine
  dependency issue, not a ledger defect. Final ledger validation uses the isolated Humanize2 tool
  environment, which already contains PyYAML, without changing global Python.
- Two simultaneous first-time Lean commands contended while fetching mathlib and one encountered
  restricted network resolution. Bootstrapping once with a serial `lake build` resolved it.
- A broad `import Mathlib` required the aggregate `Mathlib.olean`, which the repository's normal
  target build does not emit. Importing the existing `FunctionalInequalities` target makes direct
  demo compilation work after the documented repository build.
- In Codex `read-only`, Apple Git first attempted to write an `xcrun` cache under `/tmp` and was
  denied. Codex's bundled fallback Git still returned the required repository status. The harness
  itself made no repository mutation.
- An initial unisolated Lean Ralph cycle recorded `picked_up` from the preceding Python Ralph
  cycle. Per-experiment state homes removed that coupling; the final replay cycle metadata has no
  `picked_up` field.
- Humanize2's streamed CLI output repeated some messages and structured-review fragments. The
  cycle ended normally, and independent repository/compiler checks, rather than console prose,
  are the acceptance evidence.

## Validation

- Pre-change `cd formalization && lake build` — passed, 2,946 jobs.
- Pre-change `latexmk -pdf -outdir=/private/tmp/humanize2-prechange-tex main.tex` — passed,
  161 pages.
- `hmz --version` — passed, `hmz 0.1.0`.
- `hmz --help` — passed.
- Read-only Python `chat` — passed; correct root, files, bug, and failing assertions; external
  `git diff --exit-code` confirmed no mutation.
- Python `ralph_loop` — passed in one final isolated round; the exact two-test `unittest` command
  passed and the final tree matched the committed minimal repair.
- Lean `ralph_loop` — passed in one final isolated round; Lean first reported the concrete
  `Nat.zero_add` type mismatch, then accepted `Nat.add_zero`; independent compilation passed.
- Pinned upstream `rlar` — passed on the first official review; the actor repaired
  `Nat.add_assoc` to `Nat.add_comm`, and a fresh read-only reviewer compiled the file, rejected
  placeholders, audited all diffs, compared the declaration to `HEAD`, and returned
  `done: true`. No reviewer-requested repair iteration was necessary.
- `experiments/humanize2_baseline/scripts/verify_python.sh` — passed, 2 tests.
- `experiments/humanize2_baseline/scripts/verify_lean.sh` — passed, both demo files.
- Final repository-wide checks and the pushed branch tip are recorded in
  `docs/HUMANIZE2_LEAN_BASELINE_HANDOFF.md`.

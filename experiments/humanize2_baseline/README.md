# Humanize2 → Codex → Lean baseline

This directory is an infrastructure experiment. It does not formalize or change any KLS
mathematics. The fixtures test whether HumanFIA Humanize2 can drive the Codex CLI in this
repository, persist edits, invoke the pinned Lean compiler, react to compiler output, and run
an actor-reviewer flow.

## Pinned baseline

- Humanize2 source: `humanfia/humanize2` commit
  `e8bcede84d4b3365378e04f9c80d0fd397903c30` (`hmz 0.1.0`)
- Official flowverse source: `humanfia/flowverse` commit
  `22de7178543140edaaaef2bea351b51ac29e6f04`
- Agent: Codex, configured by the scripts as `gpt-5.6-sol` at `high` effort unless overridden
- Permission profiles: `read-only` for inspection/review, `workspace-write` for actors
- Lean: the repository's pinned `formalization/lean-toolchain`

The final verified results and environment record are in
`../../docs/HUMANIZE2_LEAN_BASELINE_HANDOFF.md`. That file is written after the live runs.

## Layout

| Path | Purpose |
| --- | --- |
| `python_demo/` | Tiny Python bug and its independent `unittest` check |
| `lean_demo/` | Two tiny Lean theorems, independent of KLS mathematics |
| `fixtures/` | Deliberately broken initial states used by reset scripts |
| `prompts/` | Exact tasks passed to Humanize2 |
| `configs/` | Small output budget that bounds the built-in Ralph loop |
| `scripts/` | Reset, Humanize2 invocation, and independent verification commands |

## Install Humanize2

Upstream documents both `pip` and `uv tool`; this baseline used the isolated `uv tool` form,
pinned to the inspected source commit:

```bash
uv tool install \
  'git+https://github.com/humanfia/humanize2.git@e8bcede84d4b3365378e04f9c80d0fd397903c30'
hmz --version
hmz --help
```

Humanize2 delegates authentication to the backend CLI. Configure Codex separately with
`codex login`; never put credentials in this repository. `codex login status` can confirm the
method without displaying a credential.

For unattended runs, the upstream project asks the user to choose whether crash telemetry is
enabled. Set `HUMANIZE_SENTRY=off` to make the baseline noninteractive and send no reports:

```bash
export HUMANIZE_SENTRY=off
```

If `hmz` is not on `PATH`, point the scripts at it without modifying them:

```bash
export HMZ_BIN=/path/to/hmz
```

## Reproduce the Python baseline

Run from the repository root:

```bash
experiments/humanize2_baseline/scripts/reset_python_demo.sh
experiments/humanize2_baseline/scripts/run_python_read_only.sh
git diff --exit-code -- experiments/humanize2_baseline/python_demo/calculator.py
experiments/humanize2_baseline/scripts/run_python_ralph.sh
experiments/humanize2_baseline/scripts/verify_python.sh
```

The read-only run uses Humanize2 `chat` with Codex's `read-only` permission. The editing run
uses the built-in `ralph_loop` with `workspace-write`; the checked-in config bounds cumulative
output to 0.001 million tokens so the otherwise-unbounded loop stops after a small number of
rounds.

## Reproduce the Lean proof-repair baseline

```bash
experiments/humanize2_baseline/scripts/reset_lean_demo.sh
experiments/humanize2_baseline/scripts/run_lean_repair.sh
experiments/humanize2_baseline/scripts/verify_lean.sh
```

The prompt requires Codex to run the failing Lean command before editing, preserve the theorem
statement, remove the invalid proof without `sorry`, and rerun Lean until it exits successfully.
The verifier independently invokes the same pinned toolchain after Humanize2 exits.

## Reproduce the actor-reviewer baseline

Reset only the actor-reviewer fixture if the first Lean theorem should remain complete:

```bash
cp experiments/humanize2_baseline/fixtures/lean/ActorReviewerTest.lean.initial \
  experiments/humanize2_baseline/lean_demo/ActorReviewerTest.lean
experiments/humanize2_baseline/scripts/run_lean_rlar.sh
experiments/humanize2_baseline/scripts/verify_lean.sh
```

`official/rlar` takes two Codex agents. The actor has `workspace-write`; the independent fresh
reviewer has `read-only`. The reviewer is required to inspect the repository state, run Lean,
check for placeholders and theorem weakening, and reject unrelated changes. Its structured
review ends the flow only when `done` is true; otherwise `notes` are passed to the actor as the
next prompt verbatim.

## Configuration overrides

The scripts accept:

```bash
export HUMANIZE2_AGENT_MODEL=gpt-5.6-sol
export HUMANIZE2_AGENT_EFFORT=high
```

Use model identifiers and effort levels supported by the installed Codex CLI and account.


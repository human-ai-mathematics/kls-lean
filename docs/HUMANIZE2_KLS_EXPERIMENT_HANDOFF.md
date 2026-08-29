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
- Current experiment status: **READY / NOT YET RUN**

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

## 8. Current validation

At handoff creation, only local scaffold validation is authorized. The expected pre-run state is a
compiling sentinel and therefore `verify_candidate.sh` must refuse it. The live Humanize2/Codex run
has not yet occurred and no outcome is claimed.

The following local checks passed on 2026-08-29:

- `verify_scaffold.sh`: reset fixture matched, all four oracle hashes matched, and the sentinel
  type-checked with the pinned Lean toolchain;
- `verify_candidate.sh`: exited `2` with `candidate is still the unattempted sentinel`, the expected
  pre-run refusal;
- `cd formalization && lake build`: 2,946 jobs completed successfully;
- the inherited Python baseline: 2 tests passed;
- the inherited two-file Lean baseline: both files compiled;
- `uv run --with pyyaml python research/check_ledger.py`: 2 ledgers, 195 nodes, 675 labels,
  0 structural errors;
- all baseline and experiment shell scripts passed `bash -n`; and
- a scoped credential-pattern scan found no secrets.

## 9. Authorization boundary

The previous authorization covered disposable baseline fixtures, not KLS-facing source material.
Before executing `run_statement_rlar.sh`, obtain explicit authorization to send the frozen informal
specification, allowed Lean API files, candidate contents/diff, Git metadata, Lean compiler output,
and reviewer findings to OpenAI. Credentials remain managed by the Codex CLI and must never be
placed in prompts or repository files.

## 10. What remains after the run

Persist a concise result record, not a raw transcript. Record actor files read, candidate diff,
compiler outcomes, reviewer rounds and notes, final structured decision, independent verification,
and any semantic failure. If the statement calibration passes, the next experiment may replace the
`Prop` definition with a theorem and exercise proof generation/repair. If it fails, keep the failed
candidate and reviewer diagnosis as benchmark evidence without touching mathematical status.

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

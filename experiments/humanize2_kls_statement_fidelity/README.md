# Humanize2 KLS statement-fidelity experiment

This is the first KLS-facing autoformalization calibration built on
`experiments/humanize2_baseline/`. It tests whether a prompt-blind Humanize2/Codex actor can turn a
frozen informal functional-inequality statement into a well-typed Lean proposition, and whether a
fresh reviewer can detect semantic weakening by comparing it with a pinned, independently audited
repository oracle.

The target is the shared linear-test Poincaré lower bound, ledger node
`lem:linear-test-lower`. The node is recorded in the A-series ledger, but it is a generic
functional-inequality tool used throughout KLS reasoning. This experiment is therefore a KLS
pipeline calibration, not a new KLS theorem and not a new proof of the node.

## Current status

**READY / NOT YET RUN.** The input, candidate sentinel, semantic rubric, oracle hashes, RLAR prompt,
and verification scripts are committed. The live authenticated run requires explicit authorization
to send the frozen KLS-facing specification, allowed Lean API files, candidate diff, and compiler
output to OpenAI. No mathematical status changes when this experiment runs.

## Protocol

1. `reset_candidate.sh` restores a compiling `True` sentinel marked `HUMANIZE2_UNATTEMPTED`.
2. The RLAR actor may read the frozen input and lower-level Lean API, but is instructed not to read
   the oracle, existing certificate, dossier, ledger statement, or prior semantic reviews.
3. The actor replaces only `candidate/CandidateStatement.lean` with a definition whose value is the
   proposed Lean `Prop`, and invokes the pinned Lean compiler.
4. A fresh read-only reviewer may read the pinned oracle sources and semantic rubric. It compiles
   the candidate, audits Git scope, and checks every semantic field.
5. `done: false` review notes become the actor's next prompt verbatim; `done: true` ends the run.
6. `verify_candidate.sh` independently checks scope, sentinel removal, placeholder absence, oracle
   pins, and Lean compilation. Semantic acceptance still requires the reviewer record.

The blindness boundary is prompt-enforced, not cryptographic: actor and reviewer share a repository
and the Codex read sandbox can technically read the oracle paths. Tool traces must therefore be
audited after the run. A later hardened experiment should give the actor an oracle-free snapshot.

## Setup and commands

Install and authenticate exactly as described in
`../../docs/HUMANIZE2_LEAN_BASELINE_HANDOFF.md`, then from the repository root:

```bash
export HUMANIZE_SENTRY=off
export HUMANIZE2_STATE_ROOT=/tmp/humanize2-kls-statement-fidelity

experiments/humanize2_kls_statement_fidelity/scripts/reset_candidate.sh
experiments/humanize2_kls_statement_fidelity/scripts/verify_scaffold.sh
experiments/humanize2_kls_statement_fidelity/scripts/run_statement_rlar.sh
experiments/humanize2_kls_statement_fidelity/scripts/verify_candidate.sh
```

The full continuation boundary is in
`../../docs/HUMANIZE2_KLS_EXPERIMENT_HANDOFF.md`.

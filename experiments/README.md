# Autoformalization experiments

This directory is published only on the `autoformalization-experiments` branch. The repository
root `README.md` remains the minimal project README inherited from `main`.

## Experiment map

- `humanize2_baseline/`: verified Python editing, Lean compiler repair, and actor-reviewer
  infrastructure baseline.
- `humanize2_kls_statement_fidelity/`: completed linear-test statement-fidelity calibration.
- `humanize2_kls_proof_repair/`: oracle-free proof-repair isolation scaffold; model-free checks
  passed and no authenticated run has started.
- `humanize2_kls_issue2_staged/`: staged blind reconstruction of Issue 2.

## Current Issue 2 gate

Stage 1A is a human-accepted experimental dependency. Stage 1B Run 2 passed its original
compilation, exact-surface, immutable-dependency, and trace gates, but the user rejected its one
`unnecessarySimpa` linter diagnostic. A fresh zero-warning Run 3 is authorized and being prepared;
Stage 2A has not started.

The Run 2 candidate remains immutable historical output. Do not promote it merely because Lean
exits zero.

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
`unnecessarySimpa` linter diagnostic. Fresh zero-warning Run 3 passed the silent compiler,
exact-surface, immutable-dependency, isolation, and complete-trace gates. It is stopped for human
semantic/proof review; Stage 2A has not started.

Review the Run 3 candidate using
`humanize2_kls_issue2_staged/review/STAGE_1B_RUN3_REVIEW.md`. Run 2 remains immutable historical
output.

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

Stage 1A is a human-accepted experimental dependency. Stage 1B Run 2 passed compilation, the
exact thirteen-declaration surface verifier, immutable-dependency checks, and the complete-session
trace audit. It is not yet accepted: the human semantic/proof review is pending, and Stage 2A has
not started.

Review the stopped Stage 1B candidate using
`humanize2_kls_issue2_staged/review/STAGE_1B_RUN2_REVIEW.md`. Do not run a new actor or promote the
candidate merely because Lean compiles.

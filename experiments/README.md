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

Stages 1A, 1B Run 3, 2A Run 1, 2B Run 1, Stage 3 Run 1, and Stage 4A Run 1 are human-accepted
experimental dependencies. The accepted Stage 4A source is byte-identical to its stopped
candidate after a Claude 5 Fable review reproduced all mechanical evidence, checked the two long
proofs line by line, and returned all sixteen items `PASS`.

Stage 4B is now frozen and authorized for one isolated `gpt-5.6-sol` Run 1 at high effort. Its
remaining eight centered-covariance declarations compile in the known-good fixture with the
single import `AcceptedStage4A`. The full model-free preflight passed the six-layer rebuild,
fifteen-entry fixture, exact surface, hidden oracle, soundness, isolation, trace-policy, and live-
gate controls. A live candidate remains a mechanical result until a separate human decision.

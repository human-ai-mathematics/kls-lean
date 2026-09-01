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

Stage 4B Run 1 is now a human-accepted experimental dependency under the standing statement-level
alignment ruling. The accepted source is byte-identical to the stopped candidate, and all sixteen
review items pass.

Stage 5 Run 1 is now a zero-diagnostic `mechanical-pass`. One isolated high-effort
`gpt-5.6-sol` turn produced the exact single-import, three-theorem final-assembly surface on its
second Lean call after one repair iteration. The seventeen-entry fixture, seven immutable
accepted pairs, hidden oracle, strict-implicit and deliberate-hypothesis controls, candidate-only
mutation, and complete trace passed. The stopped candidate awaits a separate sixteen-item human
decision; no experiment wrap-up is automatic.
